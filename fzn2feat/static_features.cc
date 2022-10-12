/*
* Class for extracting (static) features from a FlatZinc model.
*/
#include <cmath>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include "expr.cc"

using std::cout;
using std::endl;
using std::map;
using std::setw;
using std::left;

// Encodes variables information.
struct var_info {
  bool        assigned;
  int         id;
  const char* name;
  double      dom_size;
  expr_type   type;
  expr_set*   anns;
  bool        array;
  int         begin;
  int         end;
  int         degree;
  var_info*   alias;
};

typedef map<string, double>   :: const_iterator  feat_iterator;
typedef map<string, var_info> :: const_iterator  vars_iterator;
typedef map<int, set<int> >   :: const_iterator  cons_iterator;
typedef map<double, double>   :: const_iterator count_iterator;


class static_features {

public:

  static double inf;
  map<string, double> features;
  map<string, var_info> vars_to_info;

  static_features() {
    // Initialilization.
    init_vars();
    init_doms();
    init_cons();
    init_globals();
    init_solve();
    init_objfn();
    // Auxiliary variables.
    sum_ari_cons     = 0.0;
    sum_dom_vars2    = 0.0;
    sum_deg_vars2    = 0.0;
    sum_domdeg_vars2 = 0.0;
    sum_dom_cons2    = 0.0;
    sum_ari_cons2    = 0.0;
    sum_domdeg_cons2 = 0.0;
  }

  /*
   * Class destructor. De-allocates expressions for (possible) aliases.
   */
  ~static_features() {
    for (vars_iterator i = vars_to_info.begin(); 
                      i != vars_to_info.end(); ++i) {
      var_info* j = i->second.alias;
      while (j) {
        var_info* k = j->alias;
        expr_set* es = j->anns;
        for (expr_set::iterator h = es->begin(); h != es->end(); ++h)
          if ((*h) != NULL)
            (*h)->destroy();
        delete j;
        if (k)
          j = k;
        else
          j = 0;
      }
    }
  }


  /*
   * Updates the features for an assigned variable (i.e., a constant or an 
   * alias).
   */
  void
  update_assigned_variable(var_info& vi, expression* e) {
    vi.id = -1;
    vi.assigned = true;
    if (e->type() == STRING_EXPR) {
      var_info vi_alias = vars_to_info[string(e->value().string_val)];
      while (vi_alias.alias)
        vi_alias = vars_to_info[vi_alias.alias->name];
      vi.alias = new var_info(vi_alias);
      ++features["v_num_aliases"];
    }
    else {
      vi.alias = NULL;
      ++features["v_num_consts"];
    }

    expr_set* anns = vi.anns;
    for (expr_set::iterator i = anns->begin(); i != anns->end(); ++i) {
      string ann = string((*i)->value().string_val);
      if (ann == "is_defined_var")
        ++features["v_def_vars"];
      else
        if (ann == "var_is_introduced")
          ++features["v_intro_vars"];
    }
    vars_to_info[string(vi.name)] = vi;
  }

  /*
   * Updates the features for a not assigned variable.
   */
  void
  update_variable(var_info& vi) {
    vi.id = var_id++;
    vi.alias = NULL;
    vi.degree = 0;
    vi.assigned = false;

    switch (vi.type) {
      case BOOL_EXPR:
        ++features["d_bool_vars"];
        break;
      case FLOAT_EXPR:
        ++features["d_float_vars"];
        break;
      case INT_EXPR:
        ++features["d_int_vars"];
        break;
      case SET_EXPR:
        ++features["d_set_vars"];
        break; 
    }

    double dom = vi.dom_size;
    features["v_sum_dom_vars"] += dom;
    features["v_logprod_dom_vars"] += log2(dom);
    sum_dom_vars2 += dom * dom;
    if (dom < features["v_min_dom_vars"])
      features["v_min_dom_vars"] = dom;
    if (dom > features["v_max_dom_vars"])
      features["v_max_dom_vars"] = dom;
    ++count_dom_vars[dom];

    expr_set* anns = vi.anns;
    for (expr_set::iterator i = anns->begin(); i != anns->end(); ++i) {
      string ann = string((*i)->value().string_val);
      if (ann == "is_defined_var")
        ++features["v_def_vars"];
      else
        if (ann == "var_is_introduced")
          ++features["v_intro_vars"];
    }
    vars_to_info[string(vi.name)] = vi;
  }

  /*
   * Updates the features for an array of assigned variables.
   */
  void
  update_assigned_var_array(var_info& vi, expr_list* el) {
    vi.id = -1;
    vi.assigned = true;
    string array_name = string(vi.name);
    vars_to_info[array_name] = vi;
    int i = vi.begin;
    for (expr_list::iterator it = el->begin(); it != el->end(); ++it) {
      var_info vii = vi;
      string var_name = array_name + "[" + to_string(i) + "]";
      vii.array = false;
      vii.name = var_name.c_str();
      vii.id = -1;
      vii.assigned = true;
      if ((*it)->type() == STRING_EXPR) {
        var_info vi_alias = vars_to_info[string((*it)->value().string_val)];
        while (vi_alias.alias)
          vi_alias = vars_to_info[vi_alias.alias->name];
        vii.alias = new var_info(vi_alias);
        ++features["v_num_aliases"];
      }
      else {
        vii.alias = NULL;
        ++features["v_num_consts"];
      }
      vars_to_info[var_name] = vii;
      ++i;
    }

    int n = vi.end - vi.begin + 1;
    expr_set* anns = vi.anns;
    for (expr_set::iterator i = anns->begin(); i != anns->end(); ++i)
      if ((*i)->type() == STRING_EXPR) {
        string ann = string((*i)->value().string_val);
        if (ann == "is_defined_var")
          features["v_def_vars"] += n;
        else
          if (ann == "var_is_introduced")
            features["v_intro_vars"] += n;
      }
  }

  /*
   * Updates the features for an array of not assigned variables.
   */
  void
  update_var_array(var_info& vi) {
    vi.id = -1;
    vi.assigned = false;
    string array_name = string(vi.name);
    vars_to_info[array_name] = vi;

    int a = vi.begin;
    int b = vi.end;
    for (int i = a; i <= b; ++i) {
      var_info vii = vi;
      vii.degree = 0;
      string var_name = array_name + "[" + to_string(i) + "]";
      vii.name   = var_name.c_str();
      vii.array  = false;
      vii.id     = var_id++;
      vii.alias  = NULL;
      vii.assigned = false;
      vars_to_info[var_name] = vii;
    }

    int n = b - a + 1;
    switch (vi.type) {
      case BOOL_EXPR:
        features["d_bool_vars"] += n;
        break;
      case FLOAT_EXPR:
        features["d_float_vars"] += n;
        break;
      case INT_EXPR:
        features["d_int_vars"] += n;
        break;
      case SET_EXPR:
        features["d_set_vars"] += n;
        break;
    }
    double dom = vi.dom_size;
    features["v_sum_dom_vars"] += dom * n;
    features["v_logprod_dom_vars"] += log2(dom) * n;
    sum_dom_vars2 += dom * dom * n;
    if (vi.dom_size < features["v_min_dom_vars"])
      features["v_min_dom_vars"] = dom;
    if (vi.dom_size > features["v_max_dom_vars"])
      features["v_max_dom_vars"] = dom;
    count_dom_vars[dom] += n;

    expr_set* anns = vi.anns;
    for (expr_set::iterator i = anns->begin(); i != anns->end(); ++i)
      if ((*i)->type() == STRING_EXPR) {
        string ann = string((*i)->value().string_val);
        if (ann == "is_defined_var")
          features["v_def_vars"] += n;
        else
          if (ann == "var_is_introduced")
            features["v_intro_vars"] += n;
      }
  }

  /*
   * Updates the features for a (possibly global) constraint.
   */
  void
  update_constraint(expr_list* params, expr_list* annots) {
    string name = string(params->front()->value().string_val);
    params->pop_front();
    map<string, int>::iterator it = globals.find(name);
    if (it != globals.end()) {
      ++features["gc_global_cons"];
      if (it->second == 0)
        ++features["gc_diff_globs"];
      ++(it->second);
    }
    else {
      int i = name.find('_');
      string dom = name.substr(0, i);
      if (dom == "array")
        ++features["d_array_cons"];
      else if (dom == "bool")
        ++features["d_bool_cons"];
      else if (dom == "float")
        ++features["d_float_cons"];
      else if (dom == "int")
        ++features["d_int_cons"];
      else if (dom == "set")
        ++features["d_set_cons"];
    }
    bool priority = true;
    bool bounds = true;
    expr_set anns;
    set_expr::list_to_set(*annots, anns);
    for (expr_set::iterator i = anns.begin(); i != anns.end(); ++i) {
      expr_type et = (*i)->type();
      string ann;
      if (priority && et == ARRAY_EXPR) {
        ann = string((*i)->value().list_val->front()->value().string_val);
        if (ann == "priority")
          ++features["c_priority"];
        priority = false;
        continue;
      }
      if (!bounds)
        break;
      ann = string((*i)->value().string_val);
      bounds = false;
      if (ann == "bounds" || ann == "boundsZ")
        ++features["c_bounds_z"];
      else
        if (ann == "boundsR")
          ++features["c_bounds_r"];
        else
          if (ann == "boundsD")
            ++features["c_bounds_d"];
          else
            if (ann == "domain")
              ++features["c_domain"];
            else
              bounds = true;
    }

    // Parse constraint arguments.
    set<int> con_vars;
    double dom = 0; 
    expr_list::iterator i, j;
    for (i = params->begin(); i != params->end(); ++i)
      switch ((*i)->type()) {
        // The argument is a variable of the form A[i]. 
        case ARRAY_EXPR: {
          expr_list* exprs = (*i)->value().list_val;
          for (j = exprs->begin(); j != exprs->end(); ++j)
            if ((*j)->type() == STRING_EXPR) {
                string var_name = string((*j)->value().string_val);
              update_cons(vars_to_info[var_name], con_vars, dom);
            }
          break;
        }

        // The argument is either a variable or an array of variables.
        case STRING_EXPR: {
          string var_name = string((*i)->value().string_val);
          var_info vi = vars_to_info[var_name];
          if (vi.array)
            for (int j = vi.begin; j <= vi.end; ++j) {
              string var_id = var_name + "[" + to_string(j) + "]";
              update_cons(vars_to_info[var_id], con_vars, dom);
            }
          else
            update_cons(vi, con_vars, dom);
          break;
        }

        default:
          continue;
      }

      double deg = con_vars.size();
      // Ignore constraints that not involve variables.
      if (deg == 0) {
        std::cerr << "Warning: constraint " << name
                  << " has degree 0." << endl;
        return;
      }
      ++features["c_num_cons"];
      features["c_sum_dom_cons"] += dom;
      sum_dom_cons2 += dom * dom;
      if (dom > 0) 
        features["c_logprod_dom_cons"] += log2(dom);
      if (dom < features["c_min_dom_cons"])
        features["c_min_dom_cons"] = dom;
      if (dom > features["c_max_dom_cons"])
        features["c_max_dom_cons"] = dom;
      ++count_dom_cons[dom];

      features["c_sum_ari_cons"] += params->size();
      sum_ari_cons += deg;
      sum_ari_cons2 += deg * deg; 
      features["c_logprod_deg_cons"] += log2(deg);
      if (deg < features["c_min_deg_cons"])
        features["c_min_deg_cons"] = deg;
      if (deg > features["c_max_deg_cons"])
        features["c_max_deg_cons"] = deg;
      ++count_deg_cons[deg];

      double domdeg = dom / deg;
      features["c_sum_domdeg_cons"] += domdeg;
      sum_domdeg_cons2 += domdeg * domdeg;
      if (domdeg < features["c_min_domdeg_cons"])
        features["c_min_domdeg_cons"] = domdeg;
      if (domdeg > features["c_max_domdeg_cons"])
        features["c_max_domdeg_cons"] = domdeg;
      ++count_domdeg_cons[floor(domdeg + 0.5)];
  }

  /*
   * Updates the features for the solving goal.
   */
  void
  update_solve(const expr_list& e) {
    if (e.empty())
      return;
    expr_list* anns = e.front()->value().list_val;
    string search = string(anns->front()->value().string_val);
    // seq_search is a list of search annotations.
    if (search == "seq_search") {
      anns->pop_front();
      for (expr_list::iterator i = anns->begin(); i != anns->end(); ++i) {
        expr_list* ann = (*i)->value().list_val;
        update_search(ann);
      }
    }
    else
      update_search(anns);
  }

  /*
   * Updates the features for objective variable. 
   */
  void
  update_objvar(expression* e) {
    string var_name = string(e->value().string_val);
    obj_var = vars_to_info[var_name];
  }

  /*
   * Final computation.
   */
  void 
  final_update() {
    final_update_vars();
    final_update_cons();
    // If the input model is an optimisation problem.
    if (features["s_goal"] > 1)
      final_update_obj();
  }

  /*
   * Prints a representation of the features according to output parameter.
   */
  void
  print(string output) {
    if (output == "dict")
      print_dict();
    else
      if (output == "pp")
        print_pp();
      else
        print_csv();
  }

  /*
  * Prints a comma-separated list of the features values.
  */
  void
  print_csv(char sep = ',') {
    int n = features.size();
    int i = 1;
    feat_iterator iter = features.begin();
    for (; iter != features.end() && i < n; ++iter, ++i)
      cout << to_string(iter->second) << ',';
    cout << to_string(iter->second) << endl;
  }

  /*
  * Prints a python-like dictionary which associates to each identifier 
  * the corresponding feature value.
  */
  void print_dict() {
    int n = features.size();
    int i = 1;
    feat_iterator iter = features.begin();
    cout << "{";
    for (; iter != features.end() && i < n; ++iter, ++i) { 
      cout << "'" << iter->first << "': ";
      cout << to_string(iter->second) << ", ";
    }
    cout << "'" << iter->first << "': ";
    cout << to_string(iter->second) << '}' << endl;
  };

  /*
  * Pretty-prints the features identifiers, values, and description. 
  */
  void print_pp() {
    string k;

    cout << setw(15) << "IDENTIFIER"
         << setw(20) << "VALUE"
         << setw(40) << "DESCRIPTION" << endl;
    cout << "======================================================";
    cout << "=====================================================\n";
    cout << left;
    for (feat_iterator i = features.begin(); i != features.end(); ++i) {
      k = i->first;
      cout << setw(21) << k;
      cout << setw(23) << to_string(i->second);
      cout << setw(65) << description[k] << endl;
    }
  };

private:

  static int var_id;
  static int con_id;
  static map<string, int> globals;
  static map<string, string> description;

  double sum_ari_cons;
  double sum_dom_vars2;
  double sum_deg_vars2;
  double sum_domdeg_vars2;
  double sum_dom_cons2;
  double sum_ari_cons2;
  double sum_domdeg_cons2;

  map<int, set<int> > cons_to_vars;
  map<double, double> count_dom_vars;
  map<double, double> count_deg_vars;
  map<double, double> count_domdeg_vars;
  map<double, double> count_dom_cons;
  map<double, double> count_deg_cons;
  map<double, double> count_domdeg_cons;
  var_info obj_var;

  // Initialize variables (27 features).
  void
  init_vars() {
    features["v_num_vars"]         = 0.0;
    features["v_num_consts"]       = 0.0;
    features["v_ratio_vars"]       = 0.0;
    features["v_num_aliases"]      = 0.0;
    features["v_ratio_bounded"]    = 0.0;
    features["v_def_vars"]         = 0.0;
    features["v_intro_vars"]       = 0.0;
    features["v_logprod_dom_vars"] = 0.0;
    features["v_logprod_deg_vars"] = 0.0;
    features["v_sum_dom_vars"]     = 0.0;
    features["v_sum_deg_vars"]     = 0.0;
    features["v_sum_domdeg_vars"]  = 0.0;
    features["v_min_dom_vars"]     = inf;
    features["v_min_deg_vars"]     = inf;
    features["v_min_domdeg_vars"]  = inf;
    features["v_max_dom_vars"]     = 0.0;
    features["v_max_deg_vars"]     = 0.0;
    features["v_max_domdeg_vars"]  = 0.0;
    features["v_avg_dom_vars"]     = 0.0;
    features["v_avg_deg_vars"]     = 0.0;
    features["v_avg_domdeg_vars"]  = 0.0;
    features["v_cv_dom_vars"]      = 0.0;
    features["v_cv_deg_vars"]      = 0.0;
    features["v_cv_domdeg_vars"]   = 0.0;
    features["v_ent_dom_vars"]     = 0.0;
    features["v_ent_deg_vars"]     = 0.0;
    features["v_ent_domdeg_vars"]  = 0.0;
  }

  // Initialize domains (18 features).
  void
  init_doms() {
    features["d_bool_vars"]        = 0.0;
    features["d_float_vars"]       = 0.0;
    features["d_int_vars"]         = 0.0;
    features["d_set_vars"]         = 0.0;
    features["d_ratio_bool_vars"]  = 0.0;
    features["d_ratio_float_vars"] = 0.0;
    features["d_ratio_int_vars"]   = 0.0;
    features["d_ratio_set_vars"]   = 0.0;
    features["d_array_cons"]       = 0.0; 
    features["d_bool_cons"]        = 0.0;
    features["d_float_cons"]       = 0.0;
    features["d_int_cons"]         = 0.0;
    features["d_set_cons"]         = 0.0;
    features["d_ratio_array_cons"] = 0.0; 
    features["d_ratio_bool_cons"]  = 0.0;
    features["d_ratio_float_cons"] = 0.0;
    features["d_ratio_int_cons"]   = 0.0;
    features["d_ratio_set_cons"]   = 0.0;
  }

  // Initialize constraints (27).
  void
  init_cons() {  
    features["c_num_cons"]         = 0.0;
    features["c_ratio_cons"]       = 0.0;
    features["c_bounds_z"]         = 0.0;
    features["c_bounds_r"]         = 0.0;
    features["c_bounds_d"]         = 0.0;
    features["c_domain"]           = 0.0;
    features["c_priority"]         = 0.0;
    features["c_logprod_dom_cons"] = 0.0;
    features["c_logprod_deg_cons"] = 0.0;
    features["c_sum_dom_cons"]     = 0.0;
    features["c_sum_ari_cons"]     = 0.0;
    features["c_sum_domdeg_cons"]  = 0.0;
    features["c_min_dom_cons"]     = inf;
    features["c_min_deg_cons"]     = inf;
    features["c_min_domdeg_cons"]  = inf;
    features["c_max_dom_cons"]     = 0.0;
    features["c_max_deg_cons"]     = 0.0;
    features["c_max_domdeg_cons"]  = 0.0;
    features["c_avg_dom_cons"]     = 0.0;
    features["c_avg_deg_cons"]     = 0.0;
    features["c_avg_domdeg_cons"]  = 0.0; 
    features["c_cv_dom_cons"]      = 0.0;
    features["c_cv_deg_cons"]      = 0.0;
    features["c_cv_domdeg_cons"]   = 0.0;
    features["c_ent_dom_cons"]     = 0.0;
    features["c_ent_deg_cons"]     = 0.0;
    features["c_ent_domdeg_cons"]  = 0.0;
  }

  // Initialize global constraints (4 features).
  void
  init_globals() {
    features["gc_global_cons"] = 0.0;
    features["gc_ratio_globs"] = 0.0;
    features["gc_diff_globs"]  = 0.0;
    features["gc_ratio_diff"]  = 0.0;
  }

  // Initialize solving (11 features).
  void
  init_solve() {
    features["s_bool_search"]  = 0.0;
    features["s_int_search"]   = 0.0;
    features["s_set_search"]   = 0.0;
    features["s_goal"]         = 0.0;
    features["s_labeled_vars"] = 0.0;
    features["s_first_fail"]   = 0.0;
    features["s_input_order"]  = 0.0;
    features["s_other_var"]    = 0.0;
    features["s_indomain_min"] = 0.0;
    features["s_indomain_max"] = 0.0;
    features["s_other_val"]    = 0.0;    
  }

  // Initialize objective function (8 features).
  void
  init_objfn() {
    features["o_dom"]      = 0.0;
    features["o_dom_avg"]  = 0.0;
    features["o_dom_std"]  = 0.0;
    features["o_dom_deg"]  = 0.0;
    features["o_deg"]      = 0.0;
    features["o_deg_avg"]  = 0.0;
    features["o_deg_std"]  = 0.0;
    features["o_deg_cons"] = 0.0;
  }

  // Auxiliary function for computing variable degrees and constraint domains.
  void
  update_cons(const var_info& vi, set<int>& con_vars, double& dom) {
    std::pair<set<int>::const_iterator, bool> p;
    int var_id;
    string var_name;
    if (vi.alias) {
      var_id = vi.alias->id;
      var_name = vi.alias->name;
    }
    else
      if (vi.assigned)
        return;
      else {
        var_id = vi.id;
        var_name = vi.name;
      }
    p = con_vars.insert(var_id);
    if (p.second) {
      ++vars_to_info[var_name].degree;
      dom += log2(vars_to_info[var_name].dom_size);
    }
  }

  // Auxiliary function for computing variables statistics.
  void
  final_update_vars() {
    double n = features["d_bool_vars"] + features["d_float_vars"]
             + features["d_int_vars"]  + features["d_set_vars"];
    features["v_num_vars"] =  n;
    features["v_ratio_bounded"] =
    (features["v_num_aliases"]  + features["v_num_consts"]) / n; 
    double c = features["c_num_cons"];
    double g = features["gc_global_cons"];
    features["gc_ratio_diff"] = features["gc_diff_globs"] / g;
    features["v_ratio_vars"]   = n / c;
    features["c_ratio_cons"]   = c / n;
    features["gc_ratio_globs"] = g / c;

    features["d_ratio_bool_vars"]  = features["d_bool_vars"]  / n;
    features["d_ratio_float_vars"] = features["d_float_vars"] / n;
    features["d_ratio_int_vars"]   = features["d_int_vars"]   / n;
    features["d_ratio_set_vars"]   = features["d_set_vars"]   / n;
    features["d_ratio_array_cons"] = features["d_array_cons"] / c;
    features["d_ratio_bool_cons"]  = features["d_bool_cons"]  / c;
    features["d_ratio_float_cons"] = features["d_float_cons"] / c;
    features["d_ratio_int_cons"]   = features["d_int_cons"]   / c;
    features["d_ratio_set_cons"]   = features["d_set_cons"]   / c;

    double m = features["v_sum_dom_vars"] / n;
    features["v_avg_dom_vars"] = m;
    features["v_cv_dom_vars"]  = sqrt((sum_dom_vars2 / n) - m * m) / m;
    double h = 0;
    for (count_iterator i  = count_dom_vars.begin();
                        i != count_dom_vars.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["v_ent_dom_vars"] = log2(n) - h / n;

    for (vars_iterator iter  = vars_to_info.begin(); 
                       iter != vars_to_info.end(); iter++)
      if (!iter->second.array) {
        int deg = iter->second.degree;
        if (deg < features["v_min_deg_vars"])
          features["v_min_deg_vars"] = deg;
        if (deg > features["v_max_deg_vars"])
          features["v_max_deg_vars"] = deg;
        if (deg != 0) {
          features["v_sum_deg_vars"] += deg;
          sum_deg_vars2 += deg * deg;
          ++count_deg_vars[deg];
          features["v_logprod_deg_vars"] += log2(deg);
          double domdeg = iter->second.dom_size / deg;
          features["v_sum_domdeg_vars"] += domdeg;
          sum_domdeg_vars2 += domdeg * domdeg;
          if (domdeg < features["v_min_domdeg_vars"])
            features["v_min_domdeg_vars"] = domdeg;
          if (domdeg > features["v_max_domdeg_vars"])
            features["v_max_domdeg_vars"] = domdeg;
          ++count_domdeg_vars[floor(domdeg + 0.5)];
        }
        else
          if (!iter->second.assigned)
            std::cerr << "Warning: variable " << iter->second.name
                      << " has degree 0." << endl;
      }
    m = features["v_sum_deg_vars"] / n;
    features["v_avg_deg_vars"] = m;
    features["v_cv_deg_vars"]  = sqrt((sum_deg_vars2 / n) - m * m) / m;
    h = 0;
    for (count_iterator i  = count_deg_vars.begin(); 
                        i != count_deg_vars.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["v_ent_deg_vars"] = log2(n) - h / n;

    m = features["v_sum_domdeg_vars"] / n;
    features["v_avg_domdeg_vars"] = m;
    features["v_cv_domdeg_vars"]  = sqrt((sum_domdeg_vars2 / n) - m * m) / m;
    h = 0;
    for (count_iterator i  = count_domdeg_vars.begin(); 
                        i != count_domdeg_vars.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["v_ent_domdeg_vars"] = log2(n) - h / n;
  }

  // Auxiliary function for computing constraints statistics.
  void
  final_update_cons() {
    double n = features["c_num_cons"];
    double m = features["c_sum_dom_cons"] / n;
    features["c_avg_dom_cons"] = m;
    features["c_cv_dom_cons"]  = sqrt((sum_dom_cons2 / n) - m * m) / m;
    double h = 0;
    for (count_iterator i  = count_dom_cons.begin();
                        i != count_dom_cons.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["c_ent_dom_cons"] = log2(n) - h / n;

    m = sum_ari_cons / n;
    features["c_avg_deg_cons"] = m;
    features["c_cv_deg_cons"]  = sqrt((sum_ari_cons2 / n) - m * m) / m;
    h = 0;
    for (count_iterator i  = count_deg_cons.begin(); 
                        i != count_deg_cons.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["c_ent_deg_cons"] = log2(n) - h / n;

    m = features["c_sum_domdeg_cons"] / n;
    features["c_avg_domdeg_cons"] = m;
    features["c_cv_domdeg_cons"]  = sqrt((sum_domdeg_cons2 / n) - m * m) / m;
    h = 0;
    for (count_iterator i  = count_domdeg_cons.begin();
                        i != count_domdeg_cons.end(); ++i) {
      double x = i->second;
      h += x * log2(x);
    }
    features["c_ent_domdeg_cons"] = log2(n) - h / n;
  }

  // Auxiliary function for computing search statistics.
  void
  update_search(expr_list* e) {
    expr_list::iterator i = e->begin();
    if ((*i)->type() == ARRAY_EXPR) {
      expr_list* anns = (*i)->value().list_val;
      for (expr_list::iterator j = anns->begin(); j != anns->end(); ++j) {
        update_search(anns);
      }
      return;
    }
    string search = string((*i)->value().string_val);
    if (search == "bool_search")
      ++features["s_bool_search"];
    else if (search == "int_search")
      ++features["s_int_search"];
    else if (search == "set_search")
      ++features["s_set_search"];
    else
      return;
    ++i;
    if ((*i)->type() == ARRAY_EXPR) {
      expr_list* el = (*i)->value().list_val;
      expr_set es;
      set_expr::list_to_set(*el, es);
      features["s_labeled_vars"] += es.size();
    }
    else
      ++features["s_labeled_vars"];
    ++i;
    string var_choice = string((*i)->value().string_val);
    if (var_choice == "input_order")
      ++features["s_input_order"];
    else if (var_choice == "first_fail")
      ++features["s_first_fail"];
    else
      ++features["s_other_var"];
    ++i;
    string val_choice = string((*i)->value().string_val);
    if (val_choice == "indomain_min")
      ++features["s_indomain_min"];
    else if (val_choice == "indomain_max")
      ++features["s_indomain_max"];
    else
      ++features["s_other_val"];
  }

  // Auxiliary function for computing objective function statistics.
  void 
  final_update_obj() {
    double dom = obj_var.dom_size;
    double deg = obj_var.degree;
    double avg_dom = features["v_avg_dom_vars"];
    double std_dom = features["v_cv_dom_vars"] * avg_dom;
    double avg_deg = features["v_avg_deg_vars"];
    double std_deg = features["v_cv_deg_vars"] * avg_deg;
    double m = features["c_num_cons"];

    features["o_dom"] = dom;
    features["o_dom_avg"] = dom / avg_dom;
    features["o_dom_std"] = (dom - avg_dom) / std_dom;
    features["o_dom_deg"] = dom / deg;

    features["o_deg"] = deg;
    features["o_deg_avg"] = deg / avg_deg;
    features["o_deg_std"] = (deg - avg_deg) / std_deg;
    features["o_deg_cons"] = deg / m;
  }

};

double static_features::inf = std::numeric_limits<double>::infinity();
int static_features::var_id = 0;
int static_features::con_id = 0;
// Associates a counter to each global constraints.
map<string, int>
init_glob_names() {
  map<string, int> globs;
  string names[] = {
"fzn_alldifferent_except_0", "fzn_all_different_int", "fzn_all_equal_int", "fzn_among", "fzn_arg_max_bool", "fzn_arg_max_int", "fzn_arg_min_bool", "fzn_arg_min_int", "fzn_at_least_int", "fzn_at_least_set", "fzn_at_most_int", "fzn_at_most_set", "fzn_bin_packing", "fzn_bin_packing_capa", "fzn_bin_packing_load", "fzn_circuit", "fzn_count_eq", "fzn_count_eq_reif", "fzn_cumulative", "fzn_cumulative_opt", "fzn_decreasing_bool", "fzn_decreasing_int", "fzn_diffn", "fzn_disjoint", "fzn_disjunctive_strict", "fzn_disjunctive_strict_opt", "fzn_exactly_set", "fzn_global_cardinality", "fzn_global_cardinality_closed", "fzn_global_cardinality_low_up", "fzn_global_cardinality_low_up_closed", "fzn_increasing_bool", "fzn_increasing_int", "fzn_int_set_channel", "fzn_inverse", "fzn_inverse_set", "fzn_lex_less_bool", "fzn_lex_lesseq_bool", "fzn_lex_lesseq_int", "fzn_lex_less_int", "fzn_link_set_to_booleans", "fzn_member_bool", "fzn_member_bool_reif", "fzn_member_int", "fzn_member_int_reif", "fzn_nvalue", "fzn_partition_set", "fzn_range", "fzn_regular", "fzn_roots", "fzn_sort", "fzn_sum_pred", "fzn_sum_set", "fzn_table_bool", "fzn_table_bool_reif", "fzn_table_int", "fzn_table_int_reif", "fzn_value_precede_int", "fzn_value_precede_set", "gecode_among_seq_bool", "gecode_among_seq_int", "gecode_array_set_element_intersect", "gecode_array_set_element_intersect_in", "gecode_array_set_element_partition", "gecode_array_set_element_union", "gecode_bin_packing_load", "gecode_bool_element", "gecode_bool_element2d", "gecode_circuit", "gecode_circuit_cost", "gecode_circuit_cost_array", "gecode_cumulatives", "gecode_global_cardinality", "gecode_global_cardinality_closed", "gecode_int_element", "gecode_int_element2d", "gecode_int_pow", "gecode_int_set_channel", "gecode_inverse_set", "gecode_link_set_to_booleans", "gecode_maximum_arg_bool_offset", "gecode_maximum_arg_int_offset", "gecode_member_bool_reif", "gecode_member_int_reif", "gecode_minimum_arg_bool_offset", "gecode_minimum_arg_int_offset", "gecode_nooverlap", "gecode_precede", "gecode_precede_set", "gecode_range", "gecode_regular", "gecode_schedule_cumulative_optional", "gecode_schedule_unary", "gecode_schedule_unary_optional", "gecode_set_weights", "gecode_table_bool", "gecode_table_bool_imp", "gecode_table_bool_reif", "gecode_table_int", "gecode_table_int_imp", "gecode_table_int_reif"
  };
  for (auto n : names)
    globs[n] = 0;
  return globs;
}
map<string, int> static_features::globals(init_glob_names());

// Associates a description to each global constraint.
map<string, string>
init_descr() {
  map<string, string> descr;
  descr["c_avg_deg_cons"] = "Average of the constraints degree";
  descr["c_avg_dom_cons"] = "Average of the constraints domain";
  descr["c_avg_domdeg_cons"] = 
    "Average of the ratio constraints domain/degree";
  descr["c_bounds_d"] = "No of constraints using 'boundsD' annotation";
  descr["c_bounds_r"] = "No of constraints using 'boundsR' annotation";
  descr["c_bounds_z"] = 
    "No of constraints using 'boundsZ' or 'bounds' annotation";
  descr["c_cv_deg_cons"] = "Coefficient of Variation of constraints degree";
  descr["c_cv_dom_cons"] = "Coefficient of Variation of constraints degree";
  descr["c_cv_domdeg_cons"] = 
    "Coefficient of Variation of the ratio constraints domain/degree";
  descr["c_domain"] = "No of constraints using 'domain' annotation";
  descr["c_ent_deg_cons"] = "Entropy of constraints degree";
  descr["c_ent_dom_cons"] = "Entropy of constraints domain";
  descr["c_ent_domdeg_cons"] = 
    "Entropy of the ratio constraints domain/degree";
  descr["c_logprod_deg_cons"] = 
    "Logarithm of the product of constraints degree";
  descr["c_logprod_dom_cons"] = 
    "Logarithm of the product of constraints domain";
  descr["c_max_deg_cons"] = "Maximum of the constraints degree";
  descr["c_max_dom_cons"] = "Maximum of the constraints domain";
  descr["c_max_domdeg_cons"] = 
    "Maximum of the ratio constraints domain/degree";
  descr["c_min_deg_cons"] = "Minimum of the constraints degree";
  descr["c_min_dom_cons"] = "Minimum of the constraints domain";
  descr["c_min_domdeg_cons"] = 
    "Minimum of the ratio constraints domain/degree";
  descr["c_num_cons"] = "Total no of constraints";
  descr["c_priority"] = "No of constraints using 'priority' annotation";
  descr["c_ratio_cons"] = "Ratio no of constraints / no of variables";
  descr["c_sum_ari_cons"] = "Sum of constraints arity";
  descr["c_sum_dom_cons"] = "Sum of constraints domain";
  descr["c_sum_domdeg_cons"] = "Sum of the ratio constraints domain/degree";
  descr["d_array_cons"] = "No of array constraints";
  descr["d_bool_cons"] = "No of boolean constraints";
  descr["d_bool_vars"] = "No of boolean variables";
  descr["d_float_cons"] = "No of float constraints";
  descr["d_float_vars"] = "No of float variables";
  descr["d_int_cons"] = "No of integer constraints";
  descr["d_int_vars"] = "No of integer variables";
  descr["d_ratio_array_cons"] = 
    "Ratio array constraints / total no of constraints";
  descr["d_ratio_bool_cons"] = 
    "Ratio boolean constraints / total no of constraints";
  descr["d_ratio_bool_vars"] = 
    "Ratio boolean variables / total no of variables";
  descr["d_ratio_float_cons"] = 
    "Ratio float constraints / total no of constraints";
  descr["d_ratio_float_vars"] = 
    "Ratio float variables / total no of variables";
  descr["d_ratio_int_cons"] = 
    "Ratio integer constraints / total no of constraints";
  descr["d_ratio_int_vars"] = 
    "Ratio integer variables / total no of variables";
  descr["d_ratio_set_cons"] = 
    "Ratio set constraints / total no of constraints";
  descr["d_ratio_set_vars"] = "Ratio set variables / total no of variables";
  descr["d_set_cons"] = "No of set constraints";
  descr["d_set_vars"] = "No of set variables";
  descr["gc_diff_globs"] = "No of different global constraints";
  descr["gc_global_cons"] = "Total no of global constraints";
  descr["gc_ratio_diff"] = 
    "Ratio different global constraints / no of global constraints";
  descr["gc_ratio_globs"] = 
    "Ratio no of global constraints / total no of constraints";
  descr["o_deg"] = "Degree of the objective variable";
  descr["o_deg_avg"] = 
    "Ratio degree of the objective variable / average of var degree";
  descr["o_deg_cons"] = 
    "Ratio degree of the objective variable / number of constraints";
  descr["o_deg_std"] = 
    "Standardization of the degree of the objective variable";
  descr["o_dom"] = "Domain size of the objective variable";
  descr["o_dom_avg"] = 
    "Ratio domain of the objective variable / average of var domain";
  descr["o_dom_deg"] = 
    "Ratio domain of the objective variable / degree of the obj var";
  descr["o_dom_std"] = 
    "Standardization of the domain of the objective variable";
  descr["s_bool_search"] = "Number of 'bool_search' annotations";
  descr["s_first_fail"] = "Number of 'int_search' annotations";
  descr["s_goal"] = "Solve goal (1 = satisfy, 2 = minimize, 3 = maximize)";
  descr["s_indomain_max"] = "Number of 'indomain_max' annotations";
  descr["s_indomain_min"] = "Number of 'indomain_min' annotations";
  descr["s_input_order"] = "Number of 'input_order' annotations";
  descr["s_int_search"] = "Number of 'int_search' annotations";
  descr["s_labeled_vars"] = "Number of variables to be assigned";
  descr["s_other_val"] = "Number of other value search heuristics";
  descr["s_other_var"] = "Number of other variable search heuristics";
  descr["s_set_search"] = "Number of 'set_search' annotations";
  descr["v_avg_deg_vars"] = "Average of the variables degree";
  descr["v_avg_dom_vars"] = "Average of the variables domain";
  descr["v_avg_domdeg_vars"] = "Average of the ratio variables domain/degree";
  descr["v_cv_deg_vars"] = "Coefficient of Variation of variables degree";
  descr["v_cv_dom_vars"] = "Coefficient of Variation of variables degree";
  descr["v_cv_domdeg_vars"] = 
    "Coefficient of Variation of the ratio variables domain/degree";
  descr["v_def_vars"] = "Number of defined variables";
  descr["v_ent_deg_vars"] = "Entropy of variables degree";
  descr["v_ent_dom_vars"] = "Entropy of variables domain";
  descr["v_ent_domdeg_vars"] = "Entropy of the ratio variables domain/degree";
  descr["v_intro_vars"] = "Number of introduced variables";
  descr["v_logprod_deg_vars"] = 
    "Logarithm of the product of variables degree";
  descr["v_logprod_dom_vars"] = 
    "Logarithm of the product of variables domain";
  descr["v_max_deg_vars"] = "Maximum of the variables degree";
  descr["v_max_dom_vars"] = "Maximum of the variables domain";
  descr["v_max_domdeg_vars"] = "Maximum of the ratio variables domain/degree";
  descr["v_min_deg_vars"] = "Minimum of the variables degree";
  descr["v_min_dom_vars"] = "Minimum of the variables domain";
  descr["v_min_domdeg_vars"] = "Minimum of the ratio variables domain/degree";
  descr["v_num_aliases"] = "Number of alias variables";
  descr["v_num_consts"] = "Number of constant variables";
  descr["v_num_vars"] = "Total no of variables variables";
  descr["v_ratio_bounded"] = 
    "Ratio (aliases + constants) / total no of variables";
  descr["v_ratio_vars"] = "Ratio no of variables / no of constraints";
  descr["v_sum_deg_vars"] = "Sum of variables degree";
  descr["v_sum_dom_vars"] = "Sum of variables domain";
  descr["v_sum_domdeg_vars"] = "Sum of the ratio variables domain/degree";
  return descr;
}
map<string, string> static_features::description(init_descr());
