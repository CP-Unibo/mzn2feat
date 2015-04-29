/*
* Extract the static features.
*/

#include <cmath>
#include <iostream>
#include <limits>
#include <map>
#include <vector>
#include <signal.h>
#include <exception>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/clustering_coefficient.hpp>
#include <boost/graph/exterior_property.hpp>
#include "expr.cc"

#define TIMEOUT_GRAPH   2
#define EXIT_CODE_GRAPH 8

using std::cout;
using std::endl;
using std::map;
using std::ostream;
using std::vector;
using namespace boost;


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
typedef map<double, double>   :: const_iterator  count_iterator;

// Graphs typedefs.
typedef adjacency_list <vecS, vecS, undirectedS> Graph;
typedef graph_traits<Graph> :: vertex_iterator vertex_iter;
typedef exterior_vertex_property<Graph, float> ClusteringProperty;
typedef ClusteringProperty :: container_type ClusteringContainer;
typedef ClusteringProperty :: map_type ClusteringMap;
typedef Graph :: vertex_descriptor Vertex;

class static_features;

static_features* p_this;

class static_features {

public:
  
  static double inf;
  map<string, double>   features;
  map<string, var_info> vars_to_info;
  bool vars_ok;
  bool cons_ok;
  bool solve_ok;
  
  static_features() {
    init_vars();
    init_doms();
    init_cons();
    init_globs();
    init_graph();
    init_solve();
    // Auxiliary variables.
    vars_ok          = false;
    cons_ok          = false;
    solve_ok         = false;
    sum_ari_cons     = 0.0;
    sum_dom_vars2    = 0.0;
    sum_deg_vars2    = 0.0;
    sum_domdeg_vars2 = 0.0;
    sum_dom_cons2    = 0.0;
    sum_ari_cons2    = 0.0;
    sum_domdeg_cons2 = 0.0;
  }
  
  ~static_features() {
    for (vars_iterator i  = vars_to_info.begin(); 
	               i != vars_to_info.end(); ++i)
      if (i->second.alias)
        delete i->second.alias;
  }
  
  
  /*
   * Updates the features for a bounded variable (i.e. a constant or an alias).
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
   * Updates the features for an unbounded variable.
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
   * Updates the features for an array of bounded variables.
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
      string var_name = array_name + "[" + boost::lexical_cast<string>(i) + "]";
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
   * Updates  the features for an array of unbounded variables.
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
      string var_name = array_name + "[" + boost::lexical_cast<string>(i) + "]";
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
    map<string, string>::iterator it = globals.find(name);
    if (it != globals.end()) {
      ++features["gc_global_cons"];
      ++features[it->second];
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
      for (expr_list::iterator i = params->begin(); i != params->end(); ++i)
	switch ((*i)->type()) {
	  // The argument is a variable of the form A[i]. 
	  case ARRAY_EXPR: {
	    expr_list* exprs = (*i)->value().list_val;
	    for (expr_list::iterator j = exprs->begin(); j != exprs->end(); ++j)
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
		string var_id = var_name + "[" + boost::lexical_cast<string>(j) + "]";
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
      
      // Builds the variables graph on the fly.
      cons_to_vars[con_id++] = con_vars;
      set<int>::iterator prec_end = con_vars.end();
      --prec_end;
      for (set<int>::iterator i = con_vars.begin(); i != prec_end; ++i)
	for (set<int>::iterator j = i; j != con_vars.end(); ++j) {
	  std::pair<int, int> edge(*i, *j);
	  if (*i != *j && vg_edges.find(edge) == vg_edges.end()) {
	    add_edge(*i, *j, vars_graph); 
	    vg_edges.insert(edge);
	  }
	};
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
   * Final computation.
   */
  void 
  final_update() {
    if (vars_ok)
      final_update_vars();
    else
      def_update_vars();
    if (cons_ok)
      final_update_cons();
    else
      def_update_cons();
    if (!solve_ok)
      def_update_solve();
    // Set a timeout on graph-based features; moreover, possible exceptions 
    // are caught (typically, memory exceptions). 
    p_this = this;
    signal(SIGALRM, timeout_cg);
    alarm(TIMEOUT_GRAPH);
    try {
      update_deg_cg();
      update_clust_cg();
    }
    catch (std::exception e) {
      std::cerr << "CG exception: " << e.what() << endl;
    }
    signal(SIGALRM, timeout_vg);
    alarm(TIMEOUT_GRAPH);
    try {
      update_deg_vg();
      update_diam_vg();
    }
    catch (std::exception e) {
      std::cerr << "VG exception: " << e.what() << endl;
    }
  }  
  
  /*
   * Returns a string representation of the features keys (i.e. the name of 
   * the attributes).
   */
  string
  keys_row(char sep = ',') {
    string row = "";
    feat_iterator end = features.end();
    feat_iterator iter;
    --end;
    for (iter = features.begin(); iter != end; iter++)
      row += iter->first + sep;
    row += iter->first;
    return row;
  }
  
  /*
   * Returns a string representation of the features values (i.e. the values of 
   * the attributes).
   */
  string
  values_row(char sep = ',') {
    string row = "";
    feat_iterator end = features.end();
    feat_iterator iter;
    --end;
    for (iter = features.begin(); iter != end; iter++)
      row += boost::lexical_cast<string>(iter->second) + sep;
    row += boost::lexical_cast<string>(iter->second);
    return row;
  }
  
  /*
   * Prints a representation of the features.
   */
  void
  print_items() {
    int i = 1;
    for (feat_iterator iter  = features.begin(); 
	               iter != features.end(); iter++, i++)
      cout << i << ". " << iter->first << ": " << iter->second << endl;
  }
  
private:
  
  static int var_id;
  static int con_id;
  static map<string, string> globals;
  
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
  
  set<std::pair<int, int> > vg_edges;
  
  Graph vars_graph;
  Graph cons_graph;

  void
  init_vars() {
    // Variables (27).
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
  
  void
  def_update_vars() {
    features["v_num_vars"]         = -1;
    features["v_num_consts"]       = -1;
    features["v_ratio_vars"]       = -1;
    features["v_num_aliases"]      = -1;
    features["v_ratio_bounded"]    = -1;
    features["v_def_vars"]         = -1;
    features["v_intro_vars"]       = -1;
    features["v_logprod_dom_vars"] = -1;
    features["v_logprod_deg_vars"] = -1;
    features["v_sum_dom_vars"]     = -1;
    features["v_sum_deg_vars"]     = -1;
    features["v_sum_domdeg_vars"]  = -1;
    features["v_min_dom_vars"]     = -1;
    features["v_min_deg_vars"]     = -1;
    features["v_min_domdeg_vars"]  = -1;
    features["v_max_dom_vars"]     = -1;
    features["v_max_deg_vars"]     = -1;
    features["v_max_domdeg_vars"]  = -1;
    features["v_avg_dom_vars"]     = -1;
    features["v_avg_deg_vars"]     = -1;
    features["v_avg_domdeg_vars"]  = -1;
    features["v_cv_dom_vars"]      = -1;
    features["v_cv_deg_vars"]      = -1;
    features["v_cv_domdeg_vars"]   = -1;
    features["v_ent_dom_vars"]     = -1;
    features["v_ent_deg_vars"]     = -1;
    features["v_ent_domdeg_vars"]  = -1;
    
    features["d_bool_vars"]        = -1;
    features["d_float_vars"]       = -1;
    features["d_int_vars"]         = -1;
    features["d_set_vars"]         = -1;
    features["d_ratio_bool_vars"]  = -1;
    features["d_ratio_float_vars"] = -1;
    features["d_ratio_int_vars"]   = -1;
    features["d_ratio_set_vars"]   = -1;
  }
  
  void
  init_doms() {
    // Domains (18).
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
  
  void
  init_cons() {
    // Constraints (27).
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
  
  void
  init_globs() {
    // Global constraints (29).
    features["gc_global_cons"]   = 0.0;
    features["gc_ratio_globs"]   = 0.0;
    features["gc_all_diff"]      = 0.0;
    features["gc_all_equal"]     = 0.0;
    features["gc_among"]         = 0.0;
    features["gc_array_int"]     = 0.0;
    features["gc_array_set"]     = 0.0;
    features["gc_at_least_most"] = 0.0;
    features["gc_bin_packing"]   = 0.0;
    features["gc_bool_lin"]      = 0.0;  
    features["gc_circuit"]       = 0.0;
    features["gc_count"]         = 0.0;
    features["gc_cumulative"]    = 0.0;
    features["gc_decr_inc"]      = 0.0;
    features["gc_diffn"]         = 0.0;
    features["gc_disjoint"]      = 0.0;
    features["gc_global_card"]   = 0.0;
    features["gc_link_set"]      = 0.0;
    features["gc_inverse"]       = 0.0;
    features["gc_max_min_int"]   = 0.0;
    features["gc_member"]        = 0.0;
    features["gc_nvalue"]        = 0.0;
    features["gc_precede"]       = 0.0;
    features["gc_range"]         = 0.0;
    features["gc_regular"]       = 0.0;
    features["gc_schedule"]      = 0.0;
    features["gc_set_weights"]   = 0.0;
    features["gc_sort"]          = 0.0;
    features["gc_table"]         = 0.0;
  }
  
  void def_update_cons() {
    features["c_num_cons"]         = -1;
    features["c_ratio_cons"]       = -1;
    features["c_bounds_z"]         = -1;
    features["c_bounds_r"]         = -1;
    features["c_bounds_d"]         = -1;
    features["c_domain"]           = -1;
    features["c_priority"]         = -1;
    features["c_logprod_dom_cons"] = -1;
    features["c_logprod_deg_cons"] = -1;
    features["c_sum_dom_cons"]     = -1;
    features["c_sum_ari_cons"]     = -1;
    features["c_sum_domdeg_cons"]  = -1;
    features["c_min_dom_cons"]     = -1;
    features["c_min_deg_cons"]     = -1;
    features["c_min_domdeg_cons"]  = -1;
    features["c_max_dom_cons"]     = -1;
    features["c_max_deg_cons"]     = -1;
    features["c_max_domdeg_cons"]  = -1;
    features["c_avg_dom_cons"]     = -1;
    features["c_avg_deg_cons"]     = -1;
    features["c_avg_domdeg_cons"]  = -1; 
    features["c_cv_dom_cons"]      = -1;
    features["c_cv_deg_cons"]      = -1;
    features["c_cv_domdeg_cons"]   = -1;
    features["c_ent_dom_cons"]     = -1;
    features["c_ent_deg_cons"]     = -1;
    features["c_ent_domdeg_cons"]  = -1;
    
    features["d_array_cons"]       = -1; 
    features["d_bool_cons"]        = -1;
    features["d_float_cons"]       = -1;
    features["d_int_cons"]         = -1;
    features["d_set_cons"]         = -1;
    features["d_ratio_array_cons"] = -1; 
    features["d_ratio_bool_cons"]  = -1;
    features["d_ratio_float_cons"] = -1;
    features["d_ratio_int_cons"]   = -1;
    features["d_ratio_set_cons"]   = -1;
    
    features["gc_global_cons"]     = -1;
    features["gc_ratio_globs"]     = -1;
    features["gc_all_diff"]        = -1;
    features["gc_all_equal"]       = -1;
    features["gc_among"]           = -1;
    features["gc_array_int"]       = -1;
    features["gc_array_set"]       = -1;
    features["gc_at_least_most"]   = -1;
    features["gc_bin_packing"]     = -1;
    features["gc_bool_lin"]        = -1; 
    features["gc_circuit"]         = -1;
    features["gc_count"]           = -1;
    features["gc_cumulative"]      = -1;
    features["gc_decr_inc"]        = -1;
    features["gc_diffn"]           = -1;
    features["gc_disjoint"]        = -1;
    features["gc_global_card"]     = -1;
    features["gc_link_set"]        = -1;
    features["gc_inverse"]         = -1;
    features["gc_max_min_int"]     = -1;
    features["gc_member"]          = -1;
    features["gc_nvalue"]          = -1;
    features["gc_precede"]         = -1;
    features["gc_range"]           = -1;
    features["gc_regular"]         = -1;
    features["gc_schedule"]        = -1;
    features["gc_set_weights"]     = -1;
    features["gc_sort"]            = -1;
    features["gc_table"]           = -1;
  }  
  
  void
  init_graph() {
    // Graph based (20)
    features["gr_min_deg_vg"]   = -1.0; 
    features["gr_max_deg_vg"]   = -1.0;
    features["gr_avg_deg_vg"]   = -1.0;
    features["gr_cv_deg_vg"]    = -1.0;
    features["gr_ent_deg_vg"]   = -1.0;
    features["gr_min_deg_cg"]   = -1.0; 
    features["gr_max_deg_cg"]   = -1.0;
    features["gr_avg_deg_cg"]   = -1.0;
    features["gr_cv_deg_cg"]    = -1.0;
    features["gr_ent_deg_cg"]   = -1.0;
    features["gr_min_diam_vg"]  = -1.0; 
    features["gr_max_diam_vg"]  = -1.0;
    features["gr_avg_diam_vg"]  = -1.0;
    features["gr_cv_diam_vg"]   = -1.0;
    features["gr_ent_diam_vg"]  = -1.0;
    features["gr_min_clust_cg"] = -1.0; 
    features["gr_max_clust_cg"] = -1.0;
    features["gr_avg_clust_cg"] = -1.0;
    features["gr_cv_clust_cg"]  = -1.0;
    features["gr_ent_clust_cg"] = -1.0;
  }
  
  void
  init_solve() {
    // Solving (11).
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
  
  void
  def_update_solve() {
    features["s_bool_search"]  = -1;
    features["s_int_search"]   = -1;
    features["s_set_search"]   = -1;
    features["s_goal"]         = -1;
    features["s_labeled_vars"] = -1;
    features["s_first_fail"]   = -1;
    features["s_input_order"]  = -1;
    features["s_other_var"]    = -1;
    features["s_indomain_min"] = -1;
    features["s_indomain_max"] = -1;
    features["s_other_val"]    = -1;    
  }
  
  // Auxiliary function for computing variables deg. and constraints dom.
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
    
    features["v_ratio_vars"]       = n / c;
    features["c_ratio_cons"]       = c / n;
    features["gc_ratio_globs"]     = features["gc_global_cons"] / c; 
    features["d_ratio_bool_vars"]  = features["d_bool_vars"]    / n;
    features["d_ratio_float_vars"] = features["d_float_vars"]   / n;
    features["d_ratio_int_vars"]   = features["d_int_vars"]     / n;
    features["d_ratio_set_vars"]   = features["d_set_vars"]     / n;
    features["d_ratio_array_cons"] = features["d_array_cons"]   / c;
    features["d_ratio_bool_cons"]  = features["d_bool_cons"]    / c;
    features["d_ratio_float_cons"] = features["d_float_cons"]   / c;
    features["d_ratio_int_cons"]   = features["d_int_cons"]     / c;
    features["d_ratio_set_cons"]   = features["d_set_cons"]     / c;
    
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
	features["v_sum_deg_vars"] += deg;
	sum_deg_vars2 += deg * deg;
	if (deg < features["v_min_deg_vars"])
	  features["v_min_deg_vars"] = deg;
	if (deg > features["v_max_deg_vars"])
	  features["v_max_deg_vars"] = deg;
	++count_deg_vars[deg];
	if (deg != 0) {
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
    string search = string((*i)->value().string_val);
    if (search == "bool_search")
      ++features["s_bool_search"];
    else
      if (search == "int_search")
	++features["s_int_search"];
      else
	++features["s_set_search"];
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
    else
      if (var_choice == "first_fail")
	++features["s_first_fail"];
      else
	++features["s_other_var"];
    ++i;
    string val_choice = string((*i)->value().string_val);
    if (val_choice == "indomain_min")
      ++features["s_indomain_min"];
    else
      if (val_choice == "indomain_max")
	++features["s_indomain_max"];
      else
	++features["s_other_val"];
  }

  // Handler for CG timeout.
  static void 
  timeout_cg(int sig) {
    std::cerr << "CG timeout!" << endl;    
    signal(SIGALRM, timeout_vg);
    alarm(TIMEOUT_GRAPH);
    try {
      p_this->update_deg_vg();
      p_this->update_diam_vg();
    }
    catch (std::exception& e) {
      std::cerr << "VG exception: " << e.what() << endl;
      cout << p_this->values_row('|') << endl;
      exit(EXIT_CODE_GRAPH);
    }
  }

  // Handler for VG timeout.
  static void 
  timeout_vg(int param) {
    std::cerr << "VG timeout!" << endl;
    cout << p_this->values_row('|') << endl;
    exit(EXIT_CODE_GRAPH);
  }

  // Updates the CG degree statistics.
  void
  update_deg_cg() {
    vector<set<int> > cons;
    cons_iterator::iterator prec_end = cons_to_vars.end();
    --prec_end;
    // Builds CG.
    for (cons_iterator i = cons_to_vars.begin(); i != prec_end; ++i)
      for (cons_iterator j = i; j != cons_to_vars.end(); ++j)
        if ((*i).first != (*j).first && !disjoint((*i).second, (*j).second))
	  add_edge((*i).first, (*j).first, cons_graph);
    double sum  = 0;
    double sum2 = 0;
    int n = features["c_num_cons"];
    int min  = n - 1;
    int max  = 0;
    map<int, int> count;
    std::pair<vertex_iter, vertex_iter> vp;
    for (vp = vertices(cons_graph); vp.first != vp.second; ++vp.first) {
      int d = in_degree(*vp.first, cons_graph);
      sum  += d;
      sum2 += d * d;
      if (d < min)
	min = d;
      if (d > max)
	max = d;
      ++count[d];
    }
    features["gr_min_deg_cg"] = min; 
    features["gr_max_deg_cg"] = max;
    double m = sum / n;
    features["gr_avg_deg_cg"] = m;
    features["gr_cv_deg_cg"]  = sqrt((sum2 / n) - m * m) / m;
    sum = 0;
    for (map<int, int>::iterator i  = count.begin(); i != count.end(); ++i) {
      m = i->second;
      sum += m * log2(m);
    }
    features["gr_ent_deg_cg"] = log2(n) - sum / n;
  }

  // Returns true iff set1 and set2 are disjoint.
  bool
  disjoint(const set<int>& set1, const set<int>& set2) {
    set<int>::const_iterator it1 = set1.begin();
    set<int>::const_iterator it1_end = set1.end();
    set<int>::const_iterator it2 = set2.begin(); 
    set<int>::const_iterator it2_end = set2.end();
    if (*it1 > *set2.rbegin() || *it2 > *set1.rbegin()) 
      return true;
    while(it1 != it1_end && it2 != it2_end) {
      if (*it1 == *it2)
	return false;
      if (*it1 < *it2)
	it1++;
      else 
	it2++;
    }
    return true;
  }

  // Updates the CG clustering coefficient statistics.
  void
  update_clust_cg() {
    double sum  = 0;
    double sum2 = 0;
    int n = features["c_num_cons"];
    int min = 1;
    int max = 0;
    map<int, int> count;
    ClusteringProperty::container_type coefs(num_vertices(cons_graph));
    ClusteringMap cm(coefs, cons_graph);
    double m = all_clustering_coefficients(cons_graph, cm);
    graph_traits<Graph>::vertex_iterator i, end;
    for (tie(i, end) = vertices(cons_graph); i != end; ++i) {
      double c = get(cm, *i);
      sum2 += c * c;
      if (c < min)
	min = c;
      if (c > max)
	max = c;
      // Use unitary bins for floating point values.
      ++count[floor(c + 0.5)];
    }
    features["gr_min_clust_cg"] = min; 
    features["gr_max_clust_cg"] = max;
    features["gr_avg_clust_cg"] = m;
    features["gr_cv_clust_cg"]  = sqrt((sum2 / n) - m * m) / m;
    sum = 0;
    for (map<int, int>::iterator i  = count.begin(); i != count.end(); ++i) {
      m = i->second;
      sum += m * log2(m);
    }
    features["gr_ent_clust_cg"] = log2(n) - sum / n;
  }

  // Updates the VG degrees statistics.
  void
  update_deg_vg() {
    int n = features["v_num_vars"];
    // Add uncaught isolated nodes to variables graph.
    for (int i = num_vertices(vars_graph); i < n; ++i)
      add_vertex(vars_graph);
    double sum   = 0;
    double sum2  = 0;
    int min = n - 1;
    int max = 0;
    map<int, int>  count;
    std::pair<vertex_iter, vertex_iter> vp;
    
    for (vp = vertices(vars_graph); vp.first != vp.second; ++vp.first) {
      int deg = in_degree(*vp.first, vars_graph);
      sum  += deg;
      sum2 += deg * deg;
      if (deg < min)
	min = deg;
      if (deg > max)
	max = deg;
      ++count[deg];
    }
    features["gr_min_deg_vg"] = min; 
    features["gr_max_deg_vg"] = max;
    double m = sum / n;
    features["gr_avg_deg_vg"] = m;
    features["gr_cv_deg_vg"]  = sqrt((sum2 / n) - m * m) / m;
    sum = 0;
    for (map<int, int>::iterator i  = count.begin(); i != count.end(); ++i) {
      m = i->second;
      sum += m * log2(m);
    }
    features["gr_ent_deg_vg"] = log2(n) - sum / n;
  }

  // Updates the VG diameters statistics.
  void update_diam_vg() {
    int n = features["v_num_vars"];
    double sum  = 0;
    double sum2 = 0;
    int min  = n - 1;
    int max  = 0;
    map<int, int>  count;
    
    boost::graph_traits<Graph>::vertex_iterator vi, vi_end, next;
    for (boost::tie(vi, vi_end) = vertices(vars_graph); vi != vi_end; ++vi) {
      int diam = 0;
      list<int> S;
      S.push_back(*vi);
      int n = num_vertices(vars_graph);
      int distances[n];
      std::fill_n(distances, n, -1);
      distances[*vi] = 0;
      while (!S.empty()) {
	int u = S.back();
	S.pop_back();
	boost::graph_traits<Graph>::adjacency_iterator vii, vii_end;
	for (boost::tie(vii, vii_end) = adjacent_vertices(u, vars_graph); 
	    vii != vii_end; ++vii) {
	  int v = *vii;
	  if (distances[v] < 0) {
	    distances[v] = distances[u] + 1;
	    if (distances[v] > 0)
	      diam = distances[v];
	    S.push_back(v);
	  }
	}
      }
      sum  += diam;
      sum2 += diam * diam;
      if (diam < min)
	min = diam;
      if (diam > max)
	max = diam;
      ++count[diam];
    }
    
    features["gr_min_diam_vg"] = min;
    features["gr_max_diam_vg"] = max;
    double m = sum / n;
    features["gr_avg_diam_vg"] = m;
    features["gr_cv_diam_vg"]  = sqrt((sum2 / n) - m * m) / m;
    sum = 0;
    for (map<int, int>::iterator i  = count.begin(); i != count.end(); ++i) {
      m = i->second;
      sum += m * log2(m);
    }
    features["gr_ent_diam_vg"] = log2(n) - sum / n;
  }

};

double static_features::inf = std::numeric_limits<double>::infinity();
int static_features::var_id = 0;
int static_features::con_id = 0;

// Associates each global constraint to the corresponding class.
map<string, string>
init_globals() {
  map<string, string> globs;
  globs["all_different_int"]                     = "gc_all_diff";
  globs["all_equal_int"]                         = "gc_all_equal";
  globs["among"]                                 = "gc_among";
  globs["among_seq_int"]                         = "gc_among";
  globs["among_seq_bool"]                        = "gc_among";
  globs["array_int_lt"]                          = "gc_array_int";
  globs["array_int_lq"]                          = "gc_array_int";
  globs["gecode_array_set_element_intersect"]    = "gc_array_set";
  globs["gecode_array_set_element_intersect_in"] = "gc_array_set";
  globs["gecode_array_set_element_partition"]    = "gc_array_set";
  globs["gecode_array_set_element_union"]        = "gc_array_set";
  globs["array_set_partition"]                   = "gc_array_set";
  globs["at_least_int"]                          = "gc_at_least_most";
  globs["at_most_int"]                           = "gc_at_least_most";
  globs["gecode_bin_packing_load"]               = "gc_bin_packing";
  globs["bool_lin_eq"]                           = "gc_bool_lin";
  globs["bool_lin_ne"]                           = "gc_bool_lin";
  globs["bool_lin_le"]                           = "gc_bool_lin";
  globs["bool_lin_lt"]                           = "gc_bool_lin";
  globs["bool_lin_ge"]                           = "gc_bool_lin";
  globs["bool_lin_gt"]                           = "gc_bool_lin";
  globs["gecode_circuit"]                        = "gc_circuit";
  globs["gecode_circuit_cost"]                   = "gc_circuit";
  globs["gecode_circuit_cost_array"]             = "gc_circuit";
  globs["count"]                                 = "gc_count";
  globs["cumulatives"]                           = "gc_cumulative";
  globs["decreasing_bool"]                       = "gc_decr_inc";
  globs["decreasing_int"]                        = "gc_decr_inc";
  globs["increasing_bool"]                       = "gc_decr_inc";
  globs["increasing_int"]                        = "gc_decr_inc";
  globs["gecode_nooverlap"]                      = "gc_diffn";
  globs["disjoint"]                              = "gc_disjoint";
  globs["global_cardinality"]                    = "gc_global_card";
  globs["global_cardinality_closed"]             = "gc_global_card";    
  globs["global_cardinality_low_up"]             = "gc_global_card";
  globs["global_cardinality_low_up_closed"]      = "gc_global_card";
  globs["gecode_int_set_channel"]                = "gc_link_set";
  globs["gecode_link_set_to_booleans"]           = "gc_link_set";
  globs["inverse_offsets"]                       = "gc_inverse";
  globs["maximum_int"]                           = "gc_max_min_int";
  globs["minimum_int"]                           = "gc_max_min_int";
  globs["member_bool"]                           = "gc_member";
  globs["gecode_member_bool_reif"]               = "gc_member";
  globs["member_int"]                            = "gc_member";
  globs["gecode_member_int_reif"]                = "gc_member";
  globs["nvalue"]                                = "gc_nvalue";
  globs["gecode_precede"]                        = "gc_precede";
  globs["gecode_range"]                          = "gc_range";
  globs["regular"]                               = "gc_regular";
  globs["gecode_schedule_unary"]                 = "gc_schedule";
  globs["gecode_schedule_unary_optional"]        = "gc_schedule";
  globs["gecode_set_weights"]                    = "gc_set_weights";
  globs["sort"]                                  = "gc_sort";
  globs["table_bool"]                            = "gc_table";
  globs["table_int"]                             = "gc_table";
  return globs;
}

map<string, string> static_features::globals(init_globals());
