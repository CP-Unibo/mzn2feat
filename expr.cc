/*
* Class for modeling FlatZinc expressions.
*/

#include<iostream>
using std::cout;
using std::endl;

#include <list>
#include <set>
#include <string>
#include <boost/lexical_cast.hpp>

using std::list;
using std::set;
using std::string;

enum expr_type {
 BOOL_EXPR,
 INT_EXPR,
 FLOAT_EXPR,
 STRING_EXPR,
 ARRAY_EXPR,
 SET_EXPR
};

union expr_value;

class expression {

public:

  // The value represented by the expression.
  virtual expr_value value() = 0;
  
  virtual expr_type type()   = 0;
  
  virtual void destroy()     = 0;
  
  friend bool operator==(expression& e1, expression& e2);
  
};

typedef expression*  p_expr;
typedef list<p_expr> expr_list;
typedef  set<p_expr> expr_set;

union expr_value {
  bool          bool_val;
  double       float_val;
  int            int_val;
  const char* string_val;
  expr_list*    list_val;
  expr_set*      set_val;
  
  expr_value(bool b)        : bool_val(b)           {}
  expr_value(double d)      : float_val(d)          {}
  expr_value(int i)         : int_val(i)            {}
  expr_value(string s)      : string_val(s.c_str()) {}
  expr_value(expr_list* el) : list_val(el)          {}
  expr_value(expr_set* es)  : set_val(es)           {}
};

class bool_expr: public expression {
  
private:
  
  bool val;
  
public:
  
  bool_expr(bool b) : val(b) {}
  
  expr_value
  value() {
    return expr_value(val);
  }
  
  expr_type
  type() {
    return BOOL_EXPR;  
  }
  
  void destroy() { 
    this->~bool_expr(); 
  }
  
};

class float_expr: public expression {
  
private:
  
  float val;
  
public:
  
  float_expr(double d) : val(d) {}
  
  expr_value
  value() {
    return expr_value(val);
  }
  
  expr_type
  type() {
    return FLOAT_EXPR;  
  }
  
  void destroy() { 
    this->~float_expr(); 
  }
  
};

class int_expr: public expression {
  
private:
  
  int val;
  
public:
  
  int_expr(int i) : val(i) {}
  
  expr_value
  value() {
    return expr_value(val);
  }
  
  expr_type
  type() {
    return INT_EXPR;  
  }
  
  void destroy() { 
    this->~int_expr(); 
  }
  
};

class string_expr: public expression {
  
private:
  
  string val;
  
public:
  
  string_expr(const char* s) : val(s) {}
  
  string_expr(const char* s, int i) {
    val = string(s) + "[" + boost::lexical_cast<string>(i) + "]";
  }
  
  expr_value
  value() {
    return expr_value(val);
  }
  
  expr_type
  type() {
    return STRING_EXPR;  
  }
 
  void destroy() { 
    this->~string_expr(); 
  }
  
};

class array_expr: public expression {
  
private:
  
  expr_list* val;
  
public:
  
  array_expr() : val(new expr_list()) {}
  
  array_expr(const expr_list& el) : val(new expr_list(el)) {}
  
  array_expr(const char* s, const expr_list& el) {
    val = new expr_list(el);
    val->push_front(new string_expr(s));
  }
  
  expr_value
  value() {
    return new expr_list(*val);
  }
  
  expr_type
  type() {
    return ARRAY_EXPR;  
  }
  
  void
  destroy() {
    for (expr_list::iterator i = val->begin(); i != val->end(); ++i)
      (*i)->destroy();
    delete val;
    val = NULL;
  }
  
  ~array_expr() {
    destroy();
  }
  
};
  
class set_expr: public expression {
  
private:
  
  expr_set* val;
  
public:
  
  static void
  list_to_set(const expr_list& el, expr_set& es) {
    for (expr_list::const_iterator i = el.begin(); i != el.end(); ++i) {
      expression* e = *i;
      bool found = false;
      for (expr_set::iterator j = es.begin(); j != es.end(); ++j)
	if (*e == *(*j)) {
	  found = true;
	  break;
	}
      if (!found)
        es.insert(e);
    }
  }
  
  set_expr() : val(new expr_set()) {}
  
  set_expr(const expr_list& el) {
    expr_set es;
    list_to_set(el, es);
    val = new expr_set(es);
  }
  
  set_expr(int a, int b) {
    val = new expr_set();
    expr_set::iterator it = val->begin();
    for (int i = a; i <= b; ++i) {
      val->insert(it, new int_expr(i));
      ++it;
    }
  }
  
  expr_value
  value() {
    return expr_value(val);
  }
  
  expr_type
  type() {
    return SET_EXPR;  
  }
      
  void
  destroy() {
    for (expr_set::iterator i = val->begin(); i != val->end(); ++i)
      (*i)->destroy();
    delete val;
    val = NULL;
  }
  
  ~set_expr() {
    destroy();
  }
  
};

bool 
operator==(expression& ex1, expression& ex2) {
  expression* e1 = &ex1;
  expression* e2 = &ex2;
  if (e1->type() != e2->type())
    return false;
  switch(e1->type()) {
    case BOOL_EXPR:
      return e1->value().bool_val   == e2->value().bool_val;
    case FLOAT_EXPR:
      return e1->value().float_val  == e2->value().float_val;
    case INT_EXPR:
      return e1->value().int_val    == e2->value().int_val;
    case STRING_EXPR: 
      return string(e1->value().string_val) == string(e2->value().string_val);
    case ARRAY_EXPR: {
      expr_list el1 = *(e1->value().list_val);
      expr_list el2 = *(e2->value().list_val);
      if (el1.size() != el2.size())
	return false;
      for (expr_list::iterator i1  = el1.begin(), i2 = el2.begin(); 
	                       i1 != el1.end();   ++i1, ++i2)
	      if (!(*(*i1) == *(*i2)))
		return false;
      return true;
    }
    // FIXME: This could be not sound in general.
    case SET_EXPR: {
      expr_set el1 = *(e1->value().set_val);
      expr_set el2 = *(e2->value().set_val);
      if (el1.size() != el2.size())
	return false;
      for (expr_set::iterator i1 = el1.begin(), i2 = el2.begin(); 
	    i1 != el1.end(); ++i1, ++i2)
	      if (!(*(*i1) == *(*i2)))
		return false;
      return true;        
    }  
    default:
      return false;
  }
}
