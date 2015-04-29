// Parser for FlatZinc 1.1.
// Authors: Nick Nethercote
//          Julien Fischer
//
// NOTE: the parser produced by the following grammar does not ensure
// that expressions are type correct.  Further type-checking after parsing
// is required for this.
//
// This file is in the public domain, and can be used without copyright
// restrictions.

/*
* Parser modified in order to extract static features.
*/

%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "static_features.cc"

extern "C" {
  int yyparse(void);
  int yylex(void);  
  int yywrap(void);
  int yyerror(char*);
}

const double MAX_INT_SIZE   = 20000001;
const double MAX_FLOAT_SIZE = static_features::inf;
const double MAX_SET_SIZE   = static_features::inf;

bool initialized = false;
expression* array_elems;
static_features sf;

%}

 
// Possible values for attributed tokens.
%union {
    const char* string_val;
    int         int_val;
    double      float_val;
    bool        bool_val;
    var_info    var_val;
    expression* p_expr;
    expr_list*  p_exprs;
    set<int>*   p_setint;
};

// Token kinds
%token <int_val>    INT_LITERAL
       <string_val> STRING_LITERAL IDENT UNDERSCORE_IDENT
       <float_val>  FLOAT_LITERAL 
       ARRAY BOOL CONSTRAINT FALSE FLOAT INT MAXIMIZE MINIMIZE OF
       SATISFY SET SOLVE TRUE VAR DOTDOT COLONCOLON

%type <var_val>  non_array_ti_expr_tail;
%type <var_val>  scalar_ti_expr_tail;
%type <var_val>  bool_ti_expr_tail;
%type <var_val>  float_ti_expr_tail;
%type <var_val>  int_ti_expr_tail;
%type <var_val>  set_ti_expr_tail;
%type <var_val>  array_decl_tail;
%type <p_expr>   expr;
%type <p_expr>   bool_literal;
%type <p_expr>   set_literal;
%type <p_expr>   array_literal;
%type <p_expr>   array_access_expr;
%type <p_expr>   array_decl_tail2;
%type <p_expr>   var_decl_item2;
%type <p_exprs>  constraint_elem;
%type <p_exprs>  ident_anns;
%type <p_exprs>  exprs;
%type <p_exprs>  annotations;
%type <p_setint> int_literals;
%%

//---------------------------------------------------------------------------
// Model top-level
//---------------------------------------------------------------------------

// Nb: these rules are left-recursive, which is good for Yacc as they run in
// constant stack space.  Earlier versions were right-recursive, and this
// caused stack overflows on large models.  The error recovery isn't great,
// but it's better than none.
// Predicates were been removed.

model : 
  var_decl_items constraint_items model_end

var_decl_items : 
  var_decl_items var_decl_item ';' 
  | {
    sf.vars_ok = true;
  }
 
constraint_items: 
  constraint_items constraint_item ';' 
  | {
    sf.cons_ok = true;
  }
 
model_end : 
  solve_item ';' {
    sf.solve_ok = true;
  }
    
    
//---------------------------------------------------------------------------
// Items
//---------------------------------------------------------------------------

var_decl_item:
  VAR non_array_ti_expr_tail ':' ident_anns var_decl_item2 {
    $2.name = $4->front()->value().string_val;
    $4->pop_front();
    expr_set es;
    set_expr::list_to_set(*$4, es);
    $2.anns   = new expr_set(es);
    $2.array  = false;
    if ($5) {
      sf.update_assigned_variable($2, $5);
      $2.assigned = true;
      initialized = false;
    }
    else
      sf.update_variable($2);
  }
  | non_array_ti_expr_tail ':' ident_anns '=' expr {
    $1.name = $3->front()->value().string_val;
    $3->pop_front();
    expr_set es;
    set_expr::list_to_set(*$3, es);
    $1.anns = new expr_set(es);
    sf.update_assigned_variable($1, $5);
  }
  | ARRAY '[' INT_LITERAL DOTDOT INT_LITERAL ']' OF array_decl_tail {
    $8.array  = true;
    $8.begin  = $3;
    $8.end    = $5;
    if (initialized) {
      expr_list* el = array_elems->value().list_val;
      sf.update_assigned_var_array($8, el);
      initialized = false;
    }
    else
      sf.update_var_array($8);
  }

var_decl_item2:
  '=' expr {
    initialized = true;
    $$ = $2;
  }
  | {
    initialized = false;
    $$ = NULL;
  }

array_decl_tail:
  non_array_ti_expr_tail ':' ident_anns '=' array_literal {
    initialized = true;
    $$ = $1;
    $$.name = $3->front()->value().string_val;
    $3->pop_front();
    expr_set es;
    set_expr::list_to_set(*$3, es);
    $$.anns = new expr_set(es);
    array_elems = $5;
  }
  | VAR non_array_ti_expr_tail ':' ident_anns array_decl_tail2 {
    $$ = $2;
    $$.name = $4->front()->value().string_val;
    $4->pop_front();
    expr_set es;
    set_expr::list_to_set(*$4, es);
    $$.anns = new expr_set(es);
    array_elems = $5;
  }
  
array_decl_tail2:
  '=' array_literal {
    initialized = true;
    $$ = $2;
  }
  | {
    initialized = false;
    $$ = NULL;
  }

ident_anns:
  IDENT annotations {
    $2->push_front(new string_expr($1));
    $$ = $2;
  }
  | UNDERSCORE_IDENT annotations {
    $2->push_front(new string_expr($1));
    $$ = $2;
  }

constraint_item:
  CONSTRAINT constraint_elem annotations {
    sf.update_constraint($2, $3);
  }
  
constraint_elem:
  IDENT '(' exprs ')' {
    $3->push_front(new string_expr($1));
    $$ = $3;
  }

solve_item:
  SOLVE annotations solve_kind {
    sf.update_solve(*$2);
  }

solve_kind:
  SATISFY {
    sf.features["s_goal"] = 1;
  }
  | MINIMIZE expr {
    sf.features["s_goal"] = 2;
  }
  | MAXIMIZE expr {
    sf.features["s_goal"] = 3;
  }

//---------------------------------------------------------------------------
// Type-Inst Expression Tails
//---------------------------------------------------------------------------

non_array_ti_expr_tail:
    scalar_ti_expr_tail
  | set_ti_expr_tail

scalar_ti_expr_tail:
    bool_ti_expr_tail
  | int_ti_expr_tail
  | float_ti_expr_tail

bool_ti_expr_tail:
  BOOL {
    $$.type = BOOL_EXPR;
    $$.dom_size = 2;
  }

int_ti_expr_tail:
  INT {
    $$.type = INT_EXPR;
    $$.dom_size = MAX_INT_SIZE;
  }
  | INT_LITERAL DOTDOT INT_LITERAL {
    $$.type = INT_EXPR;
    $$.dom_size = $3 - $1 + 1;
  }
  | '{' int_literals '}' {
    $$.type = INT_EXPR;
    $$.dom_size = $2->size();
  }

int_literals:
  INT_LITERAL ',' int_literals {
    $3->insert($1);
    $$ = $3;
  }
  | INT_LITERAL {
    $$ = new set<int>;
    $$->insert($1);
  }

float_ti_expr_tail:
  FLOAT {
    $$.type = FLOAT_EXPR;
    $$.dom_size = MAX_FLOAT_SIZE;
  }
  | FLOAT_LITERAL DOTDOT FLOAT_LITERAL {
    $$.type = FLOAT_EXPR;
    $$.dom_size = $3 - $1 + 1;
  }

set_ti_expr_tail:
  SET OF int_ti_expr_tail {
    $$.type = SET_EXPR;
    $$.dom_size = pow(2, $3.dom_size);
  }

//---------------------------------------------------------------------------
// Expressions
//---------------------------------------------------------------------------

exprs:
  expr ',' exprs {
    $3->push_front($1);
    $$ = $3;
  }
  | expr {
    $$ = new expr_list();
    $$->push_front($1);
  }

expr:
  bool_literal
  | INT_LITERAL {
    $$ = new int_expr($1);
  }
  | FLOAT_LITERAL {
    $$ = new float_expr($1);
  }
  | STRING_LITERAL {
    $$ = new string_expr($1);
  }
  | set_literal
  | array_literal
  | array_access_expr
  | IDENT {
    $$ = new string_expr($1);
  }
  | UNDERSCORE_IDENT {
    $$ = new string_expr($1);
  }
  | IDENT '(' exprs ')'	{ /* An annotation value with > 0 arguments. */
    $$ = new array_expr($1, *$3);
  }
  
bool_literal:
  FALSE { 
    $$ = new bool_expr(false);
  }
  | TRUE {
    $$ = new bool_expr(true);
  }

set_literal:
  '{' exprs '}' {
    $$ = new set_expr(*$2);
  }
  | '{' '}' {
    $$ = new set_expr();
  }
  | INT_LITERAL DOTDOT INT_LITERAL {
    $$ = new set_expr($1, $3);
  }

array_literal:
  '[' exprs ']' {
    $$ = new array_expr(*$2);
  }
  | '[' ']' {
    $$ = new array_expr();
  }

array_access_expr: 
  IDENT '[' INT_LITERAL ']' {
    $$ = new string_expr($1, $3);
  }
  | UNDERSCORE_IDENT '[' INT_LITERAL ']' {
    $$ = new string_expr($1, $3);
  }

//---------------------------------------------------------------------------
// Annotations
//---------------------------------------------------------------------------

annotations:
  COLONCOLON expr annotations {
    $3->push_front($2);
    $$ = $3;
  }
  | {
    $$ = new expr_list();
  }
  
%%

#include "lex.yy.c"

char* filename;

int main(int argc, char *argv[]) {
    
  if (argc != 2) {
      fprintf(stderr, "Usage: %s <file.fzn>\n", argv[0]);
      exit(1);
  }

  filename = argv[1];
  yyin = fopen(filename, "r");
  if (yyin == NULL) {
      fprintf(stderr, "cannot open file: '%s'\n", filename);
      exit(1);
  }
  yyparse();
  
  sf.final_update();
  //sf.print_items();
  //cout << sf.keys_row('|') << endl;
  cout << sf.values_row('|') << endl;
  
  return 0;
}

int yyerror(char *s) {
  if (0 == strcmp(yytext, ""))
    fprintf(stderr, "%s:%d: %s before end of file\n", filename, yylineno, s);
  else
    fprintf(stderr, "%s:%d: %s before '%s'\n", filename, yylineno, s, yytext);
  return 0;
}

/*
** This is only defined so the Flex library isn't needed.
*/
int yywrap() {
  return 1;
}
