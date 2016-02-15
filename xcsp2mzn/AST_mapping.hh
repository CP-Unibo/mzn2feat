/*
 * AST_mapping.hh
 *
 *  Created on: Mar 14, 2013
 *      Author: jacopo
 */

#include <xcsp-parser/XMLParser_libxml2.hh>

#ifndef AST_MAPPING_HH_
#define AST_MAPPING_HH_

using namespace std;
using namespace CSPXMLParser;

template <typename T>
static string 
to_string (T const& num) {
  std::stringstream s;
  s << num;
  return s.str();
}  

static bool  isBooleanOp (NodeType  oper)
          {
            return(   (F_NOT == oper) || (F_EQ  == oper) || (F_NE == oper)
                   || (F_GE  == oper) || (F_GT  == oper) || (F_LE == oper)
                   || (F_LT  == oper) || (F_AND == oper) || (F_OR == oper)
                   || (F_XOR == oper) || (F_IFF == oper) );
          }

static bool  isIntegerOp (NodeType  oper)
          {
            return(   (F_NEG == oper) || (F_ABS == oper) || (F_ADD == oper)
                   || (F_SUB == oper) || (F_MUL == oper) || (F_DIV == oper)
                   || (F_MOD == oper) || (F_POW == oper) || (F_MIN == oper)
                   || (F_MAX == oper) || (F_IF  == oper) );
          }


string getName( AST const & dVar)
{
  string ret;

  if ( dVar.isVar() )
     ret = dVar.getVarName();
  else if ( dVar.isInteger() )
   {
     ret = to_string(dVar.getInteger());
   }
  else if (dVar.isOperator()) {

  } else {
     throw std::runtime_error("getName type error");
  }

  return(ret);
}

string manageOperator (const AST & oper) {
	switch (oper.getType()) {
		case F_EQ: return("==");
		case F_NE:return("!=");
		case F_GE:return(">=");
		case F_GT:return(">");
		case F_LE:return("<=");
		case F_LT:return("<");
		case SYMB_EQ: return("==");
		case SYMB_NE:return("!=");
		case SYMB_GE:return(">=");
		case SYMB_GT:return(">");
		case SYMB_LE:return("<=");
		case SYMB_LT:return("<");
		default:
			throw std::runtime_error("operator not supported");
	}
    return("");
}


string manageBoolExpr (const AST & expr);

string manageIntExpr (const AST & expr) {
	string ret = "";
	if ( expr.isInteger() )
		ret = to_string(expr.getInteger());
    else if ( expr.isVar() )
        ret = expr.getVarName();
    else if ( expr.isOperator() ) {
    	ASTAbstractFunction const  & aF = dynamic_cast<ASTAbstractFunction const &>(expr);

        NodeType  oper(aF.getType());

        if ( false == isIntegerOp(oper) )
						throw std::runtime_error("integer operator failure (" + to_string(oper) + ")");

        switch ( oper ) {
        	case F_ABS:
            	ret = "abs(";
            	ret.append( manageIntExpr(aF.getArg(0)) );
            	ret.append(")");
                break;

            case F_NEG:
               ret = "-";
               ret.append( manageIntExpr(aF.getArg(0)) );
               break;

            case F_MIN:
               ret = "min(";
               ret.append( manageIntExpr(aF.getArg(0)) );
               ret.append(",");
               ret.append( manageIntExpr(aF.getArg(1)) );
               ret.append(")");
               break;

            case F_MAX:
               ret = "max(";
               ret.append( manageIntExpr(aF.getArg(0)) );
               ret.append(",");
               ret.append( manageIntExpr(aF.getArg(1)) );
               ret.append(")");
               break;

            case F_MOD:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" mod ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_POW:
                ret = "pow(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(",");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_ADD:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" + ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_SUB:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" - ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_MUL:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" * ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_DIV:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" div ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_IF:
                ret = "(bool2int(";
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(") * ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(" + bool2int(not(");
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(")) * ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            default:
               throw std::runtime_error("unexpected operator dealing with integer expression");
               break;
          }

    } else
     throw std::runtime_error("unexpected AST integer expression");

	return(ret);
}


string manageBoolExpr (const AST & expr) {
	string ret = "";

    if ( expr.isBoolean() )
      ret = to_string(expr.getBoolean());
    else if ( expr.isVar() )
      throw std::runtime_error("unexpected boolean variable");
    else if ( expr.isOperator() ) {
    	ASTAbstractFunction const  & aF
            = dynamic_cast<ASTAbstractFunction const &>(expr);

        NodeType  oper(aF.getType());

        if ( false == isBooleanOp(oper) )
            throw std::runtime_error("boolean operator failure");

         switch ( oper )
          {
            case F_EQ:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" == ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_NE:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" != ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_GE:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" >= ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_GT:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" > ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_LE:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" <= ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_LT:
                ret = "(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(" < ");
                ret.append( manageIntExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_AND:
                ret = "(";
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(" /\\ ");
                ret.append( manageBoolExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_OR:
                ret = "(";
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(" \\/ ");
                ret.append( manageBoolExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_XOR:
                ret = "(";
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(" xor ");
                ret.append( manageBoolExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            case F_NEG:
                ret = "not(";
                ret.append( manageIntExpr(aF.getArg(0)) );
                ret.append(")");
                break;

            case F_IFF:
                ret = "(";
                ret.append( manageBoolExpr(aF.getArg(0)) );
                ret.append(" <-> ");
                ret.append( manageBoolExpr(aF.getArg(1)) );
                ret.append(")");
                break;

            default:
               throw std::runtime_error("unexpected operator dealing with boolean expression");
               break;
          }
       }
      else
         throw std::runtime_error("unexpected AST boolean expression");
     return(ret);
}


#endif /* AST_MAPPING_HH_ */
