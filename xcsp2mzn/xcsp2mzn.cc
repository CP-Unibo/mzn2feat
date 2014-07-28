#include <xcsp-parser/XMLParser_libxml2.hh>
#include "AST_mapping.hh"

using namespace CSPXMLParser;

/*
 * The program to convert XCSP instances into MiniZinc instances
 */

class XCSPConverter : public CSPParserCallback
{
private:
  bool firstDomainValue;
  bool firstTuple;

  string name;
  std::vector<std::string>  varNames;
  bool firstValue;
  CSPDefinitionType type;


public:
  virtual void beginInstance(const string & name)
  {
    cout << "% Processing instance<instance>" << endl;
    cout << "include \"table.mzn\";" << endl;
    cout << "include \"cumulative.mzn\";"<< endl;
    cout << "include \"disjunctive.mzn\";"<< endl;
    cout << "include \"element.mzn\";"<< endl;
    cout << "include \"alldifferent.mzn\";"<< endl;
  }

  virtual void beginDomainsSection(int nbDomains)
  {
    cout << "% Start processing domains" << endl;
  }

  virtual void beginDomain(const string & name, int idDomain, int nbValue)
  {
      if ( nbValue <= 0 )
         throw std::runtime_error("domain with illegal num values");

      firstValue = true;
      cout << "set of int: " << name << " = ";
  }

  virtual void addDomainValue(int v)
  {
	  if (firstValue) {
		  cout << "{" << v << "}";
		  firstValue = false;
	  } else {
		  cout << " union {" << v << "}";
	  }
  }

  virtual void addDomainValue(int first,int last)
  {
    if ( first > last )
      throw std::runtime_error("illegal domain range");
    if (firstValue) {
    	cout << " " << first << ".." << last;
    	firstValue = false;
  	} else {
  		cout << " union " << first << ".." << last;
  	}
  }

  virtual void endDomain()
  {
    cout << ";" << endl;
  }

  /**
   * end the definition of all domains
   */
  virtual void endDomainsSection()
  {
    cout << "% Domains processed" <<endl;
  }


  virtual void beginVariablesSection(int nbVariables)
  {
    cout << "% Start processing variables" <<endl;
  }

  virtual void addVariable(const string & name, int idVar,
			   const string & domain, int idDomain)
  {
    cout << "var " << domain << ": " << name << ";" << endl;
    varNames.push_back(name);
  }

  virtual void endVariablesSection()
  {
    cout << "% Vars processed" <<endl;
  }


  virtual void beginRelationsSection(int nbRelations)
  {
    cout << "% Start processing relations" <<endl;
  }


  virtual void beginRelation(const string & name, int idRel,
			     int arity, int nbTuples, RelType relType)
  {
    this->name = name;
    if (nbTuples == 0)
    	throw std::runtime_error("relation with 0 tuples not supported");

    cout << "predicate rel_" << name << "( var int: x0";
    for (int i=1;i<arity;i++)
    {
    	cout << ", var int:x" << i;
    }
    cout << ") = ";
    if (relType == REL_CONFLICT)
    	cout << "not(";
    cout << "table([x0";
    for (int i=1;i<arity;i++)
    {
    	cout << ",x" << i;
    }
    cout << "], table_" << name << ")";
    if (relType == REL_CONFLICT)
    	cout << ")";
    cout << ";" << endl;

    cout << "array[1.." << nbTuples << ",1.." << arity << "] of int: table_" << name << ";" << endl;
    cout << "table_" << name << " = [";

  }

  virtual void addRelationTuple(int arity, int tuple[])
  {
	cout << '|';

    cout << tuple[0];
    for(int i=1;i<arity;++i)
      cout << ',' << tuple[i];
  }

  virtual void addRelationTuple(int arity, int tuple[], int cost)
  {
	  throw std::runtime_error("cost in relation not supported");
  }

  virtual void endRelation()
  {
    cout << "|];" << endl;
  }

  virtual void endRelationsSection()
  {
    cout << "% Relation processed" <<endl;
  }

  virtual void beginPredicatesSection(int nbPredicates)
  {
    cout << "%Processing predicates" << endl;
  }

  virtual void beginPredicate(const string & name, int idPred)
  {
    this-> name = name;
    cout << "predicate pred_" << name << "(";
  }

  virtual void addFormalParameter(int pos, const string & name,
				  const string & type)
  {
    if (type != "int")
    	throw std::runtime_error("non int parameters in predicates not supported");
    if (pos == 0)
    	cout << "var int: " << name;
    else
    	cout << ", var int: " << name;
  }

  virtual void predicateExpression(AST *tree)
  {
	  cout << ") = " << manageBoolExpr(*tree) << ";" << endl;
  }


  virtual void predicateExpression(const string &expr)
  {
	  throw std::runtime_error("predicateExpression(const string &expr) not supported");
  }


  virtual void endPredicate() { }

  virtual void endPredicatesSection()
  {
    cout << "% Predicates processed" << endl;
  }

  virtual void beginConstraintsSection(int nbConstraints)
  {
    cout << "% Processing constrains" << endl;
  }

  virtual void beginConstraint(const string & name, int idConstr,
			       int arity,
			       const string & reference,
			       CSPDefinitionType type, int id,
			       const ASTList &scope)
  {
	  this->type = type;
	  this->name = reference;
  }

  virtual void constraintParameters(const ASTList &args)
  {
    switch ( type )
      {
      	  case RelationType:
      		  cout << "constraint rel_" << name << "(" << getName(args[0]);
      		  for (int j=1;j<args.size();j++)
      			  cout << "," << getName(args[j]);
      		  cout << ");" << endl;
      		  break;
      	  case PredicateType:
      	      cout << "constraint pred_" << name << "(" << getName(args[0]);
      	      for (int j=1;j<args.size();j++)
      	      	  cout << "," << getName(args[j]);
      	      cout << ");" << endl;
      	      break;
      	  default:
      		// handle global constraints
      		if (name=="global:element") {
      			if ( 3 != args.nbArg() )
      				throw std::runtime_error("element args cardinality error");

      		    AST const  & index(args[0]);
      		    AST const  & list(args[1]);
      		    AST const  & value(args[2]);

      		    if ( false == list.isList() )
      		    	throw std::runtime_error("element arg 2 error");

      		    cout << "constraint element(" << getName(index) << ", [" << getName(list[0]);
      		    for (int i=1; i<list.size();i++)
      		    	cout << ", " << getName(list[i]);
      		    cout << "], " << getName(value) << ");" << endl;
      		}
      		else if (name=="global:weightedsum") {
      			const AST &sum=args[0];
      		    const AST &op=args[1];
      		    const AST &rhs=args[2];

      		    cout << "constraint sum( [";

      		    cout << getName(sum[0]["coef"]) << " * " << getName(sum[0]["var"]);

      		    for(int i=1;i<sum.size();i++)
      		    	cout << ", " << getName(sum[i]["coef"]) << " * " << getName(sum[i]["var"]);

      		    cout << "] ) " << manageOperator(op) << " " << getName(rhs) << ";" << endl;
      		}
      		else if (name=="global:alldifferent") {
      	      // problem: in the "allDifferent" case, arguments can be directly in
      	      // 'args' (old deprecated syntax?) or in the ASTList in 'args[0]' (new
      	      // syntax?); we manage this with the following hack
      	      ASTList const & aList(
      	         dynamic_cast<ASTList const &>(
      	            ((1==args.nbArg()) && args[0].isList()) ? args[0] : args ));
      	      cout << "constraint alldifferent( [ " << getName(aList[0]);
      	      for ( int i=1 ; i < aList.nbArg() ; i++ ) {
      	    	  cout << ", " << getName(aList[i]);
      	      }
      	      cout << "] );" << endl;
      		}
      		else if (name=="global:cumulative") {
      			AST const  & tasks(args[0]);
      			AST const  & limit(args[1]);

      			vector<string> iVAOrigin;
      			vector<string> iVADuration;
      			vector<string> iVAEnd;
      			vector<string> iVAHeight;


      			if ( false == tasks.isList() )
      				 throw std::runtime_error("cumulative arg 1 error");

      			if ( false == limit.isInteger() )
      				 throw std::runtime_error("cumulative arg 2 error");

      			int const numTsk(tasks.nbArg());
      			int const limVal(limit.getInteger());

      			enum { noOrigin, noDuration, noEnd, full}  hasCase;

      			// restriction (f)
      			if ( 0 > limVal )
      				 throw std::runtime_error("cumulative restriction (f) error");

      			for ( int i=0 ; i < numTsk ; ++i )
      			{
      				 ASTDict const  & aD
      				 	 = dynamic_cast<ASTDict const &>(tasks[i]);

      				 // XCSP 2.1 specifications: "one attribute among {origin, duration,
      				 // end} may be missing" (pag. 27), so...
      				 if ( false == aD.hasKey("origin") )
      				 {
      					 hasCase = noOrigin;
      					 // no "origin", so "duration" and "end" are mandatory and
      					 // "origin := end - duration" (restriction (a) satisfied or
      					 // exception)
      					 iVADuration.push_back(getName(aD["duration"]));
      					 iVAEnd.push_back(getName(aD["end"]));
      					 string s = iVAEnd[i];
      					 s.append(" - ");
      					 s.append(iVADuration[i]);

      					 iVAOrigin.push_back(s);
      				 }
      				 else if ( false == aD.hasKey("duration") )
      				 {
      					 hasCase = noDuration;

      					// no "duration", so "origin" and "end" are mandatory and
      					// "duration := end - origin" (restriction (a) satisfied or
      					// exception)
      					 iVAOrigin.push_back(getName(aD["origin"]));
      					 iVAEnd.push_back(getName(aD["end"]));
      					 string s = iVAEnd[i];
      					 s.append(" - ");
      					 s.append(iVAOrigin[i]);
      					 iVADuration.push_back(s);
      				 }
      				 else if ( false == aD.hasKey("end") )
      				 {
      					hasCase = noEnd;
      					// no "end", so "origin" and "duration" are mandatory and
      					// "end := origin + duration" (restriction (a) satisfied or
      					// exception)
      					iVAOrigin.push_back(getName(aD["origin"]));
      					iVADuration.push_back(getName(aD["duration"]));
      					string s = iVADuration[i];
      					s.append(" + ");
      					s.append(iVAOrigin[i]);
      					iVAEnd.push_back(s);
      				 }
      				 else
      				 {
      					hasCase = full;

      					// we have "origin", "duration" and "end"; we must impose
      					// the constraint "end = origin + duration" (Gecode don't
      					// test this in comulative() and comulatives()) (restriction
      					// (a) satisfied)
      					iVAOrigin.push_back(getName(aD["origin"]));
      					iVADuration.push_back(getName(aD["duration"]));
      					iVAEnd.push_back(getName(aD["end"]));

      				 }

      				 // "height" is mandatory (restriction (b) satisfied or exception)
      				 iVAHeight.push_back(getName(aD["height"]));

					 // for each task we have (and we must, according to the case,
					 // impose) the following restrictions:
					 // (c) duration >= 0 (all cases)
					 // (e) height >= 0   (all cases)
					 // (d) origin <= end (only case full; superflous otherwise (obvious
					 //     if origin or end is calculated (with duration >=0); derive
					 //     from (c) when duration in calculated))
      		         cout << "constraint " << iVADuration[i] << " >= 0;" << endl;
      		         cout << "constraint " << iVAHeight[i] << " >= 0;" << endl;

      		         if ( full == hasCase )
      		        	cout << "constraint " << iVAOrigin[i] << " <= " << iVAEnd[i] << ";" << endl;
      			 }
 		         cout << "constraint cumulative( [" << iVAOrigin[0];
 		         for (int i=1; i < numTsk; i++) {
 		        	 cout << ", " << iVAOrigin[i];
 		         }
 		         cout << "], [" << iVADuration[0];
 		         for (int i=1; i < numTsk; i++) {
 		        	 cout << ", " << iVADuration[i];
 		         }
 		         cout << "], [" << iVAHeight[0];
 		         for (int i=1; i < numTsk; i++) {
 		        	 cout << ", " << iVAHeight[i];
 		         }
 		         cout << "], " << limVal << ");" << endl;
      		}
      		else {
      			// default
      			string s = "constraint ";
      			s.append(name);
      			s.append(" not supported");
      		    throw std::runtime_error(s);
      		}
    		break;
      }

  }


  virtual void endConstraint()
  {

  }

  /**
   * end the definition of all constraints
   */
  virtual void endConstraintsSection()
  {
    cout << "% Constraints processed" <<endl;
  }

  /********************************************************************/


  /**
   * signal the end of parsing
   */
  virtual void endInstance()
  {
    cout << "% Instance processed" <<endl;
    cout << "solve :: int_search( [ " << varNames[0];
    for (unsigned int i=1; i<varNames.size();i++){
    	cout << ", " << varNames[i];
    }
    cout << "], first_fail, indomain_min, complete) satisfy;" << endl;

    cout << "output [ \"" << varNames[0] << " = \", show(" << varNames[0] << "), \"\\n\"";
    for (unsigned int i=1; i<varNames.size();i++){
    	cout << ", \"" << varNames[i] << " = \", show(" << varNames[i] << "), \"\\n\"";
    }
    cout << "];" << endl;
  }

};




int main(int argc, char **argv)
{
	XCSPConverter cb;

  if (argc < 2)
  {
    cout << "syntax: " << argv[0] << " CSPFile.xml\n"
	 << "  This program converts the CSPFile.xml into a MiniZinc instance\n"
	 << endl;
    exit(1);
  }

  char* filename = argv[1];
  if (fopen(filename, "r") == NULL) {
    fprintf(stderr, "cannot open file: '%s'\n", filename);
    exit(1);
  }
  
  try
  {
    XMLParser_libxml2<> parser(cb);

    parser.parse(argv[1]); // parse the input file
  }
  catch (exception &e)
  {
    cout.flush();
    cerr << "\n\tUnexpected exception :\n";
    cerr << "\t" << e.what() << endl;
    exit(1);
  }

  return 0;
}
