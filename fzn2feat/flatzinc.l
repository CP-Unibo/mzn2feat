/* Lexer for FlatZinc.
 * Nick Nethercote, started May 2007.
 *
 * This file is in the public domain, and can be used without copyright
 * restrictions.
 */

%{
#include <string.h>
%}

    /* Regular expressions for attributed tokens. */
ident           	[A-Za-z][A-Za-z0-9_]*
underscore_ident	_*[A-Za-z][A-Za-z0-9_]*
string_literal  	\"[^"\n]*\"
int_literal     	-?[0-9]+|-?0x[0-9A-Fa-f]+|-?0o[0-7]+
float_literal   	-?[0-9]+\.[0-9]+|-?[0-9]+\.[0-9]+[Ee][-+]?[0-9]+|-?[0-9]+[Ee][-+]?[0-9]+

%%

    /* Reserved words */
"array"         { return ARRAY;     }
"bool"          { return BOOL;      }
"constraint"    { return CONSTRAINT;}
"false"         { return FALSE;     }
"float"         { return FLOAT;     }
"int"           { return INT;       }
"minimize"      { return MINIMIZE;  }
"maximize"      { return MAXIMIZE;  }
"of"            { return OF;        }
"satisfy"       { return SATISFY;   }
"set"           { return SET;       }
"solve"         { return SOLVE;     }
"true"          { return TRUE;      }
"var"           { return VAR;       }

\.\.            { return DOTDOT;    }
::              { return COLONCOLON;}

    /* Attributed tokens */
{ident} { 
        yylval.string_val = strdup(yytext);  
        return IDENT; 
    }
{underscore_ident} {
	yylval.string_val = strdup(yytext);
	return UNDERSCORE_IDENT;
}
{string_literal} { 
        yylval.string_val = strdup(yytext);  
        return STRING_LITERAL; 
    }
{int_literal} {
        /*
	** atoi() doesn't recognise our hex and octal numbers, so we must
	** handle them ourselves.
        **
        ** XXX: this code doesn't detect if the integer literals overflow an
        ** 'int'.  (In particular, 'atoi' doesn't detect overflow errors,
        ** but 'strtol' does, so that could be used for the decimal integer
        ** case.)
        ** 
        ** XXX: I think this code will incorrectly parse negative octal and
        ** hexadecimal numbers -- the two conditions will fail due to the
        ** leading '-', so 'atoi' will be invoked, which will fail, and
        ** yylval.int_val will be set to something bogus (probably zero).
	*/
        if        ('0' == yytext[0] && 'x' == yytext[1])  {
            int i = 2, x = 0;
            while ('\0' != yytext[i]) {
                x *= 16;
                if ('0' <= yytext[i] && yytext[i] <= '9') {
                    x += (yytext[i] - '0');
                } else {
                    x += (yytext[i] - 'a' + 10);
                }
                i++;
            }
            yylval.int_val = x;

        } else if ('0' == yytext[0] && 'o' == yytext[1])  {
            int i = 2, x = 0;
            while ('\0' != yytext[i]) {
                x *= 8;
                x += (yytext[i] - '0');
                i++;
            }
            yylval.int_val = x;

        } else {
            yylval.int_val = atoi(yytext);
        }
        return INT_LITERAL; 
    }
{float_literal} {
        yylval.float_val = atof(yytext);
        return FLOAT_LITERAL; 
    }

    /* Skip newlines, whitespace, comments and predicates 
     * return any non-matched character. */
\n          ;
[ \t]       ;
%.*         ;
predicate.* ; // Predicates were been removed (Roberto Amadini).
.           { return yytext[0]; }

%%

