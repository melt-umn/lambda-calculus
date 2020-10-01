grammar edu:umn:cs:melt:lambdacalc:concretesyntax;

imports silver:langutil;
imports edu:umn:cs:melt:lambdacalc:abstractsyntax;

parser parse::Term_c {
  edu:umn:cs:melt:lambdacalc:concretesyntax;
}

ignore terminal WhiteSpace_t /[\n\r\t\ ]+/;
ignore terminal Comment_t /#.*/;

terminal Identifier_t /[A-Za-z_]+/;
terminal Lambda_t '\';
terminal Dot_t '.' precedence=0;
terminal App_t '' precedence=1, association=left;
terminal LParen_t '(';
terminal RParen_t ')';

nonterminal Term_c with ast<Term>;

concrete productions top::Term_c
| '\' ids::Identifiers_c '.' t::Term_c
  { top.ast = ids.ast(t.ast); }
| t1::Term_c App_t t2::Term_c
  { top.ast = app(t1.ast, t2.ast); }
| id::Identifier_t
  { top.ast = var(id.lexeme); }
| '(' t::Term_c ')'
  { top.ast = t.ast; }

nonterminal Identifiers_c with ast<(Term ::= Term)>;

concrete productions top::Identifiers_c
| h::Identifier_t t::Identifiers_c
  { top.ast = \ b::Term -> abs(h.lexeme, t.ast(b)); }
| h::Identifier_t
  { top.ast = abs(h.lexeme, _); }
