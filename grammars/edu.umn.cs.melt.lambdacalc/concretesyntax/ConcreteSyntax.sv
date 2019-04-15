grammar edu:umn:cs:melt:lambdacalc:concretesyntax;

imports silver:langutil;
imports edu:umn:cs:melt:lambdacalc:abstractsyntax;

ignore terminal WhiteSpace_t /[\n\r\t\ ]+/;

terminal Identifier_t /[A-Za-z_\$][A-Za-z_0-9\$]*/;
terminal Lambda_t '\';
terminal Dot_t '.';
terminal LParen_t '(';
terminal RParen_t ')';

nonterminal Term_c with ast<Term>, location;

concrete productions top::Term_c
| '\' ids::Identifiers_c '.' t::Term_c
  { top.ast = ids.ast(t.ast); }
| t1::AppliedTerm_c t2::Term_c
  { top.ast = app(t1.ast, t2.ast, location=top.location); }
| t::AppliedTerm_c
  { top.ast = t.ast; }

nonterminal AppliedTerm_c with ast<Term>, location;

concrete productions top::AppliedTerm_c
| id::Identifier_t
  { top.ast = var(id.lexeme, location=top.location); }
| '(' t::Term_c ')'
  { top.ast = t.ast; }

nonterminal Identifiers_c with ast<(Term ::= Term)>, location;

concrete productions top::Identifiers_c
| h::Identifier_t t::Identifiers_c
  { top.ast = \ b::Term -> abs(h.lexeme, t.ast(b), location=h.location); }
| h::Identifier_t
  { top.ast = abs(h.lexeme, _, location=h.location); }
