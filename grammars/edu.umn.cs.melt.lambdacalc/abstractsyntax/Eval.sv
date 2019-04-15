grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

imports core hiding all;

imports silver:reflect;
imports silver:term;

-- Rewrite rules from Stratego tutorial slides
-- http://ftp.strategoxt.org/pub/stratego/archive/doc/TutorialSlides.ps

-- Alpha reduction with explicit substitution
global alpha::Strategy =
  directFreshRule(
    AST {edu:umn:cs:melt:lambdacalc:abstractsyntax:abs(x, e, location=l)},
    ["y"],
    AST {edu:umn:cs:melt:lambdacalc:abstractsyntax:abs(y, edu:umn:cs:melt:lambdacalc:abstractsyntax:letT(x, var(y), e))});
  
-- Beta reduction with explicit substitution
global beta::Strategy =
  directRule(
    AST {edu:umn:cs:melt:lambdacalc:abstractsyntax:app(edu:umn:cs:melt:lambdacalc:abstractsyntax:abs(x, e1, location=_), e2, location=_)},
    AST {edu:umn:cs:melt:lambdacalc:abstractsyntax:letT(x, e1, e2, location=txtLoc("beta"))});

-- Eta reduction
global eta::Strategy =
  rule(
    AST {edu:umn:cs:melt:lambdacalc:abstractsyntax:abs(x, edu:umn:cs:melt:lambdacalc:abstractsyntax:app(e, edu:umn:cs:melt:lambdacalc:abstractsyntax:var(x)))},
    \ s::[Sub] ->
      let x::String = reify(getSub("x", s)).fromRight,
          e::Term = reify(getSub("e", s)).fromRight
      in !containsBy(stringEq, x, e.freeVars)
      end,
    [], AST {e});

-- Let distribution
global letVar::Strategy =
  choice(
    directRule(AST {letT(x, e, var(x))}, AST {e}),
    directRule(AST {letT(_, _, var(y))}, AST {var(y)}));

global letApp::Strategy =
  directRule(AST {letT(x, e0, app(e1, e2))}, AST {app(letT(x, e0, e1, letT(x, e0, e2)))});

global letAbs::Strategy =
  choice(
    directRule(AST {letT(x, e1, abs(x, e2))}, AST {abs(x, e2)}),
    directRule(AST {letT(_, _, abs(x, e2))}, AST {var(y)}));

-- Let optimization
global letEta::Strategy =
  rule(
    AST {let(x, e1, e2)},
    \ s::[Sub] ->
      let x::String = reify(getSub("x", s)).fromRight,
          e2::Term = reify(getSub("e2", s)).fromRight
      in !containsBy(stringEq, x, e2.freeVars)
      end,
    [], AST {e2});

global letId::Strategy = directRule(AST {letT(x, e, var(x))}, AST {e});

global letDown::Strategy =
  directFreshRule(
    AST {letT(x, letT(y, e1, e2), e3)},
    ["z"],
    AST {letT(z, e1, letT(x, letT(y, var(z), e2), e3))});

global letUp::Strategy =
  directFreshRule(
    AST {letT(x, letT(y, e1, e2), e3)},
    ["z"],
    AST {letT(z, letT(x, e1, letT(y, var(z), e2)), letT(x, e1, letT(y, var(z), e3)))});

global normalize::Strategy = beta;

function norm
Term ::= t::Term
{
  return
    case reify(rewrite(normalize, reflect(new(t))).fromJust) of
    | left(m) -> error("Reification error in norm: " ++ m)
    | right(a) -> a
    end;
}
