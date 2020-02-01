grammar edu:umn:cs:melt:lambdacalc:abstractsyntax;

imports silver:rewrite;

-- Rewrite rules from Stratego tutorial slides
-- http://ftp.strategoxt.org/pub/stratego/archive/doc/TutorialSlides.ps

-- Alpha reduction with explicit substitution

global alpha::Strategy =
  rule on Term of
  | abs(x, e) -> let y::String = freshVar() in abs(y, letT(x, var(y), e)) end
  end;

-- Beta reduction with explicit substitution
global beta::Strategy =
  rule on Term of
  | app(abs(x, e1), e2) -> letT(x, e2, e1)
  end;

-- Eta reduction
global eta::Strategy =
  rule on Term of
  | abs(x, app(e, var(y)))
    when x == y &&!containsBy(stringEq, x, e.freeVars) -> e
  end;

-- Let distribution
global letVar::Strategy =
  rule on Term of
  | letT(x, e, var(y)) when x == y -> e
  | letT(x, e, var(y)) -> var(y)
  end;

global letApp::Strategy =
  rule on Term of
  | letT(x, e0, app(e1, e2)) -> app(letT(x, e0, e1), letT(x, e0, e2))
  end;

global letAbs::Strategy =
  rule on Term of
  | letT(x, e1, abs(y, e2)) when x == y -> abs(y, e2)
  | letT(x, e1, abs(y, e2)) ->
    let z::String = freshVar() in abs(z, letT(x, e1, letT(y, var(z), e2))) end
  end;

-- Let optimization
global letEta::Strategy =
  rule on Term of
  | letT(x, e, e1) when !containsBy(stringEq, x, e1.freeVars) -> e1
  end;

global letId::Strategy =
  rule on Term of
  | letT(x, var(y), e) when x == y -> e
  end;

global letDown::Strategy =
  rule on Term of
  | letT(x, letT(y, e1, e2), e3) ->
    let z::String = freshVar() in
      letT(z, e1, letT(x, letT(y, var(z), e2), e3))
    end
  end;

global letUp::Strategy =
  rule on Term of
  | letT(x, e1, letT(y, e2, e3)) ->
    let z::String = freshVar() in
      letT(z, letT(x, e1, letT(y, var(z), e2)),
              letT(x, e1, letT(y, var(z), e3)))
    end
  end;

-- Strong normal form: all function applications have been reduced
global isSNF::Strategy =
  rec(\ x::Strategy ->
    traverse abs(_, x) <+ traverse var(_) <+
    rec(\ y::Strategy -> traverse app(y, x) <+ traverse var(_)));

-- Full call-by-value: evaluate all arguments before substitution, reduce under
-- abstractions. (innermost through entire expression)
global fullCallByValue::Strategy = innermost(beta <+ letVar <+ letApp <+ letAbs);

-- Strong head-normal form: all function applications have been reduced, except
-- those under abstractions
global isSHNF::Strategy =
  rec(\ x::Strategy ->
    traverse abs(_, _) <+ traverse var(_) <+
    rec(\ y::Strategy -> traverse app(y, x) <+ traverse var(_)));

-- Call-by-value: evaluate all applications, but not under abstraction
-- (innermost, except for abstractions)
global callByValue::Strategy =
  rec(\ x::Strategy ->
    (traverse app(x, x) <+ traverse letT(_, x, x) <+ traverse var(_) <+ traverse abs(_, _)) <*
    try((beta <+ letVar <+ letApp <+ letAbs) <* x));

-- Weak head-normal form: all function applications have been reduced, except
-- those under abstractions and in arguments to functions
global isWHNF :: Strategy =
  rec(\ x::Strategy ->
    traverse abs(_, _) <+ traverse var(_) <+
    rec(\ y::Strategy -> traverse app(y, _) <+ traverse var(_)));

-- Call-by-name: don't evaluate function arguments and let-bound abstractions
global callByName::Strategy =
  rec(\ x::Strategy ->
    (traverse app(x, _) <+ traverse letT(_, _, x) <+ traverse var(_) <+ traverse abs(_, _)) <*
    try((beta <+ letVar <+ letApp <+ letAbs) <* x));

-- Lazy evaluation: don't distribute let bound expressions over applications or
-- lets unless they are evaluated (i.e., no duplication of computations.) A let
-- bound expression is forced when it is needed in an application.
{-
global lazyEval::Strategy =
  rec(\ x::Strategy ->
    (traverse app(x, _) <+ traverse letT(_, _, x) <+ traverse var(_) <+ traverse abs(_, _)) <*
    try((beta <+ letVar <+ letAbs <+
         (traverse Let(_, traverse Abs(_, _), _) <* (letApp <+ letUp)) <+
         forceLet(x)) <* x));
-}

global printCurrentTerm::Strategy =
  rule on Term of
  | t -> unsafeTrace(t, print(show(80, t.pp) ++ "\n", unsafeIO()))
  end;

global normalize::Strategy = fullCallByValue;

function norm
Term ::= t::Term
{
  return
    case rewriteWith(normalize, new(t)) of
    | just(t1) -> t1
    | nothing() -> error("Rewriting failed")
    end;
}

function freshVar
String ::=
{
  return "a" ++ toString(genInt());
}
