grammar edu:umn:cs:melt:lambdacalc:strategy_attributes;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:lambdacalc:concretesyntax;
imports edu:umn:cs:melt:lambdacalc:abstractsyntax;

fun main IO<Integer> ::= args::[String] = do {
  if length(args) != 1 then do {
    print("Usage: java -jar strategy_attributes.jar [file name]\n");
    return 1;
  } else do {
    let fileName :: String = head(args);
    isF::Boolean <- isFile(fileName);
    if !isF then do {
      print("File \"" ++ fileName ++ "\" not found.\n");
      return 2;
    } else do {
      text :: String <- readFile(fileName);
      let result :: ParseResult<Term_c> = parse(text, fileName);
      if !result.parseSuccess then do {
        print(result.parseErrors ++ "\n");
        return 3;
      } else do {
        let ast::Term = result.parseTree.ast;
        print(show(80, ast.pp) ++ "\n\n");
        print(show(80, evaluate(ast).pp) ++ "\n");
        return 0;
      };
    };
  };
};
