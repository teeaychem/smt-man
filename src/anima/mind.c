#include "anima.h"

Mind Mind_default() {

  Cvc5TermManager *tm = cvc5_term_manager_new();
  Cvc5SymbolManager *symbols = cvc5_symbol_manager_new(tm);
  Cvc5 *solver = cvc5_new(tm);
  Cvc5InputParser *parser = cvc5_parser_new(solver, symbols);

  cvc5_set_logic(solver, CVC5_LOGIC);

  cvc5_set_option(solver, "produce-models", "true");
  cvc5_set_option(solver, "finite-model-find", "true");
  cvc5_set_option(solver, "model-var-elim-uneval", "false");
  cvc5_set_option(solver, "print-success", "true");

  Mind mind = {
      .parser = parser,
      .sm = symbols,
      .solver = solver,
      .tm = tm,
      .terms = {},
  };

  return mind;
}
