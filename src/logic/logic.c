#include "logic.h"
#include "cvc5/c/cvc5.h"
#include <assert.h>
#include <cvc5/c/cvc5_parser.h>
#include <stdio.h>
#include <stdlib.h>

Cvc5TermManager *l_tm;
Cvc5SymbolManager *l_symbols;
char cvc5_input_buffer[1024];

void logic_init() {
  l_tm = cvc5_term_manager_new();
  l_symbols = cvc5_symbol_manager_new(l_tm);
}

void logic_setup_symbols() {
  Cvc5 *solver = cvc5_new(l_tm);
  Cvc5InputParser *parser = cvc5_parser_new(solver, l_symbols);

  cvc5_set_logic(solver, CVC5_LOGIC);

  cvc5_parser_set_str_input(
      parser,
      CVC5_LANG,
      "(declare-sort Anima 0)"
      "(declare-sort Direction 0)"

      "(declare-const gottlob Anima)"
      "(declare-const bertrand Anima)"
      "(declare-const a Anima)"

      "(declare-const up    Direction)"
      "(declare-const right Direction)"
      "(declare-const down  Direction)"
      "(declare-const left  Direction)",

      "setup_symbols");

  do {
    cvc5_cmd = cvc5_parser_next_command(parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, solver, l_symbols);
    }
  } while (cvc5_cmd);

  cvc5_parser_delete(parser);
  cvc5_delete(solver);
};

void logic_setup_foundation(Cvc5 *cvc5, Cvc5InputParser *parser) {
  cvc5_parser_set_str_input(
      parser,
      CVC5_LANG,

      "(assert (distinct up right down left))"

      "(declare-fun is_facing (Anima Direction) Bool)",

      "setup_foundation");

  do {
    cvc5_cmd = cvc5_parser_next_command(parser, &cvc5_error_msg);
    if (cvc5_error_msg) {
      printf("%s", cvc5_error_msg), exit(-1);
    }
    if (cvc5_cmd) {
      cvc5_cmd_invoke(cvc5_cmd, cvc5, l_symbols);
    }
  } while (cvc5_cmd);
};
