#include <cvc5/cvc5.h>
#include <iostream>

using namespace cvc5;

int main(int argc, char **agrv) {
  std::cout << "Hello, all" << "\n";

  TermManager tm;

  Solver solver(tm);
  solver.setOption("produce-models", "true");
  solver.setOption("finite-model-find", "true");

  Sort animaSort = tm.mkUninterpretedSort("Anima");
  Sort animaPredicate = tm.mkFunctionSort({animaSort}, tm.getBooleanSort());
  Sort directionSort = tm.mkUninterpretedSort("Direction");

  Sort facingSort = tm.mkFunctionSort({animaSort, directionSort}, tm.getBooleanSort());
  Term facingFn = tm.mkConst(facingSort, "Facing");

  Term blinky = tm.mkConst(animaSort, "blinky");

  Term up = tm.mkConst(directionSort, "up");
  Term right = tm.mkConst(directionSort, "right");
  Term down = tm.mkConst(directionSort, "down");
  Term left = tm.mkConst(directionSort, "left");

  auto bu = tm.mkTerm(Kind::APPLY_UF, {facingFn, blinky, up});
  auto br = tm.mkTerm(Kind::APPLY_UF, {facingFn, blinky, right});
  auto bd = tm.mkTerm(Kind::APPLY_UF, {facingFn, blinky, down});
  auto bl = tm.mkTerm(Kind::APPLY_UF, {facingFn, blinky, left});

  Term some_direction = tm.mkTerm(Kind::OR, {bu, br, bd, bl});
  Term u_case = tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {bu}),
                                     tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::OR, {br, bd, bl})})});
  Term r_case = tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {br}),
                                     tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::OR, {bu, bd, bl})})});
  Term d_case = tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {bd}),
                                     tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::OR, {bu, br, bl})})});
  Term l_case = tm.mkTerm(Kind::OR, {tm.mkTerm(Kind::NOT, {bd}),
                                     tm.mkTerm(Kind::NOT, {tm.mkTerm(Kind::OR, {bu, br, bd})})});

  Term exactly_one_direction = tm.mkTerm(Kind::AND, {some_direction, u_case, r_case, d_case, l_case});

  solver.assertFormula(exactly_one_direction);
  solver.assertFormula(tm.mkTerm(Kind::NOT, {bu}));

  Term helloworld = tm.mkConst(tm.getBooleanSort(), "Hello World!");

  solver.checkSat();

  std::cout << solver.getValue(bu) << " "
            << solver.getValue(br) << " "
            << solver.getValue(bd) << " "
            << solver.getValue(bl);

  return 0;
}
