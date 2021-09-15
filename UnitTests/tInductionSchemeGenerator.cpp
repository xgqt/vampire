/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Shell/InductionSchemeGenerator.hpp"

using namespace Shell;

#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_SORT(s)                                                                             \
  DECL_SKOLEM_CONST(sk1,s)                                                                 \
  DECL_SKOLEM_CONST(sk2,s)                                                                 \
  DECL_SKOLEM_CONST(sk3,s)                                                                 \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s, s}, s)                                                                  \
  DECL_PRED(p, {s, s})                                                                     \
  NUMBER_SUGAR(Int)                                                                        \
  DECL_PRED(pi, {Int})                                                                     \
  DECL_SKOLEM_CONST(sk4, Int) 

void checkOccurrenceMap(vvector<pair<InductionScheme, OccurrenceMap>> res,
  vvector<vvector<pair<TermSugar, vmap<Literal*, uint64_t>>>> c)
{
  for (auto v : c) {
    InductionTerms indTerms;
    for (unsigned i = 0; i < v.size(); i++) {
      indTerms.insert(make_pair(v[i].first.toTerm().term(), i));
    }
    auto it = res.begin();
    for (; it != res.end(); it++) {
      if (indTerms == it->first.inductionTerms()) {
        for (auto kv : v) {
          auto t = kv.first.toTerm().term();
          for (auto kv2 : kv.second) {
            auto it2 = it->second._m.find(make_pair(kv2.first, t));
            ASS(it2 != it->second._m.end());
            const auto bits = it2->second.num_bits();
            auto bv = kv2.second;
            for (uint64_t i = 0; i < bits; i++) {
              ASS_EQ(it2->second.pop_last(), bv & 1);
              bv >>= 1;
            }
            ASS(!bv);
            it->second._m.erase(it2);
          }
        }
        ASS(it->second._m.empty());
        break;
      }
    }
    ASS(it != res.end());
    res.erase(it);
  }
  ASS(res.empty());
}

TEST_FUN(test_01) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  SET_OPTIONS({ { "induction_on_complex_terms", "on" } })
  // we only need to mark the active positions here, the rest will be added by InductionPreprocessor
  DECL_FUNC_DEFS({ { clause({ f(x, r(y)) == g(f(x,y),b) }),                     0, false },   \
                   { clause({ ~p(x,r(y)), p(x,y) }),                            0, false },   \
                   { clause({ g(r(x),y) == g(x,r(y)) }),                        0, false } })
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(f.functor(), true));
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(g.functor(), true));
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(p.functor(), false));

  RecursionInductionSchemeGenerator gen;
  // active positions
  //             1 0 0 0   0    0    1 0   1 0   1
  auto mainLit = p(f(f(sk1,sk2),sk3),f(sk3,f(sk1,sk2)));
  //             1 0   1 0   1        1 1   1
  auto sideLit = f(sk3,f(sk1,sk2)) == g(sk2,sk3);
  InductionPremise mainPremise(mainLit, clause({ mainLit, p(x,x) }));
  InductionPremises premises(mainPremise);
  premises.addSidePremise(sideLit, clause({ sideLit, b != b }));

  vvector<pair<InductionScheme, OccurrenceMap>> res;
  gen.generate(premises, res);

  // these occurrence bit vectors are to be read right-to-left
  checkOccurrenceMap(res, {
    { { sk2, { { mainLit, 0b10 },
               { sideLit, 0b11 } } } },

    { { sk2, { { mainLit, 0b10 },
               { sideLit, 0b11 } } },
      { sk3, { { mainLit, 0b00 },
               { sideLit, 0b10 } } } },

    { { f(sk1,sk2), { { mainLit, 0b10 },
                      { sideLit, 0b1 } } } },

    { { f(sk3,f(sk1,sk2)), { { mainLit, 0b1 },
                             { sideLit, 0b1 } } } },
  });
}

// exhaustive generaton option
TEST_FUN(test_02) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  SET_OPTIONS({ { "induction_on_complex_terms", "on" },
                { "induction_on_complex_terms_heuristic", "off" },
                { "induction_exhaustive_generation", "on" } })
  // we only need to mark the active positions here, the rest will be added by InductionPreprocessor
  DECL_FUNC_DEFS({ { clause({ ~p(r(x),r(y)), p(x,y) }), 0, false } })
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(p.functor(), false));

  RecursionInductionSchemeGenerator gen;
  auto mainLit = p(f(r(sk1),sk2),f(sk3,r(sk3)));
  InductionPremise mainPremise(mainLit, clause({ mainLit, p(x,x) }));
  InductionPremises premises(mainPremise);

  vvector<pair<InductionScheme, OccurrenceMap>> res;
  gen.generate(premises, res);

  // these occurrence bit vectors are to be read right-to-left
  checkOccurrenceMap(res, {
    { { sk1, { { mainLit, 1 } } }, { sk3, { { mainLit, 0b11 } } } },

    { { sk1, { { mainLit, 1 } } }, { r(sk3), { { mainLit, 1 } } } },

    { { sk1, { { mainLit, 1 } } }, { f(sk3,r(sk3)), { { mainLit, 1 } } } },

    { { sk2, { { mainLit, 1 } } }, { sk3, { { mainLit, 0b11 } } } },

    { { sk2, { { mainLit, 1 } } }, { r(sk3), { { mainLit, 1 } } } },

    { { sk2, { { mainLit, 1 } } }, { f(sk3,r(sk3)), { { mainLit, 1 } } } },

    { { r(sk1), { { mainLit, 1 } } }, { sk3, { { mainLit, 0b11 } } } },

    { { r(sk1), { { mainLit, 1 } } }, { r(sk3), { { mainLit, 1 } } } },

    { { r(sk1), { { mainLit, 1 } } }, { f(sk3,r(sk3)), { { mainLit, 1 } } } },

    { { f(r(sk1),sk2), { { mainLit, 1 } } }, { sk3, { { mainLit, 0b11 } } } },

    { { f(r(sk1),sk2), { { mainLit, 1 } } }, { r(sk3), { { mainLit, 1 } } } },

    { { f(r(sk1),sk2), { { mainLit, 1 } } }, { f(sk3,r(sk3)), { { mainLit, 1 } } } },
  });
}

// main literal doesn't contain induction term
TEST_FUN(test_03) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  // we only need to mark the active positions here, the rest will be added by InductionPreprocessor
  DECL_FUNC_DEFS({ { clause({ ~p(r(x),r(y)), p(x,y) }), 0, false } })
  ASS(env.signature->getFnDefHandler()->hasInductionTemplate(p.functor(), false));

  RecursionInductionSchemeGenerator gen;
  auto lit1 = sk1 != sk1;
  auto lit2 = p(sk2,sk3);
  InductionPremise mainPremise1(lit1, clause({ lit1 }));
  InductionPremises premises1(mainPremise1);
  premises1.addSidePremise(lit2, clause({ lit2 }));

  vvector<pair<InductionScheme, OccurrenceMap>> res;
  gen.generate(premises1, res);

  // empty result
  checkOccurrenceMap(res, { });

  // swapping the two clauses results in scheme
  InductionPremise mainPremise2(lit2, clause({ lit2 }));
  InductionPremises premises2(mainPremise2);
  premises2.addSidePremise(lit1, clause({ lit1 }));

  gen.generate(premises2, res);

  checkOccurrenceMap(res, {
    { { sk2, { { lit2, 1 } } }, { sk3, { { lit2, 1 } } } },
  });
}

// complex terms are induction upon
TEST_FUN(test_04) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  SET_OPTIONS({ { "induction_on_complex_terms", "on" } })

  StructuralInductionSchemeGenerator gen;
  auto mainLit = p(f(f(sk1,sk2),sk3),f(sk3,f(sk1,sk2)));
  auto sideLit = f(sk3,f(sk1,sk2)) == g(sk2,sk3);
  InductionPremise mainPremise(mainLit, clause({ mainLit, p(x,x) }));
  InductionPremises premises(mainPremise);
  premises.addSidePremise(sideLit, clause({ sideLit, b != b }));

  vvector<pair<InductionScheme, OccurrenceMap>> res;
  gen.generate(premises, res);

  checkOccurrenceMap(res, {
    { { sk1, { { mainLit, 0 },
               { sideLit, 0  } } } },

    { { sk2, { { mainLit, 0 },
               { sideLit, 0 } } } },

    { { sk3, { { mainLit, 0 },
               { sideLit, 0 } } } },

    { { f(sk1,sk2), { { mainLit, 0 },
                      { sideLit, 0 } } } },

    { { f(f(sk1,sk2),sk3), { { mainLit, 0 } } } },

    { { f(sk3,f(sk1,sk2)), { { mainLit, 0 },
                             { sideLit, 0 } } } },

  });
}

// side literal should be made into bound with active occurrence
TEST_FUN(test_05) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR)
  SET_OPTIONS({ { "induction", "int" }, { "int_induction_interval", "infinite" } })

  IntegerInductionSchemeGenerator gen;
  auto lit1 = ~pi(sk4);
  auto lit2 = ~(sk4 < num(1));
  InductionPremise mainPremise1(lit1, clause({ lit1 }), /*originalPremise=*/true);
  InductionPremises premises1(mainPremise1);
  premises1.addSidePremise(lit2, clause({ lit2 }));

  vvector<pair<InductionScheme, OccurrenceMap>> res;
  gen.generate(premises1, res);

  checkOccurrenceMap(res, {
    { { sk4, { { lit1, 0 }, { lit2, 1 } } } },
  });

  // swapping the two clauses does not result in a scheme, since lit2
  // is not a valid induction literal
  res.clear();
  InductionPremise mainPremise2(lit2, clause({ lit2 }));
  InductionPremises premises2(mainPremise2);
  premises2.addSidePremise(lit1, clause({ lit1 }), /*originalPremise=*/true);

  gen.generate(premises2, res);

  checkOccurrenceMap(res, { });
}
