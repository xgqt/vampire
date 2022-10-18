/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "SATSubsumption/SATSubsumptionResolution.hpp"
#include "SATSubsumption/Util.hpp"
#include "Kernel/Inference.hpp"

using namespace std;
using namespace SMTSubsumption;
using namespace Test;

#define SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION \
__ALLOW_UNUSED(                        \
    DECL_DEFAULT_VARS                  \
    DECL_VAR(x1,1)                     \
    DECL_VAR(x2,2)                     \
    DECL_VAR(x3,3)                     \
    DECL_VAR(x4,4)                     \
    DECL_VAR(x5,5)                     \
    DECL_VAR(y1,11)                    \
    DECL_VAR(y2,12)                    \
    DECL_VAR(y3,13)                    \
    DECL_VAR(y4,14)                    \
    DECL_VAR(y5,15)                    \
    DECL_SORT(s)                       \
    DECL_CONST(c, s)                   \
    DECL_CONST(d, s)                   \
    DECL_CONST(e, s)                   \
    DECL_FUNC(f, {s}, s)               \
    DECL_FUNC(f2, {s, s}, s)           \
    DECL_FUNC(g, {s}, s)               \
    DECL_FUNC(g2, {s, s}, s)           \
    DECL_PRED(p, {s})                  \
    DECL_PRED(p2, {s, s})              \
    DECL_PRED(p3, {s, s, s})           \
    DECL_PRED(q, {s})                  \
    DECL_PRED(q2, {s, s})              \
    DECL_PRED(r, {s})                  \
  )

static bool vectorContains(vvector<SATSubsumption::Match*> vec, SATSubsumption::Match* match)
{
    for (auto m : vec) {
        if (m == match) {
            return true;
        }
    }
    return false;
}

static void checkConsistency(SATSubsumption::MatchSet *matchSet, vvector<SATSubsumption::Match*> matches)
{
    ASS(matchSet->getAllMatches().size() == matches.size());
    for (auto match : matches) {
        ASS(vectorContains(matchSet->getIMatches(match->_i), match));
        ASS(vectorContains(matchSet->getJMatches(match->_j), match));
        ASS(matchSet->getMatchForVar(match->_var) == match);
        ASS(vectorContains(matchSet->getAllMatches(), match));
    }
}

TEST_FUN(MatcheSetIndexing)
{
  SATSubsumption::MatchSet *matchSet = new SATSubsumption::MatchSet(3, 3);
  vvector<SATSubsumption::Match*> matches;
  SATSubsumption::Match* match1 = matchSet->addMatch(0, 0, true, subsat::Var(0));
  SATSubsumption::Match* match2 = matchSet->addMatch(2, 1, true, subsat::Var(1));
  SATSubsumption::Match* match3 = matchSet->addMatch(2, 2, true, subsat::Var(2));

  ASS(match1);
  ASS(match2);
  ASS(match3);
  ASS(match1 != match2);
  ASS(match2 != match3);
  ASS(match3 != match1);

  matches.push_back(match1);
  matches.push_back(match2);
  matches.push_back(match3);

    // Check that the matches are in the correct indices
    checkConsistency(matchSet, matches);
    delete matchSet;
    matches.clear();
}

static void checkStateI(SATSubsumption::MatchSet *matchSet, unsigned i, bool positive, bool negative)
{
    if (positive != matchSet->hasPositiveMatchI(i)) {
        cerr << "Positive match for I " << i << " should be " << positive << endl;
    } else if(negative != matchSet->hasNegativeMatchI(i)) {
        cerr << "Negative match for I " << i << " should be " << negative << endl;
    } else {
        return;
    } ASS(false);
}

static void checkStateJ(SATSubsumption::MatchSet *matchSet, unsigned j, bool positive, bool negative)
{
    if (positive != matchSet->hasPositiveMatchJ(j)) {
        cerr << "Positive match for J " << j << " should be " << positive << endl;
    } else if(negative != matchSet->hasNegativeMatchJ(j)) {
        cerr << "Negative match for J " << j << " should be " << negative << endl;
    } else {
        return;
    } ASS(false);
}


TEST_FUN(TestSetBitTricks)
{
    unsigned n = 3;
    unsigned m = 5;
    vvector<bool> iInserted(n, false);
    vvector<bool> jInserted(m, false);
    SATSubsumption::MatchSet *matchSet = new SATSubsumption::MatchSet(n, m);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            matchSet->addMatch(i, j, true, subsat::Var(0));

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(matchSet,k, iInserted[k], false);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(matchSet,k, jInserted[k], false);
            }
        }
    }
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            matchSet->addMatch(i, j, false, subsat::Var(0));

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(matchSet,k, true, iInserted[k]);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(matchSet,k, true, jInserted[k]);
            }
        }
    }
    matchSet->clear();
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            matchSet->addMatch(i, j, false, subsat::Var(0));

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(matchSet,k, false, iInserted[k]);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(matchSet,k, false, jInserted[k]);
            }
        }
    }
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            matchSet->addMatch(i, j, true, subsat::Var(0));

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(matchSet,k, iInserted[k], true);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(matchSet,k, jInserted[k], true);
            }
        }
    }
}

TEST_FUN(PositiveSubsumption) {
    __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    Kernel::Clause* L1 = clause({ p3(x1, x2, x3), p3(f(x2), x4, x4)});
    Kernel::Clause* M1 = clause({ p3(f(c), d, y1), p3(f(d), c, c)});
    Kernel::Clause* M2 = clause({ p3(f(c), d, y1), p3(f(d), c, c), r(x1)});
    Kernel::Clause* L3 = clause({ p(f2(f(g(x1)),x1)), c == g(x1)});
    Kernel::Clause* M3 = clause({ g(y1) == c, p(f2(f(g(y1)),y1))});
    Kernel::Clause* L4 = clause({ f2(x1,x2) == c, ~p2(x1,x3), p2(f(f2(x1,x2)),f(x3))});
    Kernel::Clause* M4 = clause({ c == f2(x3,y2), ~p2(x3,y1), p2(f(f2(x3,y2)),f(y1))});
    Kernel::Clause* L5 = clause({ p(f2(f(e), g2(x4, x3))), p2(f2(f(e), g2(x4, x3)), x3), f(e)==g2(x4, x3)});
    Kernel::Clause* M5 = clause({ p(f2(f(e), g2(y1, y3))), p2(f2(f(e), g2(y1, y3)), y3), f(e)==g2(y1, y3)});
    ASS(L1);
    ASS(M1);
    SATSubsumption subsumption;
    ASS(subsumption.checkSubsumption(L1, M1));
    ASS(subsumption.checkSubsumption(L1, M2));
    ASS(subsumption.checkSubsumption(L3, M3));
    ASS(subsumption.checkSubsumption(L4, M4));
    ASS(subsumption.checkSubsumption(L5, M5));

}

TEST_FUN(NegativeSubsumption) {
    __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    Kernel::Clause* L1 = clause({p2(f2(g2(x1, x2), x3), x3),
                                 p2(f2(g2(x1, x2), x3), x2),
                                 g2(x1, x2) == x3});
    Kernel::Clause* M1 = clause({p2(f2(g2(y1, y2), y2), y2),
                                 g2(y1, y2) == y2,
                                 ~p2(f2(g2(y1, y2), y2), g2(y1, y2))});
    Kernel::Clause* L2 = clause({~p2(x1,x2),
                                 p(x1)});
    Kernel::Clause* M2 = clause({p(y1),
                                 ~p(f(f2(f2(y2,y2),f2(y2,y3)))),
                                 ~p(y3),
                                 ~p(y2)});
    ASS(L1);
    ASS(M1);
    ASS(L2);
    ASS(M2);
    SATSubsumption subsumption;
    ASS(!subsumption.checkSubsumption(L1, M1));
    ASS(!subsumption.checkSubsumption(L2, M2));

    Kernel::Clause* L6 = clause({p2(y5, f(f2(c, x1))), ~p(c), ~p(y5)});
    Kernel::Clause* M6 = clause({~q(f(d)), p2(c, f(f2(c, x4))), r(e), ~p(c), d==g(c)});
    ASS(!subsumption.checkSubsumption(L6, M6));
    Kernel::Clause* L7 = clause({p2(y5, f(f2(x1, c))), ~p(c), ~p(y5)});
    Kernel::Clause* M7 = clause({~q(d), p2(c, f(f2(x4, c))), r(d), ~p(c), d==g(c)});
    ASS(!subsumption.checkSubsumption(L7, M7));
}

/**
 * Check that the subsumption resolution works for positive instances
 */
TEST_FUN(PositiveSubsumptionResolution)
{
    __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    Kernel::Clause* L = clause({ ~p(x1), q(x1)});
    Kernel::Clause* M = clause({ p(c), q(c), r(e)});

    Kernel::Clause* L2 = clause({ p2(x1, x2), p2(f(x2), x3)});
    Kernel::Clause* M2 = clause({ ~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e)});
    // Create the expected conclusion
    Kernel::Clause* expected = clause({ q(c), r(e)});
    Kernel::Clause* expected2 = clause({ ~p2(f(y1), d), p2(g(y1), c)});
    // checks
    ASS(L);
    ASS(M);
    ASS(expected);


    SATSubsumption subsumption;

    // Check that the resolution is correct
    Kernel::Clause *conclusion = subsumption.checkSubsumptionResolution(L, M);
    ASS(conclusion)
    ASS(checkClauseEquality(conclusion, expected));
    Kernel::Clause *conclusion2 = subsumption.checkSubsumptionResolution(L2, M2);
    ASS(conclusion2)
    ASS(checkClauseEquality(conclusion2, expected2));

}

TEST_FUN(NegativeSubsumptionResolution)
{
    __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    // Create the the L clause
    Kernel::Clause* L1 = clause({ ~p(x1), q(x1)});
    Kernel::Clause* L2 = clause({ ~p(x1), ~q(x2)});
    Kernel::Clause* L3 = clause({ ~p(x1), r(c)});
    Kernel::Clause* L4 = clause({ ~p(x1), p2(x1, x2)});
    // Create the M clause
    Kernel::Clause* M1 = clause({ p(c), q(d), r(e)});
    // checks
    ASS(L1);
    ASS(M1);

    SATSubsumption subsumption;
    Kernel::Clause *conclusion = subsumption.checkSubsumptionResolution(L1, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L2, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L3, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L4, M1);
    ASS(!conclusion)
}
