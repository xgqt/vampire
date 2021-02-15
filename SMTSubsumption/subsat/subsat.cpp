#include "subsat.hpp"

#include <initializer_list>
#include <iostream>

using namespace SMTSubsumption;

#ifdef SUBSAT_STANDALONE

Clause* make_clause(std::initializer_list<Lit> literals)
{
  Clause* cl = Clause::create(literals.size());
  for (size_t i = 0; i < literals.size(); ++i) {
    (*cl)[i] = literals.begin()[i];
  }
  return cl;
}

void add_clause(Solver& solver, std::initializer_list<Lit> literals)
{
  solver.add_clause(make_clause(literals));
}

int main()
{
    std::cout << "hello" << std::endl;

    Solver s;
    Var x = s.new_variable();
    Var y = s.new_variable();
    Var z = s.new_variable();

    s.add_clause(make_clause({x, y, z}));
    s.add_clause(make_clause({x, y, ~z}));
    s.add_clause(make_clause({x, ~y, z}));
    s.add_clause(make_clause({x, ~y, ~z}));
    s.add_clause(make_clause({~x, y, z}));
    s.add_clause(make_clause({~x, y, ~z}));
    s.add_clause(make_clause({~x, ~y, z}));
    s.add_clause(make_clause({~x, ~y, ~z}));

    auto res = s.solve();

    std::cout << "Result: " << res << std::endl;

    return 0;
}
#endif



#ifndef NDEBUG
bool Solver::checkInvariants() const
{
  // assigned vars + unassiged vars = used vars
  assert(m_trail.size() + m_unassigned_vars == m_used_vars);

  assert(m_values.size() == 2 * m_used_vars);

  // m_unassigned_values is correct
  assert(std::count(m_values.begin(), m_values.end(), Value::Unassigned) == 2 * m_unassigned_vars);

  // Opposite literals have opposite values
  for (uint32_t var_idx = 0; var_idx < m_used_vars; ++var_idx) {
    Var x{var_idx};
    assert(m_values[x] == ~m_values[~x]);
  }

  // Every variable is at most once on the trail
  std::set<Var> trail_vars;
  for (Lit lit : m_trail) {
    assert(lit.is_valid());
    auto [_, inserted] = trail_vars.insert(lit.var());
    assert(inserted);
  }
  assert(trail_vars.size() == m_trail.size());
  assert(m_trail.size() <= m_used_vars);

  // Check clause invariants
  for (Clause const* clause : m_clauses) {
    // Every stored clause has size >= 2
    // TODO: after binary clause optimization: >= 3
    assert(clause->size() >= 2);
    // No duplicate variables in the clause (this prevents duplicate literals and tautological clauses)
    std::set<Var> clause_vars;
    for (Lit lit : *clause) {
      assert(lit.is_valid());
      auto [_, inserted] = clause_vars.insert(lit.var());
      assert(inserted);
    }
    assert(clause_vars.size() == clause->size());
  }

  // Check watch invariants
  assert(m_watches.size() == 2 * m_used_vars);
  std::map<ClauseRef, int> num_watches; // counts how many times each clause is watched
  for (uint32_t lit_idx = 0; lit_idx < m_watches.size(); ++lit_idx) {
    Lit const lit = Lit::from_index(lit_idx);
    for (Watch watch : m_watches[lit]) {
      num_watches[watch.clause] += 1;
      Clause const& clause = get_clause(watch.clause);
      // The watched literals are always the first two in the clause
      assert(clause[0] == lit || clause[1] == lit);
      // Check status of watch literals
      // TODO: this holds only after propagation (obviously); so maybe we should make it a separate check.
      bool clause_satisfied =
        std::any_of(clause.begin(), clause.end(), [this](auto l){ return m_values[l] == Value::True; });
      if (clause_satisfied) {
        Level min_true_level = std::numeric_limits<Level>::max();
        for (Lit l : clause) {
          if (m_values[l] == Value::True && get_level(l) < min_true_level) {
            min_true_level = get_level(l);
          }
        }
        // If the clause is satisfied, one of the watches must be on the same level or above
        // at least one of the true literals.
        // Even stronger in our code: one of the watches is on the same level. (TODO: true?)
        assert(get_level(clause[0]) == min_true_level || get_level(clause[1]) == min_true_level);
      } else {
        // If the clause is not satisfied, either both watch literals must be unassigned,
        // or all literals are false (conflict).
        bool both_watches_unassigned =
          m_values[clause[0]] == Value::Unassigned && m_values[clause[1]] == Value::Unassigned;
        bool is_conflict =
          std::all_of(clause.begin(), clause.end(), [this](auto l) { return m_values[l] == Value::False; });
        CDEBUG("BLAH");
        for (Lit l: clause) {
          CDEBUG("Literal " << l << " has value " << m_values[l]);
        }
        assert(both_watches_unassigned || is_conflict);
      }
    }
  }
  // Every clause in m_clauses is watched twice
  for (ClauseRef cr = 0; cr < m_clauses.size(); ++cr) {
    assert(num_watches[cr] == 2);
  }

  return true;
}
#endif
