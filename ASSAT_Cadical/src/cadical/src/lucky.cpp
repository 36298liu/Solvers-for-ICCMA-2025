#include "internal.hpp"

namespace CaDiCaL {

// It turns out that even in the competition there are formulas which are
// easy to satisfy by either setting all variables to the same truth value
// or by assigning variables to the same value and propagating it.  In the
// latter situation this can be done either in the order of all variables
// (forward or backward) or in the order of all clauses.  These lucky
// assignments can be tested initially in a kind of pre-solving step.

// This function factors out clean up code common among the 'lucky'
// functions for backtracking and resetting a potential conflict.  One could
// also use exceptions here, but there are two different reasons for
// aborting early.  The first kind of aborting is due to asynchronous
// termination and the second kind due to a situation in which it is clear
// that a particular function will not be successful (for instance a
// completely negative clause is found).  The latter situation returns zero
// and will just abort the particular lucky function, while the former will
// abort all (by returning '-1').

int Internal::unlucky (int res) {
  if (level > 0)
    backtrack ();
  if (conflict)
    conflict = 0;
  return res;
}

int Internal::trivially_false_satisfiable () {
  LOG ("checking that all clauses contain a negative literal");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false, found_negative_literal = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      found_negative_literal = true;
      break;
    }
    if (satisfied || found_negative_literal)
      continue;
    LOG (c, "found purely positively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a negative literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky.constant.zero++;
  return 10;
}

int Internal::trivially_true_satisfiable () {
  LOG ("checking that all clauses contain a positive literal");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto &c : clauses) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    bool satisfied = false, found_positive_literal = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      found_positive_literal = true;
      break;
    }
    if (satisfied || found_positive_literal)
      continue;
    LOG (c, "found purely negatively");
    return unlucky (0);
  }
  VERBOSE (1, "all clauses contain a positive literal");
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (propagate ())
      continue;
    assert (level > 0);
    LOG ("propagation failed including redundant clauses");
    return unlucky (0);
  }
  stats.lucky.constant.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::forward_false_satisfiable () {
  LOG ("checking increasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  for (auto idx : vars) {
    if (terminated_asynchronously (100))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (!propagate ())
      return unlucky (0);
  }
  VERBOSE (1, "forward assuming variables false satisfies formula");
  assert (satisfied ());
  stats.lucky.forward.zero++;
  return 10;
}

int Internal::forward_true_satisfiable () {
  LOG ("checking increasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (!propagate ())
      return unlucky (0);
  }
  VERBOSE (1, "forward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.forward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::backward_false_satisfiable () {
  LOG ("checking decreasing variable index false assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  for (int idx = max_var; idx > 0; idx--) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (!propagate ())
      return unlucky (0);
  }
  VERBOSE (1, "backward assuming variables false satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.zero++;
  return 10;
}

int Internal::backward_true_satisfiable () {
  LOG ("checking decreasing variable index true assignment");
  assert (!unsat);
  assert (!level);
  assert (assumptions.empty ());
  for (int idx = max_var; idx > 0; idx--) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (!propagate ())
      return unlucky (0);
  }
  VERBOSE (1, "backward assuming variables true satisfies formula");
  assert (satisfied ());
  stats.lucky.backward.one++;
  return 10;
}

/*------------------------------------------------------------------------*/

// The following two functions test if the formula is a satisfiable horn
// formula.  Actually the test is slightly more general.  It goes over all
// clauses and assigns the first positive literal to true and propagates.
// Already satisfied clauses are of course skipped.  A reverse function
// is not implemented yet.

int Internal::positive_horn_satisfiable () {
  LOG ("checking that all clauses are positive horn satisfiable");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int positive_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit < 0)
        continue;
      positive_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!positive_literal) {
      LOG (c, "no positive unassigned literal in");
      return unlucky (0);
    }
    assert (positive_literal > 0);
    LOG (c, "found positive literal %d in", positive_literal);
    search_assume_decision (positive_literal);
    if (propagate ())
      continue;
    LOG ("propagation of positive literal %d leads to conflict",
         positive_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (-idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", -idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are positive horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.positive++;
  return 10;
}

int Internal::negative_horn_satisfiable () {
  LOG ("checking that all clauses are negative horn satisfiable");
  assert (!level);
  assert (assumptions.empty ());
  for (const auto &c : clauses) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (c->garbage)
      continue;
    if (c->redundant)
      continue;
    int negative_literal = 0;
    bool satisfied = false;
    for (const auto &lit : *c) {
      const signed char tmp = val (lit);
      if (tmp > 0) {
        satisfied = true;
        break;
      }
      if (tmp < 0)
        continue;
      if (lit > 0)
        continue;
      negative_literal = lit;
      break;
    }
    if (satisfied)
      continue;
    if (!negative_literal) {
      if (level > 0)
        backtrack ();
      LOG (c, "no negative unassigned literal in");
      return unlucky (0);
    }
    assert (negative_literal < 0);
    LOG (c, "found negative literal %d in", negative_literal);
    search_assume_decision (negative_literal);
    if (propagate ())
      continue;
    LOG ("propagation of negative literal %d leads to conflict",
         negative_literal);
    return unlucky (0);
  }
  for (auto idx : vars) {
    if (terminated_asynchronously (10))
      return unlucky (-1);
    if (val (idx))
      continue;
    search_assume_decision (idx);
    if (propagate ())
      continue;
    LOG ("propagation of remaining literal %d leads to conflict", idx);
    return unlucky (0);
  }
  VERBOSE (1, "clauses are negative horn satisfied");
  assert (!conflict);
  assert (satisfied ());
  stats.lucky.horn.negative++;
  return 10;
}

/*------------------------------------------------------------------------*/

int Internal::lucky_phases () {
  assert (!level);
  require_mode (SEARCH);
  if (!opts.lucky)
    return 0;

  // TODO: Some of the lucky assignments can also be found if there are
  // assumptions, but this is not completely implemented nor tested yet.
  // Nothing done for constraint either.
  // External propagator assumes a CDCL loop, so lucky is not tried here.
  if (!assumptions.empty () || !constraint.empty () || external_prop)
    return 0;

  START (search);
  START (lucky);
  assert (!searching_lucky_phases);
  searching_lucky_phases = true;
  stats.lucky.tried++;
  int res = trivially_false_satisfiable ();
  if (!res)
    res = trivially_true_satisfiable ();
  if (!res)
    res = forward_true_satisfiable ();
  if (!res)
    res = forward_false_satisfiable ();
  if (!res)
    res = backward_false_satisfiable ();
  if (!res)
    res = backward_true_satisfiable ();
  if (!res)
    res = positive_horn_satisfiable ();
  if (!res)
    res = negative_horn_satisfiable ();
  if (res < 0)
    assert (termination_forced), res = 0;
  if (res == 10)
    stats.lucky.succeeded++;
  // report ('l', !res);
  assert (searching_lucky_phases);
  searching_lucky_phases = false;
  STOP (lucky);
  STOP (search);

  return res;
}

} // namespace CaDiCaL
