#include "internal.hpp"

namespace CaDiCaL {

// This function determines the next decision variable on the queue, without
// actually removing it from the decision queue, e.g., calling it multiple
// times without any assignment will return the same result.  This is of
// course used below in 'decide' but also in 'reuse_trail' to determine the
// largest decision level to backtrack to during 'restart' without changing
// the assigned variables (if 'opts.restartreusetrail' is non-zero).

//从决策队列中选择一个未赋值的变元
int Internal::next_decision_variable_on_queue () {
  int64_t searched = 0;
  int res = queue.unassigned;
  while (val (res))
    res = link (res).prev, searched++;
  if (searched) {
    stats.searched += searched;
    update_queue_unassigned (res);
  }
  LOG ("next queue decision variable %d bumped %" PRId64 "", res,
       bumped (res));
  return res;
}

// This function determines the best decision with respect to score.
//选择得分最高的未赋值变元
int Internal::next_decision_variable_with_best_score () {
  int res = 0;
  for (;;) {
    res = scores.front ();
    if (!val (res))
      break;
    (void) scores.pop_front ();
  }
  LOG ("next decision variable %d with score %g", res, score (res));
  return res;
}

//选择是第一种策略还是第二种策略
int Internal::next_decision_variable () {
  if (use_scores ())
    return next_decision_variable_with_best_score ();
  else
    return next_decision_variable_on_queue ();
}

/*------------------------------------------------------------------------*/

// Implements phase saving as well using a target phase during
// stabilization unless decision phase is forced to the initial value
// of a phase is forced through the 'phase' option.

int Internal::decide_phase (int idx, bool target) {
  const int initial_phase = opts.phase ? 1 : -1;
  int phase = 0;
  if (force_saved_phase)
    phase = phases.saved[idx];
  if (!phase)
    phase = phases.forced[idx]; // swapped with opts.forcephase case!
  if (!phase && opts.forcephase)
    phase = initial_phase;
  if (!phase && target)
    phase = phases.target[idx];
  if (!phase)
    phase = phases.saved[idx];

  // The following should not be necessary and in some version we had even
  // a hard 'COVER' assertion here to check for this.   Unfortunately it
  // triggered for some users and we could not get to the root cause of
  // 'phase' still not being set here.  The logic for phase and target
  // saving is pretty complex, particularly in combination with local
  // search, and to avoid running in such an issue in the future again, we
  // now use this 'defensive' code here, even though such defensive code is
  // considered bad programming practice.
  //
  if (!phase)
    phase = initial_phase;

  return phase * idx;
}

// The likely phase of an variable used in 'collect' for optimizing
// co-location of clauses likely accessed together during search.

int Internal::likely_phase (int idx) { return decide_phase (idx, false); }

/*------------------------------------------------------------------------*/

// adds new level to control and trail
//
void Internal::new_trail_level (int lit) {
  level++;
  control.push_back (Level (lit, trail.size ()));
}

/*------------------------------------------------------------------------*/

bool Internal::satisfied () {
  if ((size_t) level < assumptions.size () + (!!constraint.size ()))
    return false;
  if (num_assigned < (size_t) max_var)
    return false;
  assert (num_assigned == (size_t) max_var);
  if (propagated < trail.size ())
    return false;
  size_t assigned = num_assigned;
  return (assigned == (size_t) max_var);
}

bool Internal::better_decision (int lit, int other) {
  int lit_idx = abs (lit);
  int other_idx = abs (other);
  if (stable)
    return stab[lit_idx] > stab[other_idx];
  else
    return btab[lit_idx] > btab[other_idx];
}

// Search for the next decision and assign it to the saved phase.  Requires
// that not all variables are assigned.

int Internal::decide () {
  //先确保未满足
  assert (!satisfied ());
  START (decide);
  int res = 0;
  if ((size_t) level < assumptions.size ()) {
    //if ((size_t) level < assumptions.size()):
    //检查当前决策层级是否小于假设集合 assumptions 的大小。
    //如果是，则意味着当前决策由预设假设驱动，而非动态分支选择
    const int lit = assumptions[level];
    assert (assumed (lit));
    const signed char tmp = val (lit);
    if (tmp < 0) {
      LOG ("assumption %d falsified", lit);
      //如果假设文字被判定为假，标记不可满足
      res = 20;
    } else if (tmp > 0) {
      LOG ("assumption %d already satisfied", lit);
      new_trail_level (0);
      LOG ("added pseudo decision level");
      //如果假设文字已经满足，记录日志并创建一个伪决策层级
      notify_decision ();
    } else {
      LOG ("deciding assumption %d", lit);
      //如果假设文字未赋值，记录日志并执行假设决策
      search_assume_decision (lit);
    }
  } else if ((size_t) level == assumptions.size () && constraint.size ()) {
    //如果当前层级已处理完所有假设，且约束集合 constraint 非空，则进入约束处理逻辑

    //满足约束的文字。
    int satisfied_lit = 0;  // The literal satisfying the constrain.
    //未赋值且得分最高的文字
    int unassigned_lit = 0; // Highest score unassigned literal.
    //上一个文字，用于调整约束顺序
    int previous_lit = 0;   // Move satisfied literals to the front.

    const size_t size_constraint = constraint.size ();

#ifndef NDEBUG
    unsigned sum = 0;
    for (auto lit : constraint)
      sum += lit;
#endif
    //遍历约束中的文字
    //遍历 constraint 中的每个文字 lit：
    //调整约束顺序，将 previous_lit 移动到前面。
    //根据 tmp 值（赋值状态）：
    //若为假，跳过继续下一文字。
    //若为真，记录该文字 satisfied_lit。
    //若未赋值，更新最高得分未赋值文字 unassigned_lit。
    for (size_t i = 0; i != size_constraint; i++) {

      // Get literal and move 'constraint[i] = constraint[i-1]'.

      int lit = constraint[i];
      constraint[i] = previous_lit;
      previous_lit = lit;

      const signed char tmp = val (lit);
      if (tmp < 0) {
        LOG ("constraint literal %d falsified", lit);
        continue;
      }

      if (tmp > 0) {
        LOG ("constraint literal %d satisfied", lit);
        satisfied_lit = lit;
        break;
      }

      assert (!tmp);
      LOG ("constraint literal %d unassigned", lit);

      if (!unassigned_lit || better_decision (lit, unassigned_lit))
        unassigned_lit = lit;
    }

    //根据约束处理结果决策
    //若 satisfied_lit 非零，则标记为满足，并更新伪决策层级。
    //否则，如果有 unassigned_lit，对其做假设决策。
    //若无法找到合适文字，则标记约束失败并返回 20。
    if (satisfied_lit) {

      constraint[0] = satisfied_lit; // Move satisfied to the front.

      LOG ("literal %d satisfies constraint and "
           "is implied by assumptions",
           satisfied_lit);

      new_trail_level (0);
      LOG ("added pseudo decision level for constraint");
      notify_decision ();

    } else {

      // Just move all the literals back.  If we found an unsatisfied
      // literal then it will be satisfied (most likely) at the next
      // decision and moved then to the first position.

      if (size_constraint) {

        for (size_t i = 0; i + 1 != size_constraint; i++)
          constraint[i] = constraint[i + 1];

        constraint[size_constraint - 1] = previous_lit;
      }

      if (unassigned_lit) {

        LOG ("deciding %d to satisfy constraint", unassigned_lit);
        search_assume_decision (unassigned_lit);

      } else {

        LOG ("failing constraint");
        unsat_constraint = true;
        res = 20;
      }
    }

#ifndef NDEBUG
    for (auto lit : constraint)
      sum -= lit;
    assert (!sum); // Checksum of literal should not change!
#endif

  } else {
    //动态决策和回溯
    //如果没有假设或约束，进入动态决策阶段，选择一个变量进行分支。
    //若发生回溯条件，则递归调用 decide()。
    //统计决策次数，获取下一个决策变量并假设其值。
    int decision = ask_decision ();
    if ((size_t) level < assumptions.size () ||
        ((size_t) level == assumptions.size () && constraint.size ())) {
      // Forced backtrack below pseudo decision levels.
      // So one of the two branches above will handle it.
      STOP (decide);
      res = decide (); // STARTS and STOPS profiling
      START (decide);
    } else {
      stats.decisions++;
      if (!decision) {
        int idx = next_decision_variable ();
        const bool target = (opts.target > 1 || (stable && opts.target));
        decision = decide_phase (idx, target);
      }
      search_assume_decision (decision);
    }
  }
  if (res)
    marked_failed = false;
  STOP (decide);
  return res;
}

} // namespace CaDiCaL
