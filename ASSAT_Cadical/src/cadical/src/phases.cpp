#include "internal.hpp"

namespace CaDiCaL {

void Internal::copy_phases (vector<signed char> &dst) {
  START (copy);
  for (auto i : vars)
    dst[i] = phases.saved[i];
  STOP (copy);
}

void Internal::clear_phases (vector<signed char> &dst) {
  START (copy);
  for (auto i : vars)
    dst[i] = 0;
  STOP (copy);
}

void Internal::phase (int lit) {
  const int idx = vidx (lit);
  signed char old_forced_phase = phases.forced[idx];
  signed char new_forced_phase = sign (lit);
  if (old_forced_phase == new_forced_phase) {
    LOG ("forced phase remains at %d", old_forced_phase * idx);
    return;
  }
  if (old_forced_phase)
    LOG ("overwriting old forced phase %d", old_forced_phase * idx);
  LOG ("new forced phase %d", new_forced_phase * idx);
  phases.forced[idx] = new_forced_phase;
}

void Internal::phase_target (int lit,int value) {
  const int idx = vidx (lit);
  phases.forced[idx] = value;
}


void Internal::initphase (int lit) {
  const int idx = vidx (lit);
  phases.forced[idx] = -1;
  // if(lit == max_var){
  //   for(int i = 0; i < max_var ;i++){
  //     printf("%d的初始相位是:%d",i+1,phases.forced[i+1]);
  //   }
  // }
}

// void Internal::phase (int lit) {
//   const int idx = vidx (lit);
//   signed char old_forced_phase = phases.forced[idx];

//   // 计算变量的范围
//   int total_vars = max_var;  // 需要确保 max_var 代表的是变元的总数
//   int in_vars = total_vars / 3;  // 前 1/3 变量的阈值

//   // 设定新极性值：前 1/3 设置为 -1（false），其余设置为 +1（true）
//   signed char new_forced_phase = (idx < in_vars) ? -1 : 1;

//   if (old_forced_phase == new_forced_phase) {
//     LOG ("forced phase remains at %d", old_forced_phase * idx);
//     return;
//   }
//   if (old_forced_phase)
//     LOG ("overwriting old forced phase %d", old_forced_phase * idx);
  
//   LOG ("new forced phase %d", new_forced_phase * idx);
//   phases.forced[idx] = new_forced_phase;
// }


void Internal::unphase (int lit) {
  const int idx = vidx (lit);
  signed char old_forced_phase = phases.forced[idx];
  if (!old_forced_phase) {
    LOG ("forced phase of %d already reset", lit);
    return;
  }
  LOG ("clearing old forced phase %d", old_forced_phase * idx);
  phases.forced[idx] = 0;
}

} // namespace CaDiCaL
