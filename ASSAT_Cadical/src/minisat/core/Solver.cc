/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));

//FC
BoolOption    opt_rnd_pol      (_cat, "rnd-pol",        "Random polarity", false);
BoolOption    opt_default_upol      (_cat, "default-upol",        "User polarity", false);


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    //控制求解器的输出详细程度
    verbosity        (0)
    //每次冲突后，变量的活动值都会根据该参数进行指数衰减，用于平衡当前活跃变量和新发现的重要变量，越接近 1.0，衰减越慢。
  , var_decay        (opt_var_decay)
    //每次冲突后，学习子句的活动值都会根据该参数进行指数衰减，越接近 1.0，衰减越慢。
  , clause_decay     (opt_clause_decay)
    //随机选择变量的频率。
  , random_var_freq  (opt_random_var_freq)
    //随机数生成器的种子
  , random_seed      (opt_random_seed)
    //通过特定的数学序列（Luby 序列）来调整重启间隔时间。
  , luby_restart     (opt_luby_restart)
    //冲突子句最小化模式。
    //决定是否以及如何最小化冲突子句：
    //0：不最小化；
    //1：基于第一层传播；
    //2：基于完全反向传播。
  , ccmin_mode       (opt_ccmin_mode)
    //相位保存模式。
    //决定变量上次分配的极性是否保留以供下次分支使用：
    //0：不保存相位；
    //1：部分保存；
    //2：完全保存。
    //通常用于优化启发式搜索。
  , phase_saving     (opt_phase_saving)
    // 随机选择变量极性。
    //true 表示完全随机分配极性，false 使用启发式选择。
    //与 random_var_freq 一起控制求解的随机性。
  , rnd_pol          (opt_rnd_pol)
    //初始化变量活动值时是否随机化。
  , rnd_init_act     (opt_rnd_init_act)
    //垃圾回收的触发比例。
    //当已删除子句占用的内存超过该比例时，触发垃圾回收，释放内存
  , garbage_frac     (opt_garbage_frac)
    //学习子句的最小数量限制。
    //决定了求解器保留学习子句的最小下限，用于避免因清理而丢失有用的学习子句
  , min_learnts_lim  (opt_min_learnts_lim)
    //第一次重启的冲突数阈值.
  , restart_first    (opt_restart_first)
    //控制后续重启阈值如何增.
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
    //学习子句初始最大占比，用于限制学习子句的数量.(1/3)
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
    //冲突数达到此阈值后，开始动态调整学习子句大小。初始值为 100 表示在 100 次冲突后启动
  , learntsize_adjust_start_confl (100)
    //每次调整后，冲突阈值按照此因子增长。
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
    //dec_vars记录当前被分支的变量数量;max_literals：单次冲突中涉及的最大文字数。;tot_literals：冲突处理中累计涉及的文字总数。
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , watches            (WatcherDeleted(ca))
  , order_heap         (VarOrderLt(activity))
  //用于标识当前求解器状态是否正常。true 表示无错误，求解器可继续运行
  , ok                 (true)
  , cla_inc            (1)
  //活跃度系数
  , var_inc            (1)
  , var_inc1           (1)
  //当前传播队列的头指针。指示未处理变量的起始位置
  , qhead              (0)
  //用于简化数据库的分配计数。当赋值数量变化时，触发子句简化。
  , simpDB_assigns     (-1)
  //用于简化数据库的传播计数。当传播次数达到一定阈值后，触发子句简化。
  , simpDB_props       (0)
  , progress_estimate  (0)
  //决定是否移除已经满足的子句。true 表示删除满足的子句以减少内存占用。
  , remove_satisfied   (true)
  //下一个可用变量的编号。用于动态管理变量的分配
  , next_var           (0)

    // Resource constraints:
    //
    //冲突预算（最大允许冲突次数）。-1 表示不设置限制。
  , conflict_budget    (-1)
    //传播预算（最大允许传播次数）。-1 表示不设置限制。
  , propagation_budget (-1)
    //异步中断标志。true 时中断当前求解过程。
  , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
//upol:lbool 是一个枚举类型，可能的值有 l_True、l_False、l_Undef。如果指定为 l_True 或 l_False，变量的初始值将被固定为该极性。
//指定是否将该变量作为决策变量。
//返回编号
Var Solver::newVar(lbool upol, bool dvar)
{
    Var v;
    //如果有可用的空闲变量编号，则从 free_vars 中取出编号分配给变量 v。
    //否则，分配当前未使用的编号 next_var 并递增 next_var。
    if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }else
        v = next_var++;

    //初始化该变量的正负文字在观察列表中的记录，方便快速判断哪些子句需要更新。
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    //初始值为 l_Undef，表示变量未被赋值。
    assigns  .insert(v, l_Undef);
    //vardata：变量的元数据，存储变量的相关信息。
    //CRef_Undef：表示此变量未关联任何原因子句（即未赋值的原因）。
    //0：该变量的决策层级，初始为 0
    vardata  .insert(v, mkVarData(CRef_Undef, 0));
    //activity：变量的活动度，用于分支时选择最优变量。
    //rnd_init_act：
    //如果为 true，则基于随机种子生成一个小的随机数作为初始活动度。
    //如果为 false，则初始活动度设为 0
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    //变量访问标记，通常用于冲突分析时追踪变量是否被处理
    seen     .insert(v, 0);
    //记录变量的初始极性，初始值为 0
    first_polarity.insert(v, 0);
    //polarity：变量的默认极性，默认值为 opt_default_upol
    polarity .insert(v, opt_default_upol);
    //用户指定的极性。由参数 upol 决定
    user_pol .insert(v, upol);
    //决策变量集合，提前为变量 v 分配空间
    decision .reserve(v);
    //增加 trail 容量，确保存储变量分配状态的空间足够
    trail    .capacity(v+1);
    //设置变量是否为决策变量。如果 dvar 为 true，将变量 v 添加到决策队列
    setDecisionVar(v, dvar);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
//用于释放一个变量（Lit l 表示的文字）并将其标记为已释放，以便后续可以重用。
void Solver::releaseVar(Lit l)
{
    //仅当文字未被赋值时才执行释放操作
    if (value(l) == l_Undef){
        //将文字 l 转化为一个单文字子句，并添加到子句集中。并且赋值
        addClause(l);
        //var(l)：从文字 l 中提取对应的变量编号。released_vars：存储所有已释放的变量编号的堆栈或队列。这些变量可以在后续分配新变量时被重用，从而避免浪费资源。
        released_vars.push(var(l));
    }
}


//原始子句（ps）添加到求解器的子句集中，同时返回一些与子句添加结果相关的信息
//vec<Lit>& ps：传入的子句，表示一组文字的集合。
//bool& singleLitReturned：通过引用返回一个布尔值，表示是否检测到单文字子句。
//Lit& singleLitOut：通过引用返回单文字子句的具体值（如果存在）。
bool Solver::addOrigClause(vec<Lit>& ps, bool& singleLitReturned, Lit& singleLitOut) {
    //如果添加子句后仍然满足性问题可解，则返回 true。如果添加子句导致问题无解，则返回 false
    bool still_sat = addClause_(ps);
    //用于指示上次调用 addClause_ 时，是否生成了一个单文字子句
    singleLitReturned = addClause_SingleLitReturned;
    //存储上次调用 addClause_ 时生成的单文字子句中的文字
    singleLitOut = addClause_SingleLit;
    return still_sat;
}

//vec<Lit>& ps：子句 ps 是一个文字集合，表示一个逻辑约束。
bool Solver::addClause_(vec<Lit>& ps)
{
    //用于记录是否在添加过程中生成了单子句及其内容
    addClause_SingleLitReturned = false;
    //确保函数在决策层级为 0 时调用
    assert(decisionLevel() == 0);
    //如果当前状态已经标记为不可满足
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    //将子句中的文字按照一定顺序排列，方便后续检查重复和矛盾文字。
    //消除重复和矛盾：
    //如果子句中存在满足的文字（value(ps[i]) == l_True）或文字与其否定（~p）同时出现，则整个子句已满足，直接返回 true。
    //如果文字为 l_False 或重复，则忽略这些文字，仅保留有效的文字
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    //调用 ps.shrink(i - j) 缩减子句大小，移除多余的空间
    ps.shrink(i - j);
    //出现空子句，修改ok的值
    if (ps.size() == 0)
        return ok = false;
    //如果子句仅剩一个文字（单文字子句），将其入队（uncheckedEnqueue）以触发单子句传播。
    //设置 addClause_SingleLitReturned 为 true，并记录单文字内容到 addClause_SingleLit。
    //进行单子句传播（propagate()）
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);

        // return this upwards.
        addClause_SingleLitReturned = true;
        addClause_SingleLit = ps[0];

        //未导致冲突返回true
        return ok = (propagate() == CRef_Undef);
    }
    //如果子句包含多个文字，分配一个新的子句引用（CRef）：
    //使用子句分配器（ca.alloc）存储子句，并将其标记为非学习子句。
    //将新子句引用加入到主子句集中。
    //将子句附加到相关文字的监视列表中（attachClause），以便后续的传播。
    else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}

//用于将子句 cr 关联到 监视列表中，以便高效地支持单子句传播 
void Solver::attachClause(CRef cr){
    const Clause& c = ca[cr];
    //使用 assert 检查子句大小，确保不会将单文字子句或空子句错误地加入监视列表。
    //单文字子句由 uncheckedEnqueue 直接处理，因此不会进入监视列表。
    assert(c.size() > 1);
    //子句中选择前两个文字（c[0] 和 c[1]）作为被监视的文字
    //每个监视文字的否定（~c[0] 和 ~c[1]）加入到其对应的监视列表中
    //Watcher 是一个辅助结构体，用于记录子句引用和另一个文字：
    //Watcher(cr, c[1])：表示子句 cr 被监视，同时记录另一个文字 c[1]。
    //类似地，Watcher(cr, c[0]) 记录子句和文字 c[0]。
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    //根据子句是否为学习子句（c.learnt()）更新统计信息
    //num_learnts：学习子句数量；learnts_literals：学习子句中的文字总数；num_clauses：普通子句数量；clauses_literals：普通子句中的文字总数
    if (c.learnt()) num_learnts++, learnts_literals += c.size();
    else            num_clauses++, clauses_literals += c.size();
}


//用于从监视列表（watch list）中移除一个子句 cr
void Solver::detachClause(CRef cr, bool strict){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    // Strict or lazy detaching:
    //严格模式和惰性模式的选择
    if (strict){
    //子句的两个监视器被立即从监视列表中移除，严格删除需要更多时间，可能影响性能
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
    //通过标记（smudge）方法，将监视列表标记为“脏”，稍后进行清理
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    //根据子句是否为学习子句（c.learnt()），更新统计信息：
    if (c.learnt()) num_learnts--, learnts_literals -= c.size();
    else            num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    //调用上面的方法将子句 c 的两个监视器从监视列表中移除
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    //locked(c)：检查子句是否被锁定。
    //子句被锁定通常表示它是某个变量的原因子句（即它解释了为什么该变量被赋值为当前值）。
    //获取子句中第一个文字 c[0] 所对应的变量的元数据
    //如果子句被锁定，将其原因子句设置为 CRef_Undef（未定义），表示该变量不再有一个具体的原因子句。
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    //标记子句为已删除
    c.mark(1); 
    ca.free(cr);
}


//检查是否满足
bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
//将当前求解状态回溯到给定的 level 层，并恢复在该层之前的所有决策
void Solver::cancelUntil(int level) {
    //如果当前的决策层比目标层 level 更深，则执行回溯操作
    if (decisionLevel() > level){
        //trail记录了变量赋值的历史决策
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            //phase_saving > 1 或者 phase_saving == 1 且当前决策比最后一个决策更靠前
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
        //表示变量的第一次赋值极性被恢复。
		first_polarity[x]= 1;
        //将变量 x 插入到变量顺序中，以便下一次决策时参考其顺序
            insertVarOrder(x); }
        qhead = trail_lim[level];
        //将 trail 栈的大小缩小到目标回溯层的大小
        trail.shrink(trail.size() - trail_lim[level]);
        //同样缩小 trail_lim 栈，只保留目标回溯层及之前的层次限制
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:
//选择下一个变元，决定变元赋值顺序
//order_heap 是一个存储变元优先级的最大堆（max-heap）。在这个堆中，每个元素都是一个变元，
//按照其活跃性（activity）进行排序。活跃性值越高，变元的优先级越高。
Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    int in_vars=nVars()/3;
    
    // Random decision:
    //生成一个0到1之间的随机数，如果它小于 random_var_freq，则触发随机选择变量的策略
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        //从 order_heap 中随机选择一个变量作为下一个决策的变量。
        next = order_heap[irand(random_seed,order_heap.size())];
        //检查该变量是否未赋值（l_Undef）且是一个决策变量。如果是，增加 rnd_decisions，表示进行了一次随机决策。
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++;
    }

    // Activity based decision:
    //根据活动度选择变量
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
        //rder_heap.removeMin() 会移除并返回 order_heap 中优先级最低（活动度最强）的变量
            next = order_heap.removeMin();

    // Choose polarity based on different polarity modes (global or per-variable):
    //如果未能找到有效的 next 变量，则返回 lit_Undef，表示没有找到可行的分支文字
    if (next == var_Undef)
        return lit_Undef;
    //如果用户指定了变元的极性，则根据该极性返回相应的文字
    else if (user_pol[next] != l_Undef)
        return mkLit(next, user_pol[next] == l_True);
    //如果 rnd_pol 为 true，则随机选择该变量的极性
    else if (rnd_pol)
        return mkLit(next, drand(random_seed) < 0.5);

    //如果以上条件都不满足，选择一个基于极性模式的决策
    else
    {
        //如果该变量不是初始极性
        if(!first_polarity[next])
        {
            //如果变量 next 的索引小于 in_vars，则使用 polarity[next] 来确定极性
            if (next < in_vars) {
                return mkLit(next, polarity[next]);
            }
            //如果变量 next 不在 in_vars 中，则将 polarity[next] 设置为 true，表示默认赋值为正极性。
            else
            {
		polarity[next]=true;
                return mkLit(next, true);
            }
        }
        //如果变量是初始极性，则根据 polarity[next] 恢复它的极性并返回。
        else
        {
            //printf("not first_decision\n");
            return mkLit(next, polarity[next]);
        }
	

    }
}




/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|_//分析冲突_______________________________________________________________________________________________@*/

//遇到冲突时，通过分析冲突产生的原因（即导致冲突的变量赋值），生成一个新的学习子句并决定回溯的决策层
//confl：当前冲突的子句引用
//out_learnt：存储生成的冲突子句
//out_btlevel：存储需要回溯到的决策级别
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    //路径计数器，用于跟踪在当前决策级别遇到的变量数量。
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    //为断言文字（即当前冲突子句的原因）预留一个位置
    out_learnt.push();      // (leave room for the asserting literal)
    //从 trail 的末尾开始遍历
    int index   = trail.size() - 1;

    do{
        //确保当前子句引用有效
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        //获取冲突子句
        Clause& c = ca[confl];

        //如果子句是学习子句（learnt() 返回 true），增加它的活动性
        if (c.learnt())
            claBumpActivity(c);

        //如果 p == lit_Undef（第一次处理冲突子句），从第一个文字开始。否则，从第二个文字开始（跳过断言文字）
        //q：当前处理的文字
        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

        //变量活动性更新,如果 q 的变量未被访问过 (!seen[var(q)]) 且决策级别大于 0，则：
        //检查变量是否在前 in_vars 个变量中，且其值为 true。
        //若满足，则调用 varBumpActivity_New1 增加活动性；否则调用 varBumpActivity。
            int in_vars=nVars()/3;
	    lbool var_Value=value(var(q));

            if (!seen[var(q)] && level(var(q)) > 0){
                
                if((var(q) < in_vars) && (var_Value==l_True ? 1:0))
                {
                    varBumpActivity_New1(var(q));
                }
		else
		{
		    varBumpActivity(var(q));
		}
        //标记变量并分类,标记变量为已访问。
        //如果 q 的决策级别大于等于当前决策级别，增加路径计数器 pathC。
        //否则，将文字 q 添加到冲突子句中。
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        //找下一个子句
        //通过 trail 逆序查找上一个已访问的变量。
        //更新当前文字 p 为找到的变量。
        //获取该变量的原因子句 confl。
        //将 p 标记为未访问，并减少路径计数器。
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    //将断言文字（~p，即 p 的补文字）放入冲突子句的第一个位置
    out_learnt[0] = ~p;
  
    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    //ccmin_mode：
    //模式 2：深度最小化，移除冗余文字。
    //模式 1：简单最小化，只保留无法通过原因子句推导出的文字。
    //其他：不进行简化。
    if (ccmin_mode == 2){
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    //回溯级别计算：
    //如果冲突子句只有一个文字，回溯到级别 0。
    //否则，找到文字的最高决策级别，并将其交换到冲突子句的第一个位置。

    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    //清理标记,清除 seen 标记，恢复变量状态。
    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed from a conflict clause.
//用于检查一个给定的文字是否是冗余的。冗余的意思是该文字对于当前的冲突子句来说不必要，即它的存在不会影响子句的有效性。
bool Solver::litRedundant(Lit p)
{
    //seen_undef：未访问过。
    //seen_source：来源文字。
    //seen_removable：可以移除的文字。
    //seen_failed：无法移除的文字。
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    // 确保：当前文字 p 的变量状态是未访问或来源。p 的变量必须有推导原因（reason(var(p)) 不为 CRef_Undef），否则无法进行递归检查。
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    //通过 reason(var(p)) 获取推导 p 的原因子句。初始化一个堆栈 analyze_stack，用于递归检查父文字。
    Clause*               c     = &ca[reason(var(p))];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    //遍历原因子句中的文字,遍历原因子句中的所有文字，从索引 1 开始（索引 0 是断言文字，跳过）。
    //将当前子句中的文字赋值给 l
    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];
            
            //如果文字的变量满足以下条件之一，跳过检查：
            //变量被分配到决策级别 0（全局赋值，必然满足）。
            //变量是来源文字（seen_source）。
            //变量已经标记为可移除（seen_removable）
            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; }
            
            // Check variable can not be removed for some local reason:
            //无法移除的文字处理
            //如果 l 满足以下条件之一，表示该文字无法被移除：没有推导原因（reason(var(l)) == CRef_Undef）。已经标记为不可移除（seen_failed）。
            //将当前文字 p 和堆栈中所有未访问的文字标记为 seen_failed，并加入到 analyze_toclear 中，用于后续清理。
            //返回 false，表示文字 p 无法被移除。
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }
                    
                return false;
            }

            // Recursively check 'l':
            //递归检查父文字
            //将当前文字 p 的状态（当前索引 i 和文字 p）压入堆栈，便于后续回溯。
            //更新：
            //i 重置为 0，开始检查新的文字。
            //当前文字 p 更新为 l。
            //子句 c 更新为推导 p 的原因子句。
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[reason(var(p))];
        }else{
            //当前文字 p 检查完毕后：
            //如果未被标记为可移除，则标记为 seen_removable。
            //将 p 加入到 analyze_toclear 中
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }

            // Terminate with success if stack is empty:
            //递归回溯
            //如果堆栈为空，表示所有检查已完成，退出循环。
            //否则，从堆栈中恢复上一个未完成的检查状态，继续检查剩余文字。
            if (stack.size() == 0) break;
            
            // Continue with top element on stack:
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }

    //如果函数正常完成，返回 true，表示当前文字 p 是冗余的，可以移除
    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
//对冲突分析过程中的最终冲突进行分析，确定导致当前冲突的变量集合（即冲突核心），并将其存储在 out_conflict 集合中
void Solver::analyzeFinal(Lit p, LSet& out_conflict)
{
    //清空冲突集合 out_conflict：确保结果集合从空开始。
    //将文字 p 加入冲突集合：将当前冲突的起始文字 p 视为导致冲突的一部分
    out_conflict.clear();
    out_conflict.insert(p);

    //如果当前决策层级为 0，则直接返回。这意味着当前状态已经是全局冲突（与根决策无关），冲突集合仅包含文字 p 即可。
    if (decisionLevel() == 0)
        return;

    //将 p 对应的变量标记为“已访问”（seen = 1），以防止重复处理
    seen[var(p)] = 1;

    //遍历决策路径
    //从 trail 的末尾开始逆序遍历，直到决策层的起点 trail_lim[0]。trail 包含变量赋值的记录，后面的变量更接近当前决策。
    //获取当前遍历变量的索引 x。
    //如果变量 x 已标记为“已访问”（seen[x] == 1），则继续处理。
    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            //如果变量 x 没有推导原因（reason(x) == CRef_Undef）：
            //确保变量位于非零层级（level(x) > 0），即它来自于非全局的决策层级。
            //将变量的反文字（~trail[i]）加入冲突集合 out_conflict。这是因为在无推导原因时，变量的赋值直接影响了冲突。
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.insert(~trail[i]);
            }else{
                //如果变量 x 有推导原因：
                //获取推导原因子句 c。
                //遍历子句中除第一个文字外的其他文字（第一个文字通常是断言文字，不用处理）。
                //如果文字对应的变量的决策层级大于 0，将其标记为“已访问”（seen = 1）。这表示该变量也需要加入分析路径。
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            //清除变量的访问标记：避免影响后续分析过程。清除起始文字 p 的访问标记：保持一致性，所有 seen 标记均被复位。
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}

//用于将一个文字 p（表示一个变量及其值）直接加入到赋值轨迹 trail 中，同时更新变量的状态和相关数据。
//Lit p: 需要赋值的文字。
//CRef from: 推导该赋值的原因子句引用（如果是决策赋值则传入 CRef_Undef）
void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    //更新变量的赋值状态var(p) 返回文字对应的变量索引。
    //sign(p) 返回文字的符号，true 表示文字是负文字（即 ¬x），false 表示是正文字（即 x）。
    //lbool(!sign(p))：
    //如果 p 是正文字，则赋值为 l_True。
    //如果 p 是负文字，则赋值为 l_False。
    //将赋值结果存储在 assigns 数组中，用于记录每个变量的当前赋值状态。
    assigns[var(p)] = lbool(!sign(p));
    //记录推导数据
    //vardata[var(p)] 用于存储变量的元数据，包括推导来源子句和赋值的决策层级。
    //mkVarData(from, decisionLevel())：
    //from 表示推导原因子句的引用。
    //decisionLevel() 返回当前的决策层级。
    //这段代码将变量的推导原因子句和赋值时的决策层级一起存储。
    vardata[var(p)] = mkVarData(from, decisionLevel());
    //将文字 p 添加到赋值轨迹 trail 中。
    trail.push_(p);
    //exit_trail[var(p)]=1;
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
//单子句传播
//返回导致冲突的子句（若存在），否则返回 CRef_Undef
CRef Solver::propagate()
{
    //confl: 用于存储冲突子句的引用。如果传播过程中发现冲突，则返回此子句引用。如果没有冲突，则为 CRef_Undef。
    //num_props: 用于记录当前传播过程中进行的赋值操作数。
    CRef    confl     = CRef_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches.lookup(p);
        //ws：watches.lookup(p) 返回与文字 p 相关的子句观察者列表（即监视该文字的子句）。通过该列表来处理与 p 相关的子句。
        Watcher        *i, *j, *end;
        num_props++;

        //遍历观察者列表
        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            //确保子句的格式正确
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            //如果第一个文字为 True则该子句已经满足，传播停止。
            //如果 first 文字不等于 blocker，并且 first 的值为 True，则直接将该观察者添加到结果列表。
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            //查找新的观察文字
            //如果第一个文字为 False，则需要找一个新的文字作为观察文字。遍历子句的后续文字，选择一个尚未被赋值为 False 的文字。
            //如果找到，更新子句的观察文字，并将该观察者添加到新的观察者列表中。
            //跳转到下一个子句：若成功找到新的观察文字，跳过当前子句的剩余处理，进入下一个子句。
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            //如果找不到新的观察文字，说明当前子句已经是单位子句。
            //将当前观察者 w 添加到结果列表。
            //如果子句的第一个文字为 False，说明产生了冲突，将 confl 设置为当前子句引用，并结束传播过程。
            //如果没有冲突，将该文字作为新的赋值加入传播队列，继续传播。
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);
        //将剩余的观察者移除，避免内存浪费。
        NextClause:;
        }
        //更新观察者列表，去除已处理的观察者。
        ws.shrink(i - j);
    }
    //更新统计信息
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/

//定义一个结构体用于排序 learnts 向量中的子句。优先保留活动值较高的非二元子句.
//比较条件：
//如果子句 x 的大小大于 2（即非二元子句），则比较它与子句 y 的活动值：
//如果子句 y 是二元子句（ca[y].size() == 2），则将 x 排在前面。
//否则，比较两个子句的活动值，活动值较小的排在后面。
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};

void Solver::reduceDB()
{
    //extra_lim: 计算删除子句的活动值阈值。cla_inc 是子句的活动增加值，
    //learnts.size() 是已学习子句的数量。
    //extra_lim 是在删除过程中使用的活动阈值，低于该值的子句将被删除。
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    //使用 reduceDB_lt 结构体的排序规则对 learnts 向量中的子句进行排序。
    //该排序确保优先保留活动值较高且大小大于 2 的子句（即非二元子句）。二元子句则排在后面。
    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    //遍历已学习的子句 learnts：
    //i: 当前子句的索引。
    //j: 用于重新排列 learnts 向量的位置，删除的子句不会保留下来。
    //对每个子句 c：
    //如果该子句满足以下条件，则删除该子句：
    //非二元子句（c.size() > 2）。
    //未被锁定的子句（!locked(c)）。
    //前一半的子句或其活动值小于 extra_lim（i < learnts.size() / 2 || c.activity() < extra_lim）。
    //如果子句不满足删除条件，则将其保留并放入 learnts 中
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    //通过 shrink 方法调整 learnts 向量的大小。此操作将去除删除的子句，保留剩余的子句。
    learnts.shrink(i - j);
    //执行垃圾回收
    checkGarbage();
}

//移除满足的学习子句
void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else{
            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            //对子句 c 从索引 2 开始的所有文字进行检查：
            //if (value(c[k]) == l_False)：如果文字 c[k] 的值为 l_False，则将该文字移除。
            //c[k--] = c[c.size()-1];：将最后一个文字移动到 k 位置，并将 k 递减以重新检查新的文字位置。
            //c.pop()：移除子句 c 中最后一个文字。
            //这样可以有效地删除所有被赋值为 False 的文字，减小子句的大小。
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                }
            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    //遍历获取未赋值的决策变元
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/

//用于简化 SAT 问题的子句集，移除已满足的子句，并执行一些额外的操作（如回收内存、重建变量优先级堆等），主要用于 SAT 求解中的预处理和优化
//确保当前决策层级为 0。
//检查是否有冲突或状态无效。
//如果简化条件满足，则跳过简化。
//移除已满足的子句，减少搜索空间。
//（注释的部分）进行内存回收和变量管理。
//检查垃圾并回收内存。
//重新构建优先级堆。
//更新简化数据库信息。
//返回简化结果。
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);

    //FC intervention!
    /*if (remove_satisfied){       // Can be turned off.
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?

        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0)
                trail[j++] = trail[i];
        trail.shrink(i - j);
        //printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
        qhead = trail.size();

        for (int i = 0; i < released_vars.size(); i++)
            seen[released_vars[i]] = 0;

        // Released variables are now ready to be reused:
        append(released_vars, free_vars);
        released_vars.clear();
    }*/
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/

//通过多次执行单子句传播（propagate）和分析冲突来逐步推导变量的赋值，直到找到一个解（即模型）或确定问题不可满足（冲突）。它处理了回溯、学习子句和决策变量的选择等关键部分
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){

        // 执行传播
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            //处理冲突
            //if (decisionLevel() == 0) return l_False;：如果当前决策级别为 0，表示已回溯到根层级，且问题不可满足，返回 l_False。
            //learnt_clause.clear();：清空学习到的子句。
            //analyze(confl, learnt_clause, backtrack_level);：分析冲突 confl，并生成学习到的子句 learnt_clause 和回溯级别 backtrack_level。
            //cancelUntil(backtrack_level);：回溯到 backtrack_level，撤销决策，恢复求解器状态。
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();

            analyze(confl, learnt_clause, backtrack_level);

            cancelUntil(backtrack_level);

            //处理学习到的子句
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            //活动衰减
            varDecayActivity();
            varDecayActivity_New1();
	    //varDecayActivity_New2();
	    //varDecayActivity_New3();
            claDecayActivity();

            // 调整学习子句大小
            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            //没有冲突时的操作
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            //简化和子句减少
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            //处理假设和决策
            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
	  
        }
    }
}

//计算当前求解进度的估计值。进度值是一个介于 0 和 1 之间的数值，表示求解过程中已经完成的工作量。进度的计算基于决策层级、决策栈的大小（trail）以及决策变量的数量。
double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

//实现了 Luby 序列的计算。Luby 序列是一个根据特定规则递增的整数序列，计算它需要找到一个包含指定索引 x 的子序列的大小，并根据该子序列的序列号 seq 返回 y 的 seq 次方。具体步骤如下：

//通过循环，找到包含 x 的子序列的大小（size）和序列号（seq）。
//通过调整子序列的大小，逐步缩小范围直到找到包含 x 的子序列。
//返回 y 的 seq 次方，作为 Luby 序列的值。
static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    //清理和检查初始状态
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    //计数和初始化
    solves++;

    //max_learnts 计算最大学习子句数量：通过公式 nClauses() * learntsize_factor（nClauses() 是当前子句数量，learntsize_factor 是一个预设的调整因子）。
    //if (max_learnts < min_learnts_lim) max_learnts = min_learnts_lim; 确保最大学习子句数不少于 min_learnts_lim，即防止设置的上限小于最小限制。
    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim)
        max_learnts = min_learnts_lim;

    //learntsize_adjust_confl 和 learntsize_adjust_cnt 用来控制学习子句的大小调整。
    //status 初始化为 l_Undef，表示当前解状态未定义。
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    //curr_restarts = 0; 初始化重启计数器 curr_restarts。
    //while (status == l_Undef)：只要 status 是 l_Undef（表示问题尚未解决），就持续进行搜索。
    //double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);：计算当前的重启基准 rest_base，如果启用了 luby_restart，则使用 Luby 序列来决定重启策略；否则，使用指数递增的重启策略。
    //status = search(rest_base * restart_first);：调用 search 函数进行一次求解，rest_base * restart_first 是重启的步长。
    //if (!withinBudget()) break;：检查是否超出了预算（如时间或资源限制），如果超出，则跳出循环。
    //curr_restarts++;：增加重启次数。
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//用于检查一组假设（assumps）是否能推出一个模型（通过 out 输出）。该函数实现了一个启发式的求解过程：
//它将假设加入求解队列，执行单子句传播，最后根据传播的结果决定是否成功。如果传播过程中出现冲突，则返回 false，否则返回 true
bool Solver::implies(const vec<Lit>& assumps, vec<Lit>& out)
{
    trail_lim.push(trail.size());
    //处理每个假设
    //for (int i = 0; i < assumps.size(); i++)：遍历输入的假设 assumps。
    //Lit a = assumps[i];：获取当前的假设文字 a。
    //if (value(a) == l_False)：检查该假设的值。如果其值为 l_False（假设已经被赋为 False），则说明存在冲突，立即调用 cancelUntil(0) 恢复到初始状态，并返回 false 表示无法推导出模型。
    //else if (value(a) == l_Undef)：如果假设未赋值（l_Undef），则调用 uncheckedEnqueue(a) 将该假设加入待传播的队列。
    for (int i = 0; i < assumps.size(); i++){
        Lit a = assumps[i];

        if (value(a) == l_False){
            cancelUntil(0);
            return false;
        }else if (value(a) == l_Undef)
            uncheckedEnqueue(a);
    }

    unsigned trail_before = trail.size();
    //执行单子句传播
    //bool ret = true;：初始化返回值为 true，表示默认假设能够推导出模型。
    //if (propagate() == CRef_Undef)：调用 propagate() 方法执行单子句传播。如果没有冲突（即返回 CRef_Undef），则继续：
    //out.clear(); 清空输出变量 out。
    //for (int j = trail_before; j < trail.size(); j++) out.push(trail[j]);：将传播过程中新增的文字（从 trail_before 到当前 trail.size() 之间的部分）加入到 out 中，表示这些文字是由假设推导出的。
    //else ret = false;：如果传播过程中发生了冲突（即 propagate() 返回非 CRef_Undef），则设置 ret 为 false，表示无法推导出模型。
    bool     ret          = true;
    if (propagate() == CRef_Undef){
        out.clear();
        for (int j = trail_before; j < trail.size(); j++)
            out.push(trail[j]);
    }else
        ret = false;
    
    cancelUntil(0);
    return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}

//打印
void Solver::printStats() const
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %" PRIu64"\n", starts);
    printf("conflicts             : %-12" PRIu64"   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12" PRIu64"   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12" PRIu64"   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12" PRIu64"   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
        // 'dangling' reasons here. It is safe and does not hurt.
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            ca.reloc(learnts[i], to);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
