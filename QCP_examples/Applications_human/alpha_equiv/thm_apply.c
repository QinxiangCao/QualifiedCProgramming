#include "ast.h"

term* sub_thm(term* thm, var_sub_list* lis)
/*@ With t l
      Require store_term(thm, t) * sll_var_sub_list(lis, l)
      Ensure  thm == thm@pre && lis == lis@pre &&
              sll_var_sub_list(lis, l) *
              store_sub_thm_res(thm, __return, t, l)
*/
{
  if(lis == (void*) 0) return thm;
  /*@ lis != 0 &&
      store_term(thm, t) *
      sll_var_sub_list(lis, l)
      which implies
      exists vs l0,
        thm != 0 && 
        l == cons(vs, l0) && 
        store(&(thm -> type), termtypeID(t)) *
        store_term'(thm, t) *
        store_var_sub(lis -> cur, vs) *
        sll_var_sub_list(lis -> next, l0)
  */
  if(thm->type == Quant){
    /*@ exists vs,
        termtypeID(t) == 3 &&
        thm != 0 && 
        store(&(thm -> type), termtypeID(t)) *
        store_term'(thm, t) *
        store_var_sub(lis->cur, vs)
        which implies
        exists sv st sy sz y z qt qvar qterm,
          thm != 0 && lis->cur != 0 &&
          t == TermQuant(qt, qvar, qterm) &&
          vs == VarSub(sv, st) && 
          store(&(thm -> type), termtypeID(t)) *
          store(&(thm -> content.Quant.type), qtID(qt)) *
          store(&(thm -> content.Quant.var), y) *
          store(&(thm -> content.Quant.body), z) *
          store_string(y, qvar) * store_term(z, qterm) *
          store(&(lis->cur->var), sy) *
          store(&(lis->cur->sub_term), sz) *
          store_string(sy, sv) *
          store_term(sz, st) 
    */
    term* den = lis->cur->sub_term;
    thm->content.Quant.body = subst_term(den, lis->cur->var, thm->content.Quant.body);
    return sub_thm(thm->content.Quant.body, lis->next);
  }
  else return (void*) 0;
}

// apply (apply (impl) h1) (h2)
// 不是imply形式时返回(void*) 0
imply_prop* separate_imply(term* t) 
/*@ With trm
    Require store_term(t, trm)
    Ensure t == t@pre && store_imply_res(__return, sep_impl(trm)) * store_term(t, trm)
*/
{
  /*@ store_term(t, trm)
      which implies
      t != 0 && 
      store(&(t -> type), termtypeID(trm)) *
      store_term'(t, trm)
  */
  if (t->type != Apply) return (void*)0;
  /*@ t != 0 && 
      termtypeID(trm) == 2 &&
      store_term'(t, trm)
      which implies
      exists lt rt,
      trm == TermApply(lt, rt) &&
      store_term(t->content.Apply.left, lt) *
      store_term(t->content.Apply.right, rt)
  */
  /*@ exists lt,
      store_term(t->content.Apply.left, lt)
      which implies
      t->content.Apply.left != 0 && 
      store(&(t->content.Apply.left -> type), termtypeID(lt)) *
      store_term'(t->content.Apply.left, lt)
  */
  if (t->content.Apply.left->type != Apply) return (void*)0;
  /*@ exists lt,
      t->content.Apply.left != 0 &&
      termtypeID(lt) == 2 &&
      store_term'(t->content.Apply.left, lt)
      which implies
      exists ll lr,
      lt == TermApply(ll, lr) &&
      store_term(t->content.Apply.left->content.Apply.left, ll) *
      store_term(t->content.Apply.left->content.Apply.right, lr)
  */
  /*@ exists ll,
      store_term(t->content.Apply.left->content.Apply.left, ll)
      which implies
      t->content.Apply.left->content.Apply.left != 0 && 
      store(&(t->content.Apply.left->content.Apply.left->type), termtypeID(ll)) *
      store_term'(t->content.Apply.left->content.Apply.left, ll)
  */
  if (t->content.Apply.left->content.Apply.left->type != Const) return (void*)0;
  /*@ exists ll,
      t->content.Apply.left->content.Apply.left != 0 &&
      termtypeID(ll) == 1 &&
      store_term'(t->content.Apply.left->content.Apply.left, ll)
      which implies
      exists llctype llcctnt,
      ll == TermConst(llctype, llcctnt) &&
      store(&(t->content.Apply.left->content.Apply.left->content.Const.type), ctID(llctype)) *
      store(&(t->content.Apply.left->content.Apply.left->content.Const.content), llcctnt)
  */
  if (t->content.Apply.left->content.Apply.left->content.Const.type != Impl) return (void*)0;
  else return createImplyProp(t->content.Apply.left->content.Apply.right,
                              t->content.Apply.right);
}
// 根据定理形式，匹配结论，得出要检验的前提
term_list* check_list_gen(term* thm, term* target)
/*@ low_level_spec
    With theo targ X
    Require safeExec(ATrue, check_rel(theo, targ), X) && 
            store_term(thm, theo) * 
            store_term(target, targ)
    Ensure  exists t l, 
            safeExec(ATrue, return(makepair(t, l)), X) &&
            target == target@pre &&
            store_term(target, targ) *
            sll_term_list(__return, l)
*/
{
  term_list* check_list = (void*)0;
  term_list** tail_ptr = &check_list;
  /*@ Inv 
    Assert exists t l, 
          safeExec(ATrue, check_from_mid_rel(t, targ, l), X) &&
          target == target@pre &&
          store_term(thm, t) *
          store_term(target, targ) *
          sllbseg_term_list(&check_list, tail_ptr, l) *
          store(tail_ptr, 0)
  */
  while (!alpha_equiv(thm, target)) {
    imply_prop* p = separate_imply(thm);
    free_term(thm);
    if (p == (void*)0) {
      /*@ exists l,
          sllbseg_term_list(&check_list, tail_ptr, l) *
          store(tail_ptr, 0)
          which implies
          store(&(tail_ptr), tail_ptr) *
          sll_term_list(check_list, l)
      */
      free_term_list(check_list);
      return (void*)0;
    }
    // 添加新节点到链表
    term_list* new_node = malloc_term_list();
    /*@ exists ttm,
        p != 0 && store_imply_res(p, sep_impl(ttm))
        which implies
        exists c r tr pa pc,
        ttm == TermApply(TermApply(TermConst(CImpl, c), r), tr) &&
        store(&(p->assum), pa) *
        store(&(p->concl), pc) *
        store_term(pa, r) * store_term(pc, tr)
    */
    new_node->element = p->assum;  // 转移所有权
    new_node->next = (void*)0;

    *tail_ptr = new_node;
    tail_ptr = &(new_node->next);
    thm = p->concl;
    /*@ exists r tr pa pc,
        p != 0 &&
        store(&(p->assum), pa) *
        store(&(p->concl), pc) *
        store_term(pa, r) * store_term(pc, tr)
        which implies
        store_ImplyProp(p, pa, pc, r, tr)
    */
    free_imply_prop(p);  // 释放imply_prop结构体（不释放其成员）
  }
  free_term(thm);
  /*@ exists l,
      sllbseg_term_list(&check_list, tail_ptr, l) *
      store(tail_ptr, 0)
      which implies
      store(&(tail_ptr), tail_ptr) *
      sll_term_list(check_list, l)
  */
  return check_list;
}

term_list* check_list_gen(term* thm, term* target)
  /*@ low_level_spec_aux <= low_level_spec
      With {B} theo targ (c: (term * (list term)) -> program unit B) X
      Require safeExec(ATrue, bind(check_rel(theo, targ), c), X) && 
              store_term(thm, theo) * 
              store_term(target, targ)
      Ensure  exists t l, 
              safeExec(ATrue, applyf(c, makepair(t, l)), X) &&
              target == target@pre &&
              store_term(target, targ) *
              sll_term_list(__return, l)
  */
  ;

solve_res* thm_apply(term* thm, var_sub_list* lis, term* goal) 
/*@ With t l g X
    Require thm != 0 &&
            safeExec(ATrue, thm_app_rel(t, l, g), X) &&
            store_term(thm, t) * 
            sll_var_sub_list(lis, l) * 
            store_term(goal, g)
    Ensure exists sr t,
            thm == thm@pre &&
            safeExec(ATrue, return(sr), X) &&
            store_term(thm, t) *
            sll_var_sub_list(lis, l) * 
            store_term(goal, g) *
            store_solve_res(__return, sr)
*/
{
  term* thm_ins = sub_thm(thm, lis);
  solve_res* res = malloc_solve_res();
  /*@ store_solve_res(res, SRBool(0))
      which implies
      res->type == 0 &&
      res->d.ans == 0
  */
  if (thm_ins == (void*)0) {
    res->type = bool_res;
    res->d.ans = 0;
  } else {
    // Added {} here without changing the semantics!
    /*@ thm_ins != 0 &&
        store_sub_thm_res(thm, thm_ins, t, l)
        which implies
        exists pq st,
        thm_subst_allres_rel(t, l, pq, st) &&
        store_partial_quant(thm, thm_ins, pq) *
        store_term(thm_ins, st)
    */
    /*@ Given pq st*/
    if (alpha_equiv(thm_ins, goal)) {
      res->type = bool_res;
      res->d.ans = 1;
    } else {
      res->type = termlist;
      /*@ res->d.ans == 0
          which implies
          res->d.list == 0
      */
     term* thm_ins_c = copy_term(thm_ins);
      /*@ term_alpha_eqn(st, g) == 0 &&
          thm_subst_allres_rel(t, l, pq, st) &&
          safeExec(ATrue, thm_app_rel(t, l, g), X)
          which implies 
          safeExec(ATrue, bind(check_rel(st, g), get_list), X)
      */
      res->d.list = check_list_gen(thm_ins_c, goal)
        /*@ where(low_level_spec_aux) theo = st, targ = g, c = get_list, X = X; B = solve_res */
      ; 
    }
  }
  return res;
}
