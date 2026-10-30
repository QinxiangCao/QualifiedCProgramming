

#include "safeexec_def.h"


/*@ Import Coq  Require Import ast_lib */
/*@ Import Coq  Require Import thm_apply_lib */
/*@ Import Coq  Require Import malloc */
/*@ Import Coq  Require Import super_poly_sll2 */

/*@ Extern Coq (term :: *) */
/*@ Extern Coq (partial_quant :: *) */
/*@ Extern Coq (var_sub :: *) */
/*@ Extern Coq (solve_res :: *) */
/*@ Extern Coq (ImplyProp :: *) */
/*@ Extern Coq (var_name :: *)*/
/*@ Extern Coq (const_type :: *)*/
/*@ Extern Coq (quant_type :: *)*/
/*@ Extern Coq (term_type :: *)*/
/*@ Extern Coq (CImpl : const_type) 
               (makepair: term -> list term ->  (term * (list term)))
               (store_string : Z -> list Z -> Assertion)
               (store_term : Z -> term -> Assertion)
               (store_term' : Z -> term -> Assertion)
               (store_term_res : Z -> option term -> Assertion)
               (store_term_cell : Z -> term -> Assertion)
               (sll_term_list : Z -> list term -> Assertion)
               (sllseg_term_list : Z -> list term -> Assertion)
               (sllbseg_term_list : Z -> Z -> list term -> Assertion)
               (store_partial_quant : Z -> Z -> partial_quant -> Assertion)
               (store_var_sub : Z -> var_sub -> Assertion)
               (store_var_sub_cell : Z -> var_sub -> Assertion)
               (sll_var_sub_list : Z -> list var_sub -> Assertion)
               (sllseg_var_sub_list : Z -> list var_sub -> Assertion)
               (sllbseg_var_sub_list : Z -> Z -> list var_sub -> Assertion)
               (store_solve_res : Z -> solve_res -> Assertion)
               (store_solve_res' : Z -> solve_res -> Assertion)
               (store_ImplyProp : Z -> Z -> Z -> term -> term -> Assertion)
               (store_imply_res : Z -> option ImplyProp -> Assertion)
               (list_Z_cmp : list Z -> list Z -> Z)
               (term_alpha_eqn : term -> term -> Z)
               (term_subst_v : list Z -> list Z -> term -> term)
               (term_subst_t : term -> list Z -> term -> term)
               (ctID : const_type -> Z)
               (qtID : quant_type -> Z)
               (ttID : term_type -> Z)
               (termtypeID : term -> Z)
               (TermVar: list Z -> term)
               (TermConst: const_type -> Z -> term)
               (TermApply: term -> term -> term)
               (TermQuant: quant_type -> list Z -> term -> term)
               (VarSub: list Z -> term -> var_sub)
               (thm_subst_allres: term -> list var_sub -> option (partial_quant * term))
               (sep_impl: term -> option ImplyProp)
               (gen_pre: term -> term -> list term)
               (thm_app_result: term -> list var_sub -> term -> solve_res)
               (imply_res_Cont: term -> term -> option ImplyProp)
               (SRBool: Z -> solve_res)
               (store_sub_thm_res: Z -> Z -> term -> list var_sub -> Assertion)
               (thm_subst_allres_rel: term -> list var_sub -> partial_quant -> term -> Prop)
               (cur_term_list: term -> term -> list term)
               (cur_thm: term -> list term -> term)
               (gen_res: term -> term -> list term -> Assertion)
               (check_rel: term -> term -> program unit (term * list term))
               (check_from_mid_rel: term -> term -> list term -> program unit (term * list term))
               (thm_app_rel: term -> list var_sub -> term -> program unit (solve_res))
               (get_list: (term * list term) -> program unit solve_res)
*/

typedef int bool;

enum const_type {
  Num = 0,
  // oper
  Add,
  Mul,
  // pred
  Eq,
  Le,
  // connect
  And,
  Or,
  Impl
};
typedef enum const_type const_type;

enum quant_type { Forall, Exists };
typedef enum quant_type quant_type;

enum term_type { Var, Const, Apply, Quant };
typedef enum term_type term_type;

struct term {
  term_type type;
  union {
    char *Var;
    struct {
      const_type type;
      int content;
    } Const;
    struct {
      struct term *left;
      struct term *right;
    } Apply;
    struct {
      quant_type type;
      char *var;
      struct term *body;
    } Quant;
  } content;
};
typedef struct term term;

struct term_list {
  term *element;
  struct term_list *next;
};
typedef struct term_list term_list;

typedef struct var_sub {
  char *var;
  term *sub_term;
} var_sub;

typedef struct var_sub_list {
  var_sub *cur;
  struct var_sub_list *next;
} var_sub_list;

typedef enum { bool_res, termlist } res_type;
typedef struct solve_res {
  res_type type;
  union {
    bool ans;
    term_list *list;
  } d;
} solve_res;

typedef struct imply_prop {
  term *assum;
  term *concl;
} imply_prop;

/* BEGIN Given Functions */

// malloc 函数，内存均初始为全0
term_list *malloc_term_list()
    /*@ Require emp
        Ensure __return != 0 &&
              store(&(__return -> element), 0) *
              store(&(__return -> next), 0)
    */
    ;

solve_res *malloc_solve_res()
    /*@ Require emp
        Ensure __return != 0 &&
              store_solve_res(__return, SRBool(0))
    */
    ;

// 构造函数
imply_prop *createImplyProp(term *t1, term *t2)
    /*@ With term1 term2
          Require store_term(t1, term1) *
                  store_term(t2, term2)
          Ensure exists t1' t2',
                t1 == t1@pre && t2 == t2@pre &&
                  store_term(t1, term1) *
                  store_term(t2, term2) *
                store_ImplyProp(__return, t1', t2', term1, term2)
    */
    ;

// 深拷贝函数
term *copy_term(term *t)
    /*@ With _term
          Require store_term(t, _term)
          Ensure __return != 0 &&
                store_term(t, _term) *
                store_term(__return, _term)
    */
    ;

term_list *copy_term_list(term_list *list)
    /*@ With l
          Require sll_term_list(list, l)
          Ensure __return != 0 &&
                sll_term_list(list, l) *
                sll_term_list(__return, l)
    */
    ;

// free 函数
void free_str(char *s)
    /*@ Require s != 0 && exists n, store_string(s, n)
        Ensure emp
    */
    ;

void free_imply_prop(imply_prop *p)
    /*@ With term1 term2 t1 t2
          Require store_ImplyProp(p, t1, t2, term1, term2)
          Ensure store_term(t1, term1) *
                store_term(t2, term2) *
                emp
    */
    ;

void free_term(term *t)
    /*@ Require exists _term, store_term(t, _term)
        Ensure emp
    */
    ;

void free_term_list(term_list *list)
    /*@ Require exists l, sll_term_list(list, l)
        Ensure emp
    */
    ;

// string 相关函数
char *strdup(const char *s)
    /*@ With str
          Require store_string(s, str)
          Ensure __return != 0 &&
                store_string(s, str) *
                store_string(__return, str)
    */
    ;

int strcmp(const char *s1, const char *s2)
    /*@ With str1 str2
          Require store_string(s1, str1) *
                  store_string(s2, str2)
          Ensure __return == list_Z_cmp(str1, str2) &&
                store_string(s1, str1) *
                store_string(s2, str2)
    */
    ;

/* END Given Functions */

term *subst_var(char *den, char *src, term *t)
  /*@ With trm src_str den_str
        Require den != 0 && src != 0 && t != 0 &&
                store_term(t, trm) *
                store_string(src, src_str) *
                store_string(den, den_str)
        Ensure __return == t && t == t@pre && den == den@pre && src == src@pre &&
              store_term(t, term_subst_v(den_str, src_str, trm)) *
              store_string(den, den_str) *
              store_string(src, src_str)
  */
  ;

term *subst_term(term *den, char *src, term *t)
    /*@ With trm src_str den_term
          Require den != 0 && src != 0 && t != 0 &&
                  store_term(t, trm) *
                  store_string(src, src_str) *
                  store_term(den, den_term)
          Ensure den == den@pre && src == src@pre &&
                store_term(__return, term_subst_t(den_term, src_str, trm)) *
                store_term(den, den_term) *
                store_string(src, src_str)
    */
  ;

bool alpha_equiv(term *t1, term *t2)
    /*@ With term1 term2
      Require store_term(t1, term1) *
              store_term(t2, term2)
      Ensure __return == term_alpha_eqn(term1, term2) && t1 == t1@pre && t2 == t2@pre
      && store_term(t1, term1) * store_term(t2, term2)
    */
    ;

term* sub_thm(term* thm, var_sub_list* lis)
  /*@ With t l
        Require store_term(thm, t) * sll_var_sub_list(lis, l)
        Ensure  thm == thm@pre && lis == lis@pre &&
                sll_var_sub_list(lis, l) *
                store_sub_thm_res(thm, __return, t, l)
  */
  ;

imply_prop* separate_imply(term* t) 
  /*@ With trm
    Require store_term(t, trm)
    Ensure t == t@pre && store_imply_res(__return, sep_impl(trm)) * store_term(t, trm)
  */
  ;

term_list* check_list_gen(term* thm, term* target)
  /*@ With theo targ X
      Require safeExec(ATrue, check_rel(theo, targ), X) && store_term(thm, theo) * store_term(target, targ)
      Ensure  exists t l, 
              safeExec(ATrue, return(makepair(t, l)), X) &&
              target == target@pre &&
              store_term(target, targ) *
              sll_term_list(__return, l)
  */
  ;

solve_res* thm_apply(term* thm, var_sub_list* lis, term* goal)
#ifndef QCP_THM_APPLY_IMPLEMENTATION
  /*@ high_level_spec
      With t l g
      Require store_term(thm, t) * 
              sll_var_sub_list(lis, l) * 
              store_term(goal, g)
      Ensure exists t_after,
            thm == thm@pre &&
            store_term(thm, t_after) *
            sll_var_sub_list(lis, l) * 
            store_term(goal, g) *
            store_solve_res(__return, thm_app_result(t, l, g))
  */
#endif
  ;
  
