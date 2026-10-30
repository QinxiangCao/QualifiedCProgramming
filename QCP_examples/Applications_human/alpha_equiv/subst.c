#include "ast.h"

term *subst_var(char *den, char *src, term *t)
/*@ default */
{
  /*@ store_term(t, trm) 
      which implies
        t != 0 && 
        store(&(t -> type), termtypeID(trm)) *
        store_term'(t, trm)
  */
  switch (t->type) {
    case Var: {
      /*@ termtypeID(trm) == 0 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y var,
            t != 0 && 
            trm == TermVar(var) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Var), y) *
            store_string(y, var)
      */
      if (!strcmp(t->content.Var, src)) {
        free_str(t->content.Var);
        t->content.Var = strdup(den);
      }
      break;
    }
    case Const: {
      /*@ termtypeID(trm) == 1 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists con typ,
            t != 0 && 
            trm == TermConst(typ, con) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Const.type), ctID(typ)) *
            store(&(t -> content.Const.content), con) 
      */
      break;
    }
    case Apply: {
      /*@ termtypeID(trm) == 2 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z lt rt,
            t != 0 && 
            trm == TermApply(lt, rt) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Apply.left), y) *
            store(&(t -> content.Apply.right), z) *
            store_term(y, lt) * store_term(z, rt)
      */
      t->content.Apply.left = subst_var(den, src, t->content.Apply.left);
      t->content.Apply.right = subst_var(den, src, t->content.Apply.right);
      break;
    }
    case Quant: {
      /*@ termtypeID(trm) == 3 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z qt qvar qterm,
            t != 0 && 
            trm == TermQuant(qt, qvar, qterm) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Quant.type), qtID(qt)) *
            store(&(t -> content.Quant.var), y) *
            store(&(t -> content.Quant.body), z) *
            store_string(y, qvar) * store_term(z, qterm)
      */
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_var(den, src, t->content.Quant.body);
      }
      break;
    }
    default: {
      /*@ Branch clear all
       */
      break;
    }
  }
  return t;
}

term *subst_term(term *den, char *src, term *t)
/*@ implementation
    With trm src_str den_term
      Require den != 0 && src != 0 && t != 0 &&
              store_term(t, trm) *
              store_string(src, src_str) *
              store_term(den, den_term)
      Ensure den == den@pre && src == src@pre &&
             store_term(__return, term_subst_t(den_term, src_str, trm)) *
             store_term(den, den_term) *
             store_string(src, src_str)
*/
{
  /*@ store_term(t, trm) 
      which implies
        t != 0 && 
        store(&(t -> type), termtypeID(trm)) *
        store_term'(t, trm)
  */
  switch (t->type) {
    case Var: {
      /*@ termtypeID(trm) == 0 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y var,
            t != 0 &&
            trm == TermVar(var) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Var), y) *
            store_string(y, var)
      */
      if (!strcmp(t->content.Var, src)) {
        /*@ exists y var,
            t != 0 &&
            trm == TermVar(var) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Var), y) *
            store_string(y, var)
            which implies
            store_term(t, trm)
        */
        free_term(t);
        t = copy_term(den);
      }
      break;
    }
    case Const: {
      /*@ termtypeID(trm) == 1 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists con typ,
            t != 0 && 
            trm == TermConst(typ, con) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Const.type), ctID(typ)) *
            store(&(t -> content.Const.content), con) 
      */
      break;
    }
    case Apply: {
      /*@ termtypeID(trm) == 2 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z lt rt,
            t != 0 && 
            trm == TermApply(lt, rt) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Apply.left), y) *
            store(&(t -> content.Apply.right), z) *
            store_term(y, lt) * store_term(z, rt)
      */
      t->content.Apply.left = subst_term(den, src, t->content.Apply.left) /*@ where(implementation) */;
      t->content.Apply.right = subst_term(den, src, t->content.Apply.right) /*@ where(implementation) */;
      break;
    }
    case Quant: {
      /*@ termtypeID(trm) == 3 &&
          t != 0 && 
          store(&(t -> type), termtypeID(trm)) *
          store_term'(t, trm)
          which implies
          exists y z qt qvar qterm,
            t != 0 && 
            trm == TermQuant(qt, qvar, qterm) &&
            store(&(t -> type), termtypeID(trm)) *
            store(&(t -> content.Quant.type), qtID(qt)) *
            store(&(t -> content.Quant.var), y) *
            store(&(t -> content.Quant.body), z) *
            store_string(y, qvar) * store_term(z, qterm)
      */
      if (strcmp(t->content.Quant.var, src)) {
        t->content.Quant.body = subst_term(den, src, t->content.Quant.body) /*@ where(implementation) */;
      }
      break;
    }
    default: {
      /*@ Branch clear all
       */
      break;
    }
  }
  return t;
}
