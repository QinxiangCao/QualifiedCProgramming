Inductive CUop :=
  | CO_UMINUS    (**r - *) 
  | CO_UPLUS     (**r + *)
  | CO_NOTBOOL   (**r ! *)
  | CO_NOTINT    (**r ~ *)
.

Inductive CBinop :=
  | CO_PLUS    (**r +  *) 
  | CO_MINUS   (**r -  *)
  | CO_MUL     (**r *  *)
  | CO_DIV     (**r /  *)
  | CO_MOD     (**r %  *)
  | CO_LT      (**r <  *)
  | CO_GT      (**r >  *) 
  | CO_LE      (**r <= *)
  | CO_GE      (**r >= *)
  | CO_EQ      (**r == *)
  | CO_NE      (**r != *)
  | CO_AND     (**r &  *)
  | CO_OR      (**r |  *)
  | CO_XOR     (**r ^  *)
  | CO_SHL     (**r << *)
  | CO_SHR     (**r >> *)
  | CO_BAND    (**r && *)
  | CO_BOR     (**r || *)
.

Inductive CAssignType :=
  | CO_ASSIGN        (**r  =  *)
  | CO_PLUS_ASSIGN   (**r +=  *)
  | CO_MINUS_ASSIGN  (**r -=  *)
  | CO_MUL_ASSIGN    (**r *=  *)
  | CO_DIV_ASSIGN    (**r /=  *)
  | CO_MOD_ASSIGN    (**r %=  *)
  | CO_AND_ASSIGN    (**r &=  *)
  | CO_OR_ASSIGN     (**r |=  *)
  | CO_XOR_ASSIGN    (**r ^=  *)
  | CO_SHL_ASSIGN    (**r <<= *)
  | CO_SHR_ASSIGN    (**r >>= *)
.

Inductive CIncDecType :=
  | CO_INCPRE      (**r ++x *)
  | CO_INCPOST     (**r x++ *)
  | CO_DECPRE      (**r --x *)
  | CO_DECPOST     (**r x-- *)
.

