Require Import OrderedTypeEx.

Module Type UsualOrderedTypeWithHints.

  Include UsualOrderedType.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End UsualOrderedTypeWithHints.