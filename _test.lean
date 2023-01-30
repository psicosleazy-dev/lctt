variables p q r : Prop

variable z : (p ∧ q) ∨ (p ∧ r)

#check ((or.elim z) (assume x : p ∧ q, and.left x) (assume y : p ∧ r, and.left y))

#check ((or.elim z) (assume x : p ∧ q, or.intro_left r (and.right x)) (assume y : p ∧ r, or.intro_right q (and.right y)))