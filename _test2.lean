-- k)

variables p q r : Prop

variable x : (p ∧ q) ∨ (p ∧ r)
variable y : p ∧ q
variable z : p ∧ r

#check (and.intro
       (or.elim (x) (assume y, and.left y) (assume z, and.left z))
       (or.elim (x) (assume y, (or.intro_left (and.right y))) (assume z, (or.intro_right (and.left z)))))