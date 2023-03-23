variables A B C : Prop

variable x : (A ∨ B) ∧ C
variable y : B → A
variable z : B
variable w : A


#check (and.intro (or.elim (and.elim_left x) (assume w, w) (assume z, y z)) (and.elim_right x))
