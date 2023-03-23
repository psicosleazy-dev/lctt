variables A B C D: Prop

variable x : (A ∨ B → C ∧ D)
variable y : A


#check (or.intro_left B (and.elim_right (x (or.intro_left B y))))
