variables A B C: Prop

variable x : A → B ∧ C
variable y : A


#check (and.intro (assume y : A, (and.elim_left (x y))) (assume y : A, (and.elim_right (x y))))
