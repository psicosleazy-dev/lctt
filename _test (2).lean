variables p q r : Prop

variable x : (p → q) ∧ (p → r)

#check (assume y:p, and.intro ((and.left x) y) ((and.right x) y))