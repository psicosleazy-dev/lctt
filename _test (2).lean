variables p q r : Prop

variable x : (p → q) ∧ (p → r)

-- h)

#check (assume y:p, and.intro ((and.left x) y) ((and.right x) y))