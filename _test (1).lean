variables p q r : Prop

variable x : p → (q ∧ r)

#check and.intro 
       (assume y:p, and.left (x y))
       (assume z:p, and.right (x z))