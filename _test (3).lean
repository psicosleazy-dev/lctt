variables p q : Prop

variable x: p → q

#check and.intro 
        (assume y:p ∧ q, (and.left y))
        (assume z:p, (and.intro z (x z)))