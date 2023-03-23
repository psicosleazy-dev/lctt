variables A B C : Prop

#check (assume x : A → B, assume y : B → false, assume z : A, y (x z))
