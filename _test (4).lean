variables p q r s: Prop

variable x : p → q ∨ r
variable y : q → s
variable z : r → s
variable a : q
variable b : r

#check (assume w:p, (or.elim ((y a) (z b))))
