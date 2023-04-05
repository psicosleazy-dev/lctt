
variable S: Type*
variable Q: S → S → Prop

theorem t1 (h: ∀  x y : S,  Q x y) :  (∀ u:S, Q u u) :=
show ∀ u:S, Q u u, from
      assume u:S,  (h u) u 

theorem t1v2 (S: Type*) (Q: S → S → Prop)  (h: ∀  x y : S,  Q x y)  :  (∀ u:S, Q u u) :=
show ∀ u:S, Q u u, from
      assume u:S,  (h u) u 

------------------------------------------------
variables  P R: S → Prop

theorem t2  (h1: ∀ x: S, P x → R x) (h2: ∀ x: S, P x) :   ∀ x:S, R x :=
assume x: S, (h1 x) (h2 x) 

------------------------------------

theorem t3   (h: ∀ x: S, P x ∧ R x)  : ∀ y: S, P y :=
assume y: S, and.left (h y)

-------------------------



theorem t4 (h : ∃ x:S , P x ∧ R x) : ∃ x:S , R x ∧ P x :=
exists.elim h
  (assume w : S ,
    assume hw : P w ∧ R w,
    show ∃ x:S, R x ∧ P x, from 
          ⟨ w,  (and.intro hw.right hw.left) ⟩ )


theorem t4v2 (h : ∃ x:S , P x ∧ R x) : ∃ x:S , R x ∧ P x :=
exists.elim h
  (assume w : S ,
    assume hw : P w ∧ R w,
    show ∃ x:S, R x ∧ P x, from 
            ⟨w, ⟨ hw.right, hw.left⟩⟩ )

#print t4v2

theorem t4v3 (h : ∃ x:S, P x ∧ R x) : ∃ x:S, R x ∧ P x :=
match h with ⟨w, hw⟩ :=
  ⟨w, hw.right, hw.left⟩
end


----------------------------------------
variable T: S → Prop 

-----∃x.P(x), ∀y.P(y) ⇒ T(y) ∧ R(y) |-- ∃z.R(z)

theorem t5 (h1 : ∃ x:S, P x) (h2: ∀ y:S, P y → (T y ∧ R y)) : ∃ z:S, R z := 
exists.elim h1
(assume w: S,
 assume hw : P w,
     ⟨ w, and.right ((h2 w) hw)  ⟩ )

---------------------------

theorem t61 : (∀ x:S, P x) →  ¬ (∃ x:S, ¬ P x) :=
assume h1: ∀ x:S, P x,
assume h2: ∃ x:S, (P x) → false,  
show false, from 
exists.elim h2
 (assume w:S, 
  assume h2w: (P w) → false, 
      h2w (h1 w) )


theorem t62: ¬ (∃ x:S, ¬ P x) →  (∀ x:S, P x) := sorry 

---------------------------------

theorem t71 : (∃ x:S,P x) →  ¬ (∀ x:S, ¬ P x) := 
assume h1 : ∃ x:S,P x,
assume h2 : ∀ x:S, (P x) → false, 
show false, from
 exists.elim h1
 (assume w: S,
  assume h1w: P w,
     (h2 w) h1w  )


theorem t72:  ¬ (∀ x:S, ¬ P x)  →  (∃  x:S,P x) := sorry 

---------------------------------

theorem t81 : (¬ ∃ x:S, P x)  →   (∀ x:S, ¬ P x) := 
assume h : ¬ ∃ x:S, P x,
assume x:S, 
assume hpx: P x,
        h (exists.intro x hpx)


theorem t82 : (∀ x:S, ¬ P x) → (¬ ∃ x:S, P x) :=
assume h1 : ∀ x:S, ¬ P x,
assume h2:  ∃ x:S, P x,
show false, from
exists.elim h2
(assume w: S,
 assume h2w: P w, 
  (h1 w) h2w )


---------------------------------

-- theorem t9 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry
