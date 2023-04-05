namespace aula28

-- definição indutiva sem parâmetro, sem recorrência

inductive MyBool : Type
| mt : MyBool
| mf : MyBool
open MyBool

#print MyBool.rec



-- definição indutiva sem parâmetro, com recorrência

inductive MyNat : Type
| z : MyNat
| s : MyNat → MyNat
open MyNat

#print MyNat.rec



-- definição indutiva com parâmetro, sem recorrência

inductive maybe (a:Type) : Type
| nothing  : maybe 
| just     : a → maybe
open maybe

#check maybe
#check maybe ℕ 
#check maybe bool

#check nothing
#check @nothing ℕ 
#check @nothing bool

#check just 
#check just 2
#check just tt
#check @just ℕ 2
#check @just bool tt





-- definição indutiva com parametro e recorrência

inductive lista (a:Type) : Type
| vazio   : lista
| pref    : a → lista → lista
open lista

#check lista
#check vazio
#check @vazio
#check pref
#check @pref
#check pref 2 (pref 1 vazio)
#check @pref ℕ 2 (@pref ℕ 1 (@vazio ℕ))
#check pref tt (pref ff vazio)




def anexa {a:Type} : lista a → lista a → lista a
| vazio b      := b 
| (pref h t) b := pref h (anexa t b)

infix `++`:60 := anexa

#check anexa 
#check @anexa ℕ 


theorem l1 : ∀ a:Type, ∀x:lista a, vazio ++ x  =  x := 
begin intros, unfold anexa, end

theorem l2 : ∀ a:Type, ∀x:lista a,   x ++ vazio = x := 
begin 
intros a x,
induction x,
unfold anexa,
unfold anexa, congr, assumption,  
end

#check congr_arg


theorem l3 : ∀ a:Type, ∀x y z:lista a,  x ++ (y ++ z) =  (x ++ y) ++ z := 
begin
intro a,
intro x, 
induction x,
  unfold anexa, intros y z, refl, 
  rename x_ᾰ x, rename x_ᾰ_1 l, rename x_ih hi, 
  intros y z,  unfold anexa,
  apply congr_arg (pref x),  apply hi,
end


def reverte {a:Type} : lista a → lista a
| vazio       := vazio
| (pref h t)  := anexa (reverte t) (pref h vazio)

#check reverte (pref 2 (pref 1 vazio))
#reduce reverte (pref 2 (pref 1 vazio))
#reduce reverte (reverte (pref 2 (pref 1 vazio)))


theorem l4 : ∀ a:Type, ∀ x y: lista a, reverte (x ++ y) = (reverte y) ++ (reverte x) :=
begin
intros a x,
induction x with h t hi,
  intro y, unfold reverte, unfold anexa, rw l2, 
  intro y, unfold reverte, unfold anexa, unfold reverte, 
  rw (hi y),  rw l3, 
end


theorem l5 : ∀ a:Type, ∀ x: lista a, reverte (reverte x) = x :=
begin
intro a,
intro x,
induction x with k l m,
unfold reverte, unfold reverte, 
rw l4, rw m, unfold reverte, unfold anexa, 
end


------ definição indutiva com tipos dependentes

inductive vec (a:Type) : nat → Type
| nil    : vec 0
| cons   : Π{n:ℕ}, a → vec n → vec (nat.succ n)
open vec

#check vec
#check nil
#check @nil
#check cons
#check @cons

#check ((cons 4 (cons 2 nil)) : vec ℕ 2)


definition tail {a:Type} {n:ℕ} : Π v:vec a (nat.succ n), vec a n
| (cons h t) := t

open nat

def appn {a:Type} : Π{m n:ℕ}, Π(v1:vec a m), Π(v2:vec a n), vec a (m+n) 
| 0        _  nil          v2  :=  begin rw nat.zero_add, assumption, end
| (succ m) n  (cons h t)   v2  :=  begin let h1 := cons h (appn t v2), rw nat.succ_add, assumption end

#check appn (cons 2 (cons 4 nil)) (cons 1 nil)


end aula28
