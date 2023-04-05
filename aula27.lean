namespace aula27

variables P Q : Prop

theorem modus_tollens : (P → Q) → (¬ Q) → (¬ P) := 
  begin
    intro h,
    intro i,
    intro j,
    have k:Q, from h j,
    show false, from i k,
  end

#print modus_tollens  

#check and.intro

theorem and_rev : (P ∧ Q) → (Q ∧ P) := 
  begin
  intro h,
  apply and.intro,
    apply and.elim_right h,
    apply and.elim_left h,
  end

/-

Definições de init.core:

inductive bool : Type
| ff : bool
| tt : bool

inductive nat:Type
| zero : ℕ
| succ : ℕ → ℕ

def add : nat → nat → nat
| a  zero     := a
| a  (succ b) := succ (add a b)

-/
open nat

#check zero
#check succ

def dobro : ℕ → ℕ 
| zero     := zero
| (succ m) := succ (succ (dobro m))

def soma : ℕ → ℕ → ℕ 
| zero     b := b
| (succ x) b := succ (soma x b)

def vezes : ℕ → ℕ → ℕ 
| zero     b := zero
| (succ x) b := soma b (vezes x b)

#reduce vezes 3 0


-- S(a+b) = (a+ S b)

lemma soma_succ_dir : ∀a:ℕ, ∀b:ℕ, succ (soma a b) = (soma a (succ b)) := 
 begin
 intro a,
 induction a,
   -- caso a=0
   intro b,
   unfold soma,
   -- caso a=succ x
   rename a_n x,
   rename a_ih hi,
   intro b0,
   unfold soma,
   congr,
   let hi' := hi b0,
   assumption
 end




theorem dobro_soma : ∀n:ℕ, dobro n = soma n n := 
 begin
 intro n,
 induction n,
   -- caso n=0
   unfold dobro,
   unfold soma,
   -- caso n=succ m
   rename n_n m,
   rename n_ih hi,
     unfold dobro,
     unfold soma,
     rw hi, 
     congr,
     apply soma_succ_dir,
 end


theorem vezes_neutro1 : ∀n:ℕ, vezes 1 n = n := sorry 

theorem vezes_neutro2 : ∀n:ℕ, vezes n 1 = n := sorry

theorem dist_vezes_soma: ∀a b c:ℕ, vezes a (soma b c) =
soma (vezes a b) (vezes a c) := sorry

end aula27