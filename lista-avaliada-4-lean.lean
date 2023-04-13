namespace lista_avaliada_4

/-
  Considere o universo de quantificação U, 
  as proposições X, Y, Z, 
  os predicados unários (sobre U) P e Q
  e o  predicado binário (sobre U) R
-/

variable U:Type
variables X Y Z : Prop
variables P Q : U → Prop
variable R : U → U → Prop


/-
QUESTÃO 1: Complete a prova das seguintes deduções.

theorem q1 : ((X ∧ X) → Y) →  ¬ Y → ¬ X :=
begin
  assume h: ((X ∧ X) → Y),
  assume i: X,
  apply h (apply and.intro i i)


end
-/


theorem q2 : (X ∨ (Z ∧ X)) → X :=
begin
  intro h,
  apply or.elim h,
  apply (assume j:X, j),
  apply (assume k:Z ∧ X, and.elim_right k)
end

--variables (α:Type*)


theorem q3 : (∀ x:U, P x → Q x → R x x) → (∀ y:U, P y ∧ Q y) → (∀ z:U, R z z) :=
  assume h: (∀ x:U, P x → Q x → R x x),
  assume i: (∀ y:U, P y ∧ Q y),
  assume z:U,
  have hz: P z → Q z → R z z, from h z,
  have iz: P z ∧ Q z, from i z,
  show R z z, from (hz (and.elim_left iz)) (and.elim_right iz)





theorem q4 : (∃ x:U, P x → ¬ Q x) → (∀ y:U, P y) → (∃ z:U, ¬ Q z) := 
  assume h: (∃ x:U, P x → ¬ Q x),
  assume i: (∀ y:U, P y),
  exists.elim h
  (assume a:U, 
  assume h2: P a → ¬ Q a,
  have i2: P a, from i a,
  show ∃ z:U, ¬ Q z, from exists.intro a (h2 i2))




/-
Considere a seguinte definição indutiva dos numeros naturais, 
pré-definida pelo sistema Lean:

inductive nat:Type
| zero : ℕ
| succ : ℕ → ℕ

e as seguintes definições próprias das
operações de soma e multiplicação:

-/

open nat

def soma : ℕ → ℕ → ℕ 
| zero     b := b
| (succ x) b := succ (soma x b)

def vezes : ℕ → ℕ → ℕ 
| zero     b := zero
| (succ x) b := soma b (vezes x b)

/-

QUESTÃO 2: Complete a prova dos seguintes teoremas:

-/

theorem q5 : ∀a:ℕ, soma 0 a = a := 
begin
intro a,
induction a,
-- caso a = 0
unfold soma,
-- caso a = succ x
rename a_n x,
rename a_ih hi,
refl,
end

theorem q6 : ∀a:ℕ, soma a 0 = a :=
begin
intro a,
induction a,
-- caso a = 0
unfold soma,
-- caso a = succ x
rename a_n x,
rename a_ih hi,
unfold soma,
rw hi,
end

/-
theorem q7 : ∀n:ℕ, vezes n 1 = n :=
begin
intro n,
induction n,
-- caso n = 0
unfold vezes,
-- caso n = succ x
rename n_n m,
rename n_ih hi,
end
-/


/-
theorem q8 : ∀a:ℕ, ∀b:ℕ,  soma a b = soma b a :=
begin
intro a,
induction a,
-- caso a = 0
  intro b,
  unfold soma,
-- caso a = succ x

end
-/

/-

QUESTÃO EXTRA (pontos extra): Complete a prova dos seguintes teoremas:

-/

theorem soma_assoc: ∀ a b c:ℕ , soma a (soma b c) = soma (soma a b) c := sorry

theorem vezes_succ : ∀a b:ℕ, vezes a (succ b) = soma a (vezes a b) := sorry

theorem dist_vezes_soma: ∀a b c:ℕ, vezes a (soma b c) = soma (vezes a b) (vezes a c) := sorry


end lista_avaliada_4

