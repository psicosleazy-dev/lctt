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

-/

theorem q1 : ((X ∧ X) → Y) →  ¬ Y → ¬ X := sorry

theorem q2 : (X ∨ (Z ∧ X)) →  X := sorry

theorem q3 : (∀ x:U, P x → Q x → R x x) → (∀ y:U, P y ∧ Q y) → (∀ z:U, R z z) := sorry

theorem q4 : (∃ x:U, P x → ¬ Q x) → (∀ y:U, P y) → (∃ z:U, ¬ Q z) := sorry



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

theorem q5 : ∀a:ℕ, soma 0 a = a := sorry

theorem q6 : ∀a:ℕ, soma a 0 = a := sorry

theorem q7 : ∀n:ℕ, vezes n 1 = n := sorry

theorem q8 : ∀a:ℕ, ∀b:ℕ,  soma a b = soma b a := sorry


/-

QUESTÃO EXTRA (pontos extra): Complete a prova dos seguintes teoremas:

-/

theorem soma_assoc: ∀ a b c:ℕ , soma a (soma b c) = soma (soma a b) c := sorry

theorem vezes_succ : ∀a b:ℕ, vezes a (succ b) = soma a (vezes a b) := sorry

theorem dist_vezes_soma: ∀a b c:ℕ, vezes a (soma b c) = soma (vezes a b) (vezes a c) := sorry


end lista_avaliada_4

