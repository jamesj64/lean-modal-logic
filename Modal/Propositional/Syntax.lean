import Mathlib.Data.Set.Basic

universe u

namespace propositional


inductive wff : Type
| Atom : Nat → wff
| Falsum : wff
| Implies : wff → wff → wff
| Nec : wff → wff

deriving instance DecidableEq for wff

open wff

open Classical

notation "⊥" => Falsum
notation " p " => Atom
infixr:75 " ⊃ " => wff.Implies
infixr:80 " ~> " => wff.Implies
notation:max " ~ " φ => φ ⊃ ⊥
prefix:95 "□" => Nec
prefix:95 "◇" => λ φ => ~ □ ~ φ

@[simp]
def degree : wff → Nat
| Atom _ | ⊥ => 0
| □ φ => 1 + degree φ
| φ ~> ψ => degree φ + degree ψ + 1

@[simp]
def depth : wff → Nat
| Atom _ | ⊥ => 0
| □ φ => 1 + depth φ
| φ ~> ψ => 1 + max (depth φ) (depth ψ)


-- This definition of proof was heavily inspired by https://philpapers.org/archive/BENAHC-2.pdf
@[reducible]
inductive proof : Set wff → wff → Prop
| ax {Γ} {α} (h : α ∈ Γ) : proof Γ α
| ax1 {Γ} {α β} : proof Γ (α ~> β ~> α)
| ax2 {Γ} {α β γ} : proof Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
| ax3 {Γ} {α β} : proof Γ (((~α) ~> (~β)) ~> (β ~> α))
| mp {Γ} {α β} (h : proof Γ (α ~> β)) (ha : proof Γ α) : proof Γ β
| nec {Γ} {α} (h : proof ∅ α) : proof Γ (□ α)
| distr {Γ} {α β} : proof Γ (□ (α ~> β) ~> □ α ~> □ β)

@[reducible]
inductive proofS5 : Set wff → wff → Prop
| ax {Γ} {α} (h : α ∈ Γ) : proofS5 Γ α
| ax1 {Γ} {α β} : proofS5 Γ (α ~> β ~> α)
| ax2 {Γ} {α β γ} : proofS5 Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
| ax3 {Γ} {α β} : proofS5 Γ (((~α) ~> (~β)) ~> (β ~> α))
| mp {Γ} {α β} (h : proofS5 Γ (α ~> β)) (ha : proofS5 Γ α) : proofS5 Γ β
| nec {Γ} {α} (h : proofS5 ∅ α) : proofS5 Γ (□ α)
| distr {Γ} {α β} : proofS5 Γ (□ (α ~> β) ~> □ α ~> □ β)
| axT {Γ} {α} : proofS5 Γ (□ α ~> α)
| axB {Γ} {α} : proofS5 Γ (α ~> □◇α)
| axS4 {Γ} {α} : proofS5 Γ (□α ~> □□α)

open proof

notation Γ " ⊢ " φ => proof Γ φ
notation Γ " ⊬ " φ => ¬ proof Γ φ
notation " ⊢ " φ => proof ∅ φ
notation " ⊬ " φ => ¬ proof ∅ φ

notation Γ " ⊢ₛ₅ " φ => proofS5 Γ φ
notation Γ " ⊬ₛ₅ " φ => ¬ proofS5 Γ φ
notation " ⊢ₛ₅ " φ => proofS5 ∅ φ
notation " ⊬ₛ₅ " φ => ¬ proofS5 ∅ φ

@[simp]
lemma s5_stronger_k {Γ : Set wff} {φ : wff} : (Γ ⊢ φ) → Γ ⊢ₛ₅ φ := by
  intro h
  induction h
  . apply proofS5.ax; assumption
  . apply proofS5.ax1
  . apply proofS5.ax2
  . apply proofS5.ax3
  . case mp _ _ ih₁ ih₂ => apply proofS5.mp ih₁ ih₂
  . apply proofS5.nec; assumption
  . apply proofS5.distr


lemma reflexive {Γ : Set wff} {φ : wff} : Γ ⊢ φ ⊃ φ :=
  have : Γ ⊢ (φ ~> φ ~> φ) ~> φ ~> φ := mp ax2 ax1
  mp this ax1

lemma monotonicity {Γ Δ : Set wff} {φ : wff} (sub : Γ ⊆ Δ) (h : Γ ⊢ φ) : Δ ⊢ φ := by
  induction h with
  | ax h => exact ax (sub h)
  | ax1 => apply ax1
  | ax2 => apply ax2
  | ax3 => apply ax3
  | mp _ _ ih₁ ih₂ =>
    simp_all
    apply mp ih₁ ih₂
  | nec h _ =>
    apply nec; apply h
  | distr => apply distr

@[simp]
def consistent (Γ : Set wff) := Γ ⊬ ⊥

lemma cons_sub {Γ Δ : Set wff} (sub : Γ ⊆ Δ) (h : consistent Δ) : consistent Γ := by
  apply (monotonicity sub).mt
  simp_all

-- (~φ ~> ~⊥) ~> ⊥ ~> φ
-- ~⊥ from reflexivity
-- ~φ ~> ~⊥ from ax1 + mp
-- mp to φ

lemma cut {Γ : Set wff} {α β γ : wff} (h₁ : Γ ⊢ α ~> β) (h₂ : Γ ⊢ β ~> γ) : Γ ⊢ α ~> γ :=
  mp (mp ax2 (mp ax1 h₂)) h₁

lemma hs {Γ : Set wff} {α β γ : wff} : Γ ⊢ (β ~> γ) ~> ((α ~> β) ~> (α ~> γ)) :=
  have : Γ ⊢ (β ~> γ) ~> ((α ~> β ~> γ) ~> ((α ~> β) ~> α ~> γ)) := mp ax1 ax2
  mp (mp ax2 this) ax1

lemma l1 {Γ : Set wff} {α β : wff} : Γ ⊢ α ~> ((α ~> β) ~> β) :=
  mp (mp hs (mp ax2 reflexive)) ax1

lemma dne {Γ : Set wff} {φ : wff} : (Γ ⊢ ~~φ) → Γ ⊢ φ := by
  intro h
  have : Γ ⊢ (~~φ) ~> (((~~φ) ~> φ) ~> φ) := l1
  have := mp this h
  apply mp (cut (cut ax1 (cut ax3 ax3)) this) h


theorem deduction {Γ : Set wff} {φ ψ : wff} : (insert φ Γ ⊢ ψ) → Γ ⊢ φ ~> ψ := by
  intro h
  generalize eq : insert φ Γ = Γ'; rw [eq] at h
  induction h with
  | ax h =>
    rw [←eq] at h
    cases h with
    | inl ap =>
      have : Γ ⊢ φ ~> φ := reflexive
      rw [ap]; assumption
    | inr g =>
      have := ax g
      apply mp ax1 this
  | ax1 =>
    apply mp ax1 ax1
  | ax2 =>
    apply mp ax1 ax2
  | ax3 =>
    apply mp ax1 ax3
  | mp _ _ h_ih ha_ih =>
    simp_all
    apply mp (mp ax2 h_ih) ha_ih
  | distr =>
    apply mp ax1 distr
  | nec h _ =>
    apply mp ax1 (nec h)


lemma not_prove_cons {Γ : Set wff} {φ : wff} : (Γ ⊬ φ) → consistent Γ := by
  contrapose; simp; intro h
  have p1 : Γ ⊢ (~φ) ~> ~⊥ := mp ax1 reflexive
  have p2 : Γ ⊢ ((~φ) ~> ~⊥) ~> ⊥ ~> φ := ax3
  apply mp (mp p2 p1) h

lemma not_prove_cons_insert {Γ : Set wff} {φ : wff} : (Γ ⊬ φ) → consistent (insert (~φ) Γ) := by
  contrapose; simp; intro h
  have : Γ ⊢ ~φ ~> ⊥ := deduction h
  apply dne this

lemma cons_not_prove_contra {Γ : Set wff} {φ : wff} : consistent Γ → (Γ ⊬ φ) ∨ (Γ ⊬ ~φ) := by
  intro h
  apply byContradiction
  intro hnp; push_neg at hnp
  have ⟨hp, hnp⟩ := hnp
  have := mp hnp hp
  contradiction


end propositional
