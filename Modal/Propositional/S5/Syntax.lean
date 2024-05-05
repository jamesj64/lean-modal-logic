import Mathlib.Data.Set.Basic

universe u

namespace S5

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
| axT {Γ} {α} : proof Γ (□ α ~> α)
| axB {Γ} {α} : proof Γ (α ~> □◇α)
| axS4 {Γ} {α} : proof Γ (□α ~> □□α)

inductive proofK : Set wff → wff → Prop
| ax {Γ} {α} (h : α ∈ Γ) : proofK Γ α
| ax1 {Γ} {α β} : proofK Γ (α ~> β ~> α)
| ax2 {Γ} {α β γ} : proofK Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
| ax3 {Γ} {α β} : proofK Γ (((~α) ~> (~β)) ~> (β ~> α))
| mp {Γ} {α β} (h : proofK Γ (α ~> β)) (ha : proofK Γ α) : proofK Γ β
| nec {Γ} {α} (h : proofK ∅ α) : proofK Γ (□ α)
| distr {Γ} {α β} : proofK Γ (□ (α ~> β) ~> □ α ~> □ β)

open proof

notation Γ " ⊢ " φ => proof Γ φ
notation Γ " ⊬ " φ => ¬ proof Γ φ
notation " ⊢ " φ => proof ∅ φ
notation " ⊬ " φ => ¬ proof ∅ φ

notation Γ " ⊢ₖ " φ => proofK Γ φ
notation Γ " ⊬ₖ " φ => ¬ proofK Γ φ
notation " ⊢ₖ " φ => proofK ∅ φ
notation " ⊬ₖ " φ => ¬ proofK ∅ φ

lemma reflexive {Γ : Set wff} {φ : wff} : Γ ⊢ φ ⊃ φ :=
  have : Γ ⊢ (φ ~> φ ~> φ) ~> φ ~> φ := mp ax2 ax1
  mp this ax1

@[simp]
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
  | axT => apply axT
  | axB => apply axB
  | axS4 => apply axS4

@[reducible]
def Consistent (Γ : Set wff) := Γ ⊬ ⊥

@[simp]
lemma cons_sub {Γ Δ : Set wff} (sub : Γ ⊆ Δ) (h : Consistent Δ) : Consistent Γ := by
  apply (monotonicity sub).mt
  simp_all


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

@[simp]
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
  | axT =>
    apply mp ax1 axT
  | axB =>
    apply mp ax1 axB
  | axS4 =>
    apply mp ax1 axS4


lemma not_prove_cons {Γ : Set wff} {φ : wff} : (Γ ⊬ φ) → Consistent Γ := by
  contrapose; simp; intro h
  have p1 : Γ ⊢ (~φ) ~> ~⊥ := mp ax1 reflexive
  have p2 : Γ ⊢ ((~φ) ~> ~⊥) ~> ⊥ ~> φ := ax3
  apply mp (mp p2 p1) h

lemma not_prove_cons_insert {Γ : Set wff} {φ : wff} : (Γ ⊬ φ) → Consistent (insert (~φ) Γ) := by
  contrapose; simp; intro h
  have : Γ ⊢ ~φ ~> ⊥ := deduction h
  apply dne this

lemma cons_not_prove_contra {Γ : Set wff} {φ : wff} : Consistent Γ → (Γ ⊬ φ) ∨ (Γ ⊬ ~φ) := by
  intro h
  apply byContradiction
  intro hnp; push_neg at hnp
  have ⟨hp, hnp⟩ := hnp
  have := mp hnp hp
  contradiction

lemma cons_insert_either {Γ : Set wff} (h : Consistent Γ) : Consistent (insert φ Γ) ∨ Consistent (insert (~φ) Γ) := by
  have : (Γ ⊬ φ) ∨ (Γ ⊬ ~φ) := cons_not_prove_contra h
  cases (this) with
  | inl hnp =>
    apply Or.inr (not_prove_cons_insert hnp)
  | inr hnp =>
    apply Or.inl (deduction.mt hnp)

def subst := Nat → wff

@[simp]
def substitute (s : subst) : wff → wff
| p n => s n
| Falsum => Falsum
| φ ~> ψ => substitute s φ ~> substitute s ψ
| □φ => □ substitute s φ

def bind (f : subst) (a : Nat) (b : wff) : subst :=
  λ n => if n = a then b else f a

def m_sub : subst :=
  have base := λ n => p n
  bind base 1 (□ p 1)


end S5
