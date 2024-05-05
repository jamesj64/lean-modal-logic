import Mathlib.Logic.Encodable.Basic
import Modal.Propositional.Syntax

import Mathlib.Tactic

namespace propositional

open wff

namespace encoding

@[reducible]
def wff_depth_n (n : Nat) := {φ : wff // depth φ ≤ n}

private lemma atom_or_bot_of_depth_zero (φ : wff_depth_n 0) : φ = Falsum ∨ ∃ n, φ = p n := by
  cases h : φ.1 <;> simp_all
  case Implies α β =>
    have := φ.2
    simp_all
  case Nec α =>
    have := φ.2
    rw [h] at this
    simp at this

private instance encodable_zero : Encodable (wff_depth_n 0) := by
  let f (φ : wff_depth_n 0) : Nat :=
    match φ.1 with
    | Atom n => n + 1
    | _ => 0
  let finv (n : Nat) : wff_depth_n 0 :=
    match n with
    | 0 => ⟨Falsum, by simp⟩
    | n => ⟨Atom (n - 1), by simp⟩
  have : ∀ x, finv (f x) = x := by
    intro φ
    simp [finv, f]
    split
    . case h_1 heq n =>
      split at n
      . case h_1 => simp_all
      . case h_2 ψ h =>
        have := atom_or_bot_of_depth_zero φ
        cases this with
        | inl =>
          have : ⟨φ.1, φ.2⟩ = φ := by simp
          simp_all
        | inr => simp_all
    . case h_2 n heq =>
      split at heq
      . case h_1 =>
        have : ⟨φ.1, φ.2⟩ = φ := by simp
        simp_all
      . case h_2 => simp_all
  apply Encodable.ofLeftInverse f finv this

private def f (n : Nat) : wff_depth_n (n + 1) → wff_depth_n 0 ⊕ wff_depth_n 0 ⊕ wff_depth_n n ⊕ (wff_depth_n n × wff_depth_n n) := λ φ => by
  cases h : φ.1 with
  | Atom n =>
    apply Sum.inl
    have : depth φ = 0 := by rw [h]; simp
    constructor
    simp
    assumption
  | Falsum =>
    apply Sum.inr
    apply Sum.inl
    have : depth φ = 0 := by rw [h]; simp
    constructor
    simp
    assumption
  | Implies α β =>
    let degp := φ.2
    rw [h] at degp
    simp at degp
    have : max (depth α) (depth β) ≤ n := by linarith
    have dal : depth α ≤ n := by simp_all
    have dbl : depth β ≤ n := by simp_all
    apply Sum.inr
    apply Sum.inr
    apply Sum.inr
    constructor
    . constructor
      apply dal
    . constructor
      apply dbl
  | Nec α =>
    let degp := φ.2
    rw [h] at degp
    simp at degp
    have : depth α ≤ n := by linarith
    apply Sum.inr
    apply Sum.inr
    apply Sum.inl
    constructor
    apply this

private def finv (n : Nat) : wff_depth_n 0 ⊕ wff_depth_n 0 ⊕ wff_depth_n n ⊕ (wff_depth_n n × wff_depth_n n) → wff_depth_n (n + 1) := λ h => by
  cases h with
  | inl φ =>
    have dp := φ.2
    have : depth φ.1 ≤ n + 1 := by linarith
    constructor
    exact this
  | inr h =>
    cases h with
    | inl φ =>
      have dp := φ.2
      have : depth φ.1 ≤ n + 1 := by linarith
      constructor
      exact this
    | inr h =>
      cases h with
      | inl φ =>
        have dp := φ.2
        have : depth (□ φ) ≤ n + 1 := by simp [depth]; linarith
        constructor
        exact this
      | inr h =>
        obtain ⟨α, β⟩ := h
        let m := depth (α ~> β)
        have mdepth : m = depth (α ~> β) := rfl
        simp at mdepth
        have : depth α ≤ n := α.2
        have : depth β ≤ n := β.2
        have : m ≤ n + 1 := by
          simp_all
          suffices max (depth α) (depth β) ≤ n by linarith
          simp_all
        constructor
        have : depth (α ~> β) ≤ n + 1 := by simp_all
        apply this

private def encodable_succ (n : Nat) (h : Encodable (wff_depth_n n)) : Encodable (wff_depth_n n.succ) := by
  suffices h : ∀ φ : wff_depth_n n.succ, finv n (f n φ) = φ by
    apply Encodable.ofLeftInverse (f n) (finv n) h
  intro φ
  simp [f, finv]
  cases φ with
  | mk φ _ =>
    cases φ <;> eq_refl

instance : Encodable wff := by
  let f (φ : wff) : Σ n, wff_depth_n n := by
    have : depth φ ≤ depth φ := le_refl (depth φ)
    constructor
    . constructor
      exact this
  let finv (h : Σ n, wff_depth_n n) : wff := by
    obtain ⟨_, φ⟩ := h
    exact φ.1
  suffices h : ∀ φ : wff, finv (f φ) = φ from
    have : Encodable ((n : ℕ) × wff_depth_n n) :=
      have (n : Nat) : Encodable (wff_depth_n n) :=
        Nat.recOn n encodable_zero encodable_succ
      Sigma.encodable
    Encodable.ofLeftInverse f finv h
  intro φ; rfl

end encoding

end propositional
