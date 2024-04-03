import Modal.Propositional.Syntax
import Modal.Propositional.Semantics

import Mathlib.Data.Set.Lattice

namespace propositional

open Classical

open wff

def max (Γ : Set wff) := ∀ φ, φ ∈ Γ ∨ (~φ) ∈ Γ

def max_cons (Γ : Set wff) := max Γ ∧ consistent Γ

@[simp]
def cons_insert (Γ : Set wff) (φ : wff) := if consistent (insert φ Γ) then insert φ Γ else insert (~φ) Γ

@[simp]
def max_con_n (Γ : Set wff) : Nat → Set wff
| 0 => Γ
| Nat.succ n => cons_insert (max_con_n Γ n) (Atom n)

def maximize (Γ : Set wff) : Set wff := ⋃ n, max_con_n Γ n

lemma sub_maximize {Γ : Set wff} : Γ ⊆ maximize Γ := by
  have sub₁ {n : Nat} : Γ ⊆ max_con_n Γ n := by
    induction n with
    | zero => simp; apply refl
    | succ n ih =>
      simp
      split
      repeat (intro x xg; simp; apply Or.inr (ih xg))

  have sub₂ {n : Nat} : max_con_n Γ n ⊆ maximize Γ :=
    Set.subset_iUnion (max_con_n Γ) n

  apply subset_trans (@sub₁ 0) sub₂

lemma all_mem_max {Γ : Set wff} {n : Nat} : p n ∈ maximize Γ ∨ (~p n) ∈ maximize Γ := by
  have h : p n ∈ max_con_n Γ n.succ ∨ (~ p n) ∈ max_con_n Γ n.succ := by
    induction n with
    | zero =>
      simp
      split
      . apply Or.inr
        apply (Set.mem_insert (~ p 0) Γ)
      . apply Or.inl
        apply (Set.mem_insert (p 0) Γ)
    | succ n _ =>
      simp
      split
      . split
        . apply Or.inr
          apply (Set.mem_insert (~ p n.succ))
        . apply Or.inl
          apply (Set.mem_insert (p n.succ))
      . split
        . apply Or.inr
          apply (Set.mem_insert (~ p n.succ))
        . apply Or.inl
          apply (Set.mem_insert (p n.succ))

  have := Set.subset_iUnion (max_con_n Γ) n.succ
  apply Or.elim h
  . intro hp; constructor; apply this hp
  . intro hp; apply Or.inr; apply this hp



theorem completeness {Γ : Set wff} {φ : wff} : (Γ ⊨ φ) → Γ ⊢ φ := by
  apply byContradiction; intro hnp
  push_neg at hnp
  have ⟨gep, gnpp⟩ := hnp
  have cons := not_prove_cons_insert gnpp
  sorry





end propositional
