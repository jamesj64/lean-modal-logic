import Modal.Propositional.Syntax
import Modal.Propositional.Semantics
import Modal.Propositional.Encoding

import Mathlib.Data.Set.Lattice

namespace propositional

open Classical

open wff

open encoding

def code (φ : wff) : Nat := Encodable.encode φ

def maximal (Γ : Set wff) := ∀ φ, φ ∈ Γ ∨ (~φ) ∈ Γ

@[simp]
def max_cons (Γ : Set wff) := maximal Γ ∧ consistent Γ

@[simp]
def cons_insert (Γ : Set wff) (φ : wff) := if consistent (insert φ Γ) then insert φ Γ else insert (~φ) Γ

@[simp]
def max_con_n (Γ : Set wff) : Nat → Set wff
| 0 => Γ
| Nat.succ n =>
  match Encodable.decode n with
  | some φ => cons_insert (max_con_n Γ n) φ
  | none => max_con_n Γ n

def maximize (Γ : Set wff) : Set wff := ⋃ n, max_con_n Γ n

lemma sub_maximize {Γ : Set wff} : Γ ⊆ maximize Γ := by
  have sub₁ {n : Nat} : Γ ⊆ max_con_n Γ n := by
    induction n with
    | zero => simp; apply refl
    | succ n ih =>
      simp
      split
      . split
        repeat (intro γ gg; apply Set.subset_insert _ (max_con_n Γ n) (ih gg))
      . assumption

  have sub₂ {n : Nat} : max_con_n Γ n ⊆ maximize Γ :=
    Set.subset_iUnion (max_con_n Γ) n

  apply subset_trans (@sub₁ 0) sub₂

lemma ed {φ : wff} {n : Nat} (h : n = Encodable.encode φ) : Encodable.decode n = some φ := by simp_all

lemma all_mem_max {Γ : Set wff} : maximal (maximize Γ) := by
  intro φ
  let i := Encodable.encode φ
  simp [maximize]
  have : φ ∈ max_con_n Γ i.succ ∨ (~φ) ∈ max_con_n Γ i.succ := by
    have : Encodable.decode i = some φ := ed rfl
    simp
    split
    . case _ ψ heq =>
      split
      . rw [this] at heq
        have : φ = ψ := by simp_all
        rw [this]
        apply Or.inl (Set.mem_insert ψ (max_con_n Γ i))
      . rw [this] at heq
        have : φ = ψ := by simp_all
        rw [this]
        apply Or.inr (Set.mem_insert (~ψ) (max_con_n Γ i))
    . case _ ψ heq => simp_all
  apply byContradiction
  push_neg
  intro ⟨h₁, h₂⟩
  have := h₁ i.succ
  have := h₂ i.succ
  simp_all

lemma cons_max_con_n {Γ : Set wff} (h : consistent Γ) : ∀ n : Nat, consistent (max_con_n Γ n) := by
  intro n
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp_all
    intro hnp
    split at hnp
    . split at hnp
      . contradiction
      . case _ φ _ h =>
        have : (max_con_n Γ n ⊬ φ) ∨ max_con_n Γ n ⊬ ~φ := cons_not_prove_contra ih
        cases this with
        | inl np =>
          have := not_prove_cons_insert np
          contradiction
        | inr np =>
          simp at h
          have := deduction h
          contradiction
    . contradiction

lemma in_max_is_in_max_n {Γ : Set wff} {φ : wff} : φ ∈ maximize Γ → ∃ n, φ ∈ max_con_n Γ n := Set.mem_iUnion.1

lemma max_con_n_mono {Γ : Set wff} {m n : Nat} (h : m ≤ n) : max_con_n Γ m ⊆ max_con_n Γ n := by
  induction h
  . rfl
  . simp_all
    split
    . split
      . apply subset_trans
        assumption
        apply Set.subset_insert
      . apply subset_trans
        assumption
        apply Set.subset_insert
    . assumption

lemma max_big_stronger {Γ : Set wff} {φ : wff} {m n : Nat} (h : m ≤ n) (hp : max_con_n Γ m ⊢ φ) : max_con_n Γ n ⊢ φ :=
  have : max_con_n Γ m ⊆ max_con_n Γ n := max_con_n_mono h
  monotonicity this hp

lemma max_proves_max_n_proves {Γ : Set wff} {φ : wff} (h : maximize Γ ⊢ φ) : ∃ n, max_con_n Γ n ⊢ φ := by
  generalize eq : maximize Γ = Γ'; rw [eq] at h
  induction h with
  subst eq
  | ax h =>
    have ⟨n, hp⟩ := in_max_is_in_max_n h
    constructor
    apply proof.ax hp
  | ax1 =>
    constructor
    apply proof.ax1
    apply 0
  | ax2 =>
    constructor
    apply proof.ax2
    apply 0
  | ax3 =>
    constructor
    apply proof.ax3
    apply 0
  | mp h hp ih₁ ih₂ =>
    have := proof.mp h hp
    have nab := by apply ih₁; apply refl
    have na := by apply ih₂; apply refl
    have ⟨n, ab⟩ := nab
    have ⟨m, a⟩ := na
    cases (max_cases m n) with
    | inl mc =>
      have ⟨_, nlem⟩ := mc
      have := max_big_stronger nlem ab
      constructor
      apply proof.mp this a
    | inr mc =>
      have ⟨_, nlem⟩ := mc
      have nlem : m ≤ n := Nat.le_of_lt nlem
      have := max_big_stronger nlem a
      constructor
      apply proof.mp ab this
  | nec h =>
    constructor
    apply proof.nec h
    apply 0
  | distr =>
    constructor
    apply proof.distr
    apply 0

lemma cons_max_of_cons {Γ : Set wff} (h : consistent Γ) : consistent (maximize Γ) := by
  intro hnp
  have := max_proves_max_n_proves hnp
  have := cons_max_con_n h
  simp_all

lemma max_cons_of_cons {Γ : Set wff} (h : consistent Γ) : max_cons (maximize Γ) := by
  constructor
  apply all_mem_max
  apply cons_max_of_cons h


lemma cons_empty : consistent ∅ := by
  intro hp
  have := soundness hp
  simp at this
  let f : Frame := Frame.mk (Set.singleton (Set.singleton (p 0))) (Set.nonempty_of_mem (Set.mem_singleton (Set.singleton (p 0)))) (λ _ _ => False)
  have m : f.Model := Frame.Model.mk f (λ _ _ => True)
  have := this f m (Set.singleton (p 0))
  simp_all
  have := Set.mem_singleton (Set.singleton (p 0))
  contradiction

private def worlds : Set world := {w | max_cons w}

def val (w : Set wff) (n : Nat) : Prop := w ∈ worlds ∧ p n ∈ w

def rel (w : Set wff) (v : Set wff) : Prop := ∀ φ : wff, □φ ∈ w → φ ∈ v

instance nonempty_worlds : Set.Nonempty worlds := by
  have : ∃ Γ : Set wff, consistent Γ := ⟨∅, cons_empty⟩
  have ⟨Γ, cons⟩ := this
  have := max_cons_of_cons cons
  have : maximize Γ ∈ worlds := by
    simp [worlds]
    have : maximize Γ ∈ {w | maximal w ∧ ¬w ⊢ ⊥} := by simp_all
    exact this
  apply Set.nonempty_of_mem this

private def frame : Frame := Frame.mk worlds nonempty_worlds rel
private def model : frame.Model := Frame.Model.mk frame val


lemma closed_max_cons {Γ : Set wff} {φ ψ : wff} (h : max_cons Γ) (hen : {φ} ⊢ ψ) (hp : φ ∈ Γ) : ψ ∈ Γ := by
  have himp : ⊢ φ ~> ψ := by
    have : ({φ} : Set wff) = insert φ ∅ := by simp_all
    rw [this] at hen
    apply deduction hen
  simp at h
  have ⟨maxm, cons⟩ := h
  cases (maxm ψ) with
  | inl => assumption
  | inr hnp =>
    have gpp : Γ ⊢ φ := proof.ax hp
    have gpimp : Γ ⊢ φ ~> ψ := monotonicity (by simp) himp
    have : Γ ⊢ ψ := proof.mp gpimp gpp
    absurd proof.mp (proof.ax hnp) this
    apply cons

lemma max_cons_proves_in {Γ : Set wff} {φ : wff} (h : max_cons Γ) (hp : Γ ⊢ φ) : φ ∈ Γ := by
  have ⟨maxm, cons⟩ := h
  cases (maxm φ) with
  | inl => assumption
  | inr hnp =>
    have : Γ ⊢ ⊥ := proof.mp (proof.ax hnp) hp
    contradiction

def unbox (Γ : Set wff) : Set wff := {γ | □γ ∈ Γ}

lemma box_mem_of_unbox_prf {w : world} {φ : wff} (ww : w ∈ frame.worlds) (h : unbox w ⊢ φ) : (□ φ) ∈ w := by
  generalize eq : unbox w = Γ; rw [eq] at h
  induction h with
  subst eq
  | ax h =>
    simp [unbox] at h
    assumption
  | ax1 =>
    exact max_cons_proves_in ww (proof.nec proof.ax1)
  | ax2 =>
    exact max_cons_proves_in ww (proof.nec proof.ax2)
  | ax3 =>
    exact max_cons_proves_in ww (proof.nec proof.ax3)
  | mp hab ha iha ihab =>
    have ab := proof.ax (iha rfl)
    have a := proof.ax (ihab rfl)
    have := proof.mp (proof.mp (proof.distr) ab) a
    exact max_cons_proves_in ww this
  | nec h _ =>
    have hbb := @proof.nec ∅ _ (@proof.nec ∅ _ h)
    exact max_cons_proves_in ww (monotonicity (by simp_all) hbb)
  | distr =>
    exact max_cons_proves_in ww (proof.nec proof.distr)

lemma truth_at_world_is_mem {φ : wff} : ∀ w ∈ frame.worlds, φ ∈ w ↔ Model.satisfies model w φ := by
  induction φ with
  | Atom n =>
    intros
    constructor
    . intro h
      constructor
      repeat (assumption)
    . intro h
      simp at h
      apply h.2
  | Falsum =>
    intro _ ww
    have ⟨_, cons⟩ := ww
    simp_all
    by_contra hnp
    absurd cons
    apply proof.ax hnp
  | Implies φ ψ ihphi ihpsi =>
    intro w ww
    have ⟨maxm, cons⟩ := ww
    constructor
    . intro h; simp; intro hp
      have := proof.mp (proof.ax h)
      cases (maxm φ) with
      | inl hpw =>
        exact (ihpsi w ww).mp $ max_cons_proves_in ww (this (proof.ax hpw))
      | inr hnphi =>
        have hphi := (ihphi w ww).mpr hp
        absurd cons
        apply proof.mp (proof.ax hnphi) (proof.ax hphi)
    . intro h; simp at h;
      cases (maxm φ) with
      | inl hp =>
        have := (ihpsi w ww).mpr $ h ((ihphi w ww).mp hp)
        apply max_cons_proves_in ww
        apply proof.mp proof.ax1 (proof.ax this)
      | inr hnp =>
        cases (maxm ψ) with
        | inl hpsi =>
          apply max_cons_proves_in ww
          apply proof.mp proof.ax1 (proof.ax hpsi)
        | inr hnpsi =>
          apply max_cons_proves_in ww
          apply proof.mp proof.ax3
          apply proof.mp proof.ax1 (proof.ax hnp)
    | Nec φ ih =>
      intro w ww
      have ⟨maxm, _⟩ := ww
      constructor
      . intro h v vw wRv
        exact (ih v vw).mp (wRv φ h)
      . intro h; simp at h
        cases (maxm (□φ)) with
        | inl _ => assumption
        | inr hnp =>
          by_contra hnnp
          have := not_prove_cons_insert $ (box_mem_of_unbox_prf ww).mt hnnp

          have : ∀ φ : wff, □φ ∈ w → φ ∈ unbox w := by simp [unbox]
          generalize eq : maximize (insert (φ ~> ⊥) (unbox w)) = Γ

          have wRΓ : frame.rel w Γ := by
            intro f bp
            have : f ∈ insert (φ ~> ⊥) (unbox w) := Set.mem_insert_of_mem (φ ~> ⊥) (this f bp)
            have : f ∈ maximize (insert (φ ~> ⊥) (unbox w)) := (@sub_maximize (insert (φ ~> ⊥) (unbox w))) this
            subst eq; assumption

          have max_c_g : max_cons Γ := by
            subst eq
            apply max_cons_of_cons
            assumption

          absurd h Γ (max_c_g) wRΓ

          have npg : (~φ) ∈ Γ := by
            have : (~φ) ∈ insert (φ ~> ⊥) (unbox w) := Set.mem_insert _ _
            have := (@sub_maximize (insert (φ ~> ⊥) (unbox w))) this
            subst eq; assumption

          apply (ih Γ max_c_g).mpr.mt

          by_contra hpg

          absurd max_c_g.2

          exact proof.mp (proof.ax npg) (proof.ax hpg)


theorem completeness {Γ : Set wff} {φ : wff} : (Γ ⊨ φ) → Γ ⊢ φ := by
  by_contra hnp
  push_neg at hnp

  have ⟨gep, gnpp⟩ := hnp
  have cons := not_prove_cons_insert gnpp

  generalize eq : maximize (insert (~φ) Γ) = Γ'
  have max_cons := max_cons_of_cons cons
  have ⟨maxm, _⟩ := max_cons
  rw [eq] at maxm max_cons


  have npg : (~φ) ∈ Γ' := by
    have : (~φ) ∈ insert (φ ~> ⊥) Γ := Set.mem_insert _ _
    have := (@sub_maximize (insert (φ ~> ⊥) Γ)) this
    subst eq; assumption

  absurd (truth_at_world_is_mem Γ' max_cons).mp npg

  apply gep frame model Γ' max_cons

  intro γ gg

  have : γ ∈ Γ' := by
    have : γ ∈ insert (φ ~> ⊥) Γ := Set.mem_insert_of_mem _ gg
    have := (@sub_maximize (insert (φ ~> ⊥) Γ)) this
    subst eq; assumption

  exact (truth_at_world_is_mem Γ' max_cons).mp this

end propositional
