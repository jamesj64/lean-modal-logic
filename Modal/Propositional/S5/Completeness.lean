import Mathlib
import Modal.Propositional.S5.Syntax
import Modal.Propositional.S5.Semantics

universe u

namespace S5

namespace Completeness

open Classical

def Maximal (Γ : Set wff) := ∀ φ, φ ∈ Γ ∨ (~φ) ∈ Γ

def Maximally_Consistent (Γ : Set wff) := Maximal Γ ∧ Consistent Γ

-- proof theoretic "compactness"
theorem compact {Γ φ} (h : Γ ⊢ φ) : ∃ Δ : Finset wff, ↑Δ ⊆ Γ ∧ ↑Δ ⊢ φ := by
  induction h
  . case ax Γ φ mem =>
    existsi {φ}
    simp_all
    exact proof.ax (by simp)
  . case ax1 => existsi ∅; simp; exact proof.ax1
  . case ax2 => existsi ∅; simp; exact proof.ax2
  . case ax3 => existsi ∅; simp; exact proof.ax3
  . case mp Γ φ ψ _ _ ihimp ihp =>
    obtain ⟨Δ, ⟨dsub, dimp⟩⟩ := ihimp
    obtain ⟨Δ', ⟨d'sub, d'imp⟩⟩ := ihp
    existsi Δ ∪ Δ'
    simp_all
    have uimp : (↑Δ ∪ ↑Δ') ⊢ φ ~> ψ := by
      apply S5.monotonicity
      apply Set.subset_union_left
      assumption
    have up : (↑Δ ∪ ↑Δ') ⊢ φ := by
      apply S5.monotonicity
      apply Set.subset_union_right
      assumption
    exact proof.mp uimp up
  . case nec Γ φ hp _ =>
   existsi ∅
   simp
   exact proof.nec hp
  . case distr => existsi ∅; simp; exact proof.distr
  . case axT => existsi ∅; simp; exact proof.axT
  . case axB => existsi ∅; simp; exact proof.axB
  . case axS4 => existsi ∅; simp; exact proof.axS4


-- https://github.com/iehality/lean4-logic/blob/271e4ef1a22fa883e03d2a5abcbb3759da504db8/Logic/Vorspiel/Vorspiel.lean#L723
lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by simp [Set.insert_subset_iff] at h; exact h.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)


@[simp]
lemma lindenbaum {Γ : Set wff} (h : Consistent Γ) : ∃ Δ, Maximally_Consistent Δ ∧ Γ ⊆ Δ := by
  have : ∀ x ∈ {Γ | Consistent Γ}, ∃ m ∈ {Γ | Consistent Γ}, x ⊆ m ∧ ∀ a ∈ {Γ | Consistent Γ}, m ⊆ a → a = m := by
    apply zorn_subset_nonempty
    intro c csub isChain nonempty_c
    existsi (⋃₀ c)
    simp
    constructor
    . by_contra hnp
      obtain ⟨Δ, dsub, ndcons⟩ := compact hnp
      have := Finset.finite_toSet Δ
      have ⟨t, tc, tdsub⟩ : ∃ t ∈ c, ↑Δ ⊆ t := subset_mem_chain_of_finite c nonempty_c isChain this dsub
      have : Consistent t := csub tc
      absurd this
      apply S5.monotonicity tdsub ndcons
    . intro s hs
      exact Set.subset_sUnion_of_mem hs
  have ⟨Δ, hc, hsub, himp⟩ := this Γ h
  existsi Δ
  constructor
  . constructor
    . intro φ
      cases (cons_insert_either hc) with
      | inl h =>
        have := himp (insert φ Δ) h (by simp)
        simp_all
      | inr h =>
        have := himp (insert (~φ) Δ) h (by simp)
        simp_all
    . exact hc
  . assumption

namespace Canonical

  lemma cons_empty : Consistent ∅ := by
    intro hp
    have := Soundness hp
    simp_all
    apply this Nat 0
    constructor
    apply (λ (_ _ : Nat) => True)
    have equiva : Equivalence (λ (_ _ : Nat) => True) := by
      constructor
      repeat (intros; simp_all)
    apply equiva

  lemma max_cons_proves_in {Γ : Set wff} {φ : wff} (h : Maximally_Consistent Γ) (hp : Γ ⊢ φ) : φ ∈ Γ := by
    have ⟨maxm, cons⟩ := h
    cases (maxm φ) with
    | inl => assumption
    | inr hnp =>
      have : Γ ⊢ ⊥ := proof.mp (proof.ax hnp) hp
      contradiction

  @[simp]
  private def unbox (Γ : Set wff) := {γ | □ γ ∈ Γ}

  @[reducible]
  private def world := {w : Set wff // Maximally_Consistent w}

  @[reducible]
  private def val (w : world) (n : Nat) := p n ∈ w.1

  @[reducible]
  private def rel (w v : world) := ∀ φ, □ φ ∈ w.1 → φ ∈ v.1

  instance nonempty_worlds : Nonempty world := by
    have : ∃ Γ : Set wff, Consistent Γ := ⟨∅, cons_empty⟩
    have ⟨Γ, cons⟩ := this
    obtain ⟨Δ, max_cons, _⟩ := lindenbaum cons
    constructor
    have : world := ⟨Δ, max_cons⟩
    exact this

  instance equiv : Equivalence rel := by
    constructor
    . intro w φ bp
      have : ↑w ⊢ φ := proof.mp proof.axT (proof.ax bp)
      exact max_cons_proves_in w.2 this
    . intro w v wRv φ bp
      obtain ⟨maxw, _⟩ := w.2
      cases (maxw φ) with
      | inl hp => assumption
      | inr hnp =>
        have := max_cons_proves_in w.2 $ proof.mp proof.axB (proof.ax hnp)
        have a : (~□~~φ) ∈ v.1 := wRv _ this
        have : ↑v ⊢ □(φ ~> ~~φ) := proof.nec l1
        have := proof.mp (proof.ax a) $ proof.mp (proof.mp proof.distr this) (proof.ax bp)
        absurd v.2.2
        exact this
    . intro x y z xRy yRz φ bp
      have := xRy (□φ) (max_cons_proves_in x.2 $ proof.mp (proof.axS4) (proof.ax bp))
      exact yRz φ $ xRy (□φ) (max_cons_proves_in x.2 $ proof.mp (proof.axS4) (proof.ax bp))

  private def model : Model world := Model.mk rel val equiv


  lemma box_mem_of_unbox_prf {w : world} {φ : wff} (h : unbox w ⊢ φ) : (□φ) ∈ w.1 := by
    have ww := w.2
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
    | axT =>
      exact max_cons_proves_in ww (proof.nec proof.axT)
    | axB =>
      exact max_cons_proves_in ww (proof.nec proof.axB)
    | axS4 =>
      exact max_cons_proves_in ww (proof.nec proof.axS4)

  lemma truth_at_world_is_mem {φ : wff} : ∀ w : world, φ ∈ w.1 ↔ Model.satisfies model w φ := by
    induction φ with
    | Atom n =>
      intros
      constructor
      repeat (exact id)
    | Falsum =>
      intro w
      have ⟨_, cons⟩ := w.2
      simp_all
      by_contra hnp
      absurd cons
      apply proof.ax hnp
    | Implies φ ψ ihphi ihpsi =>
      intro w
      have ⟨maxm, cons⟩ := w.2
      constructor
      . intro h; simp; intro hp
        have := proof.mp (proof.ax h)
        cases (maxm φ) with
        | inl hpw =>
          exact (ihpsi w).mp (max_cons_proves_in w.2 (this (proof.ax hpw)))
        | inr hnphi =>
          have hphi := (ihphi w).mpr hp
          absurd cons
          apply proof.mp (proof.ax hnphi) (proof.ax hphi)
      . intro h; simp at h;
        cases (maxm φ) with
        | inl hp =>
          have := (ihpsi w).mpr (h ((ihphi w).mp hp))
          apply max_cons_proves_in w.2
          apply proof.mp proof.ax1 (proof.ax this)
        | inr hnp =>
          cases (maxm ψ) with
          | inl hpsi =>
            apply max_cons_proves_in w.2
            apply proof.mp proof.ax1 (proof.ax hpsi)
          | inr hnpsi =>
            apply max_cons_proves_in w.2
            apply proof.mp proof.ax3
            apply proof.mp proof.ax1 (proof.ax hnp)
    | Nec φ ih =>
      intro w
      have ⟨maxm, _⟩ := w.2
      constructor
      . intro h v wRv
        exact (ih v).mp (wRv φ h)
      . intro h; simp at h
        cases (maxm (□φ)) with
        | inl _ => assumption
        | inr hnp =>
          by_contra hnnp
          have := (box_mem_of_unbox_prf).mt hnnp
          have cons_insert := not_prove_cons_insert this
          have : ∀ φ : wff, □φ ∈ w.1 → φ ∈ unbox w := by simp [unbox]
          obtain ⟨Δ, max_cons, sub⟩ := lindenbaum cons_insert

          have : model.rel w ⟨Δ, max_cons⟩ := by
            intro f bp
            have := this f bp
            have : f ∈ insert (φ ~> ⊥) (unbox w) := Set.mem_insert_of_mem (φ ~> ⊥) this
            exact sub this

          have npg : (~φ) ∈ Δ := by
            have : (~φ) ∈ insert (φ ~> ⊥) (unbox w) := Set.mem_insert _ _
            exact sub this

          have gunsat := (ih ⟨Δ, max_cons⟩).mpr.mt (by
            by_contra hpg
            absurd max_cons.2
            exact proof.mp (proof.ax npg) (proof.ax hpg)
          )

          have := h Δ max_cons this

          contradiction

  variable {α : Type u} [n : Nonempty α]

  theorem completeness {Γ : Set wff} {φ : wff} : (Γ ⊨ₛ₅ φ) → Γ ⊢ φ := by
    by_contra hnp
    push_neg at hnp

    have ⟨gep, gnpp⟩ := hnp
    have cons := not_prove_cons_insert gnpp

    obtain ⟨Γ', max_cons, sub⟩ := lindenbaum cons

    have npg : (~φ) ∈ Γ' := by
      have : (~φ) ∈ insert (φ ~> ⊥) Γ := Set.mem_insert _ _
      exact sub this

    absurd (truth_at_world_is_mem ⟨Γ', max_cons⟩).mp npg

    simp at gep

    apply gep world ⟨Γ', max_cons⟩

    intro γ gg

    have : γ ∈ Γ' := by
      have : γ ∈ insert (φ ~> ⊥) Γ := Set.mem_insert_of_mem _ gg
      exact sub this

    exact (truth_at_world_is_mem ⟨Γ', max_cons⟩).mp this

end Canonical

end Completeness

end S5
