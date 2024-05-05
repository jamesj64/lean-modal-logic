import Modal.Propositional.Syntax

universe u

open Classical

namespace propositional

open wff


-- Definitions of Kripke frames / models

@[reducible]
def world := Set wff

structure Frame : Type where
  worlds : Set world
  nonempty : worlds.Nonempty
  rel : world → world → Prop

abbrev Frame.Reflexive (F : Frame) := ∀ w ∈ F.worlds, F.rel w w

abbrev Frame.Symmetric (F : Frame) := ∀ w ∈ F.worlds, ∀ v ∈ F.worlds, F.rel w v → F.rel v w

abbrev Frame.Transitive (F : Frame) := ∀ x ∈ F.worlds, ∀ y ∈ F.worlds, ∀ z ∈ F.worlds, F.rel x y → F.rel y z → F.rel x z

def Frame.Equivalence (F : Frame) := F.Reflexive ∧ F.Symmetric ∧ F.Transitive

abbrev TFrame := {F : Frame // F.Reflexive}

abbrev S5Frame := {F : Frame // F.Equivalence}

structure Frame.Model {f : Frame} extends Frame where
  val : world → Nat → Prop



-- Truth in a model and other semantic notions

@[simp]
def Model.satisfies {F : Frame} (M : F.Model) (w : world) (φ : wff) : Prop :=
  match φ with
  | Atom n => M.val w n
  | ⊥ => False
  | φ ~> ψ => Model.satisfies M w φ → Model.satisfies M w ψ
  | □ φ => ∀ w' ∈ F.worlds, F.rel w w' → Model.satisfies M w' φ

def Model.satisfies_set {F : Frame} (M : F.Model) (w : world) (Γ : Set wff) : Prop :=
  ∀ φ ∈ Γ, Model.satisfies M w φ

@[simp]
def sem_cons (Γ : Set wff) (φ : wff) : Prop :=
  ∀ (F : Frame) (M : F.Model), ∀ w ∈ F.worlds, (∀ γ ∈ Γ, Model.satisfies M w γ) → Model.satisfies M w φ

@[simp]
def sem_cons_s5 (Γ : Set wff) (φ : wff) : Prop :=
  ∀ (F : S5Frame) (M : F.1.Model), ∀ w ∈ F.1.worlds, (∀ γ ∈ Γ, Model.satisfies M w γ) → Model.satisfies M w φ


notation Γ "⊨" φ => sem_cons Γ φ
notation Γ "⊭" φ => ¬ sem_cons Γ φ

notation Γ "⊨ₛ₅" φ => sem_cons_s5 Γ φ
notation Γ "⊭ₛ₅" φ => ¬ sem_cons_s5 Γ φ

@[simp]
lemma sem_cons_s5_mono {Γ Δ: Set wff} {φ : wff} (sub : Γ ⊆ Δ) (h : Γ ⊨ₛ₅ φ) : Δ ⊨ₛ₅ φ := by
  intro F M w ww msd
  simp at h
  apply h F F.2 M w ww
  intro γ gg
  apply msd γ $ sub gg


@[simp]
def Frame.valid {F : Frame} (φ : wff) :=
  ∀ M : F.Model, ∀ w ∈ F.worlds, Model.satisfies M w φ

@[simp]
def valid (φ : wff) := ∀ F : Frame, F.valid φ

@[simp]
def valid_t (φ : wff) := ∀ F : TFrame, F.1.valid φ

@[simp]
def valid_s5 (φ : wff) := ∀ F : S5Frame, F.1.valid φ

prefix:50 " ⊨ " => valid

prefix:50 " ⊨ₜ " => valid_t

prefix:50 " ⊨ₛ₅ " => valid_s5


-- Some results

theorem modus_ponens {φ ψ : wff} : ⊨ (φ ~> ψ) → ⊨ φ → ⊨ ψ := by
  intro himp hp
  simp [valid, Frame.valid] at *
  intro F M w ww
  exact (himp F M w ww) (hp F M w ww)

theorem distribution {φ ψ : wff} : ⊨ □ (φ ~> ψ) ~> □ φ ~> □ ψ := by
  simp
  intro F M w _ h hp v vw wRv
  have := hp v vw wRv
  exact (h v vw wRv) this

theorem necessitation {φ : wff} : ⊨ φ → ⊨ □ φ := by simp_all

example {φ : wff} : ⊨ₜ □ φ ~> φ := by
  simp
  intro F R M w ww h
  have refl := R w ww
  apply h w ww refl

example {φ : wff} (h : ⊨ₜ □ φ) : ⊨ₜ φ := by
  simp_all
  intro F R M w ww
  have refl := R w ww
  exact h F R M w ww w ww refl

@[simp]
theorem B {φ : wff} : ⊨ₛ₅ φ ~> □◇φ := by
  simp
  intro F equiv M w ww hp v vw wRv
  have := equiv.2.1 w ww v vw wRv
  simp at this
  constructor
  . constructor
    . exact this
    . exact And.intro ww hp

@[simp]
theorem S4 {φ : wff} : ⊨ₛ₅ □ φ ~> □□φ := by
  simp
  intro F equiv M w ww h v vw wRv u uw vRu
  have := equiv.2.2 _ ww _ vw _ uw wRv vRu
  exact h u uw this


theorem soundness {Γ : Set wff} {φ : wff} : (Γ ⊢ φ) → Γ ⊨ φ := by
  intro hp; induction hp <;> try (repeat intro); simp_all


end propositional
