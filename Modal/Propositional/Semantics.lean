import Modal.Propositional.Syntax

universe u

open Classical

namespace propositional

open wff


-- Definitions of Kripke frames / models
def world := Set wff

structure Frame : Type where
  worlds : Set world
  nonempty : worlds.Nonempty
  rel : world → world → Prop

def TFrame := {F : Frame // Reflexive F.rel}

def S5Frame := {F : Frame // Equivalence F.rel}

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


@[simp]
def sem_cons (Γ : Set wff) (φ : wff) : Prop :=
  ∀ (F : Frame) (M : F.Model), ∀ w ∈ F.worlds, (∀ γ ∈ Γ, Model.satisfies M w γ) → Model.satisfies M w φ

@[simp]
def sem_cons_s5 (Γ : Set wff) (φ : wff) : Prop :=
    ∀ (F : S5Frame) (M : F.1.Model), ∀ w ∈ F.1.worlds, (∀ γ ∈ Γ, Model.satisfies M w γ) → Model.satisfies M w φ


notation Γ "⊨" φ => sem_cons Γ φ
notation Γ "⊭" φ => ¬ sem_cons Γ φ

notation Γ "⊨ₛ₅" φ => sem_cons_s5 Γ φ
notation Γ "⊭ₛ₅" φ => sem_cons_s5 Γ φ


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
  intro F M w ww h
  have refl := F.2 w
  apply h w ww refl

example {φ : wff} (h : ⊨ₜ □ φ) : ⊨ₜ φ := by
  simp_all
  intro F M w ww
  have refl := F.2 w
  exact h F M w ww w ww refl

theorem B {φ : wff} : ⊨ₛ₅ φ ~> □◇φ := by
  simp
  intro F M w ww hp v _ wRv
  have := Equivalence.symm F.2 wRv
  constructor
  . constructor
    . exact this
    . exact And.intro ww hp

theorem S4 {φ : wff} : ⊨ₛ₅ □ φ ~> □□ φ := by
  simp
  intro F M w _ h v _ wRv u uw vRu
  have := Equivalence.trans F.2 wRv vRu
  exact h u uw this


-- That this works honestly amazes me.
theorem soundness {Γ : Set wff} {φ : wff} : (Γ ⊢ φ) → Γ ⊨ φ := by
  intro hp; induction hp <;> simp_all


end propositional
