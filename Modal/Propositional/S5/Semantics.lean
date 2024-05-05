import Modal.Propositional.S5.Syntax

universe u

namespace S5

variable {world : Type} [Nonempty world]

@[reducible]
structure Model (world : Type) [Nonempty world] where
  rel : world → world → Prop
  val : world → ℕ → Prop
  equiv : Equivalence rel

open wff

@[simp]
def Model.satisfies (M : Model world) (w : world) (φ : wff) : Prop :=
  match φ with
  | Atom n => M.val w n
  | ⊥ => False
  | φ ~> ψ => Model.satisfies M w φ → Model.satisfies M w ψ
  | □ φ => ∀ w' : world, M.rel w w' → Model.satisfies M w' φ


@[simp]
def sem_cons (Γ : Set wff) (φ : wff) : Prop :=
  ∀ world : Type, (h : Nonempty world) → ∀ (M : Model world) w, (∀ γ ∈ Γ, Model.satisfies M w γ) → Model.satisfies M w φ


notation Γ "⊭" φ => ¬ sem_cons Γ φ
notation:50 Γ " ⊨ₛ₅ " φ => sem_cons Γ φ


@[simp]
def valid (φ : wff) :=
  ∀ (M : Model world) w, Model.satisfies M w φ


theorem Soundness {Γ : Set wff} {φ : wff} : (Γ ⊢ φ) → Γ ⊨ₛ₅ φ := by
  intro hp; intros; induction hp <;> try (repeat intro); simp_all;
  case mp a b _ _ e f g h i j k =>
    have := j e h g h k
    exact i e h g h k this
  case nec a b _ d e f g h i _ _ =>
    exact i d h f h
  case axT a b c d e _ g =>
    exact g e $ d.equiv.refl e
  case axB a b c d _ f g h i =>
    absurd f
    exact i d $ c.equiv.symm h
  case axS4 a b c d _ f g h i j =>
    exact h g (c.equiv.trans i j)
end S5
