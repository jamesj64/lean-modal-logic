-- This paper demonstrates the soundness and completeness of a similar embedding of Higher-Order Modal Logic into Simple Type Theory.
-- https://arxiv.org/pdf/0905.2435.pdf

open Classical

universe u v

namespace Quantified

set_option quotPrecheck false

-- i is the type of individuals
-- μ is the type of worlds
variable {i : Type u} {μ : Type v}

variable (R : μ → μ → Prop)
variable (φ ψ : μ → Prop)
variable (Φ : i → μ → Prop)
variable (w w' : μ)
variable (x y : i)

@[simp]
def mNot := ¬(φ w)

@[simp]
def mImpl := φ w → ψ w

@[simp]
def mAnd := φ w ∧ ψ w

@[simp]
def mOr := φ w ∨ ψ w

@[simp]
def box := ∀ w', R w w' → φ w'

@[simp]
def box₂ (x : i) (w : μ) := ∀ w', R w w' → Φ x w'

@[simp]
def dia := ∃ w', R w w' ∧ φ w'

-- "Constant domain" quantifiers
@[simp]
def mForall := ∀ x : i, Φ x w

@[simp]
def mExists := ∃ x : i, Φ x w

prefix:80 " ∀' " => mForall
prefix:80 " ∃' " => mExists

@[simp]
def mIdentity := λ _ : μ => x = y

prefix:max " ~ " => mNot

infixr:60 " ⊃ " => mImpl

prefix:80 " □ " => box R

prefix:80 " □₂ " => box₂ R

prefix:80 " ◇ " => dia R

infixr:70 " ≃ " => mIdentity

@[simp]
def reflexive := ∀ x, R x x

@[simp]
def symmetric := ∀ {x y}, R x y → R y x

@[simp]
def transitive := ∀ {x y z}, R x y → R y z → R x z

@[simp]
def valid := ∀ w, φ w

prefix:40 " ⊨ " => valid

@[simp]
def validT := reflexive R → valid φ

@[simp]
def validS5 := reflexive R → symmetric R → transitive R → valid φ

prefix:40 " ⊨ₜ " => validT R

prefix:40 " ⊨ₛ₅ " => validS5 R

example : ⊨ ∀' (λ (_ : i) (_ : μ) => True) := by simp_all

example : ⊨ φ ⊃ φ := by simp

example (h : reflexive R) : ⊨ □ φ ⊃ φ := by simp_all

example : ⊨ₜ □□φ ⊃ φ := by
  simp
  intro r w h
  exact h w (r w) w (r w)

example : ⊨ₛ₅ φ ⊃ □◇φ := by
  simp
  intro _ s _ w hw w' wRw'
  constructor
  constructor
  exact s wRw'
  assumption


example : ⊨ ∀'□₂Φ ⊃ □∀'Φ := by simp_all

example : ⊨ □∀'Φ ⊃ ∀'□₂Φ := by simp_all

example : ⊨ ∃' (λ (x : i) (w : μ) => mIdentity x x w) := by
  simp_all
  intro
  constructor
  trivial
  trivial

example : ⊨ₛ₅ □∀'(λ (x : i) (w : μ) => (□∃'(λ (y : i) (w' : μ) => mIdentity x y w')) w) := by simp_all



end Quantified
