import Mathlib.Data.Set.Basic

universe u

namespace propositional

inductive wff : Type
| Atom : Nat → wff
| Falsum : wff
| Implies : wff → wff → wff
| Nec : wff → wff

open wff

notation "⊥" => Falsum
notation " p " => Atom
infixr:75 " ⊃ " => wff.Implies
infixr:80 " ~> " => wff.Implies
notation " ~ " φ:40 => φ ⊃ ⊥
prefix:95 "□" => Nec
prefix:95 "◇" => λ φ => ~ □ ~ φ


-- This definition of proof was heavily inspired by https://philpapers.org/archive/BENAHC-2.pdf
inductive proof : Set wff → wff → Prop
| ax {Γ} {α} (h : α ∈ Γ) : proof Γ α
| ax1 {Γ} {α β} : proof Γ (α ~> β ~> α)
| ax2 {Γ} {α β γ} : proof Γ ((α ~> β ~> γ) ~> (α ~> β) ~> (α ~> γ))
| ax3 {Γ} {α β} : proof Γ ((~α ~> ~β) ~> β ~> α)
| mp {Γ} {α β} (h : proof Γ (α ~> β)) (ha : proof Γ α) : proof Γ β
| nec {Γ} {α} (h : proof ∅ α) : proof Γ (□ α)
| distr {Γ} {α β} : proof Γ (□ (α ~> β) ~> □ α ~> □ β)

open proof

notation Γ " ⊢ " φ => proof Γ φ

lemma reflexive {Γ : Set wff} {φ : wff} : Γ ⊢ φ ~> φ :=
  have : Γ ⊢ (φ ~> φ ~> φ) ~> φ ~> φ := mp ax2 ax1
  mp this ax1


end propositional
