import Mathlib.Data.Vector.Basic

namespace language

universe u

structure Language : Type (u + 1) where
  func : Nat → Type u
  rel : Nat → Type u

abbrev Language.constants (L : Language) := L.func 0

variable (L : Language.{u}) {arity : Nat}

namespace term

inductive Preterm : Nat → Type u
| Var (_ : Nat) : Preterm 0
| Func {arity : Nat} (_ : L.func arity) : Preterm arity
| App {arity : Nat} (_ : Fin arity → Preterm 0) (_ : Preterm 0) : Preterm arity

@[reducible]
def Term := Preterm L 0

inductive Preformula

end term

end language
