import Mathlib

/-!
# Common definitions

Shared notation for the formalizations accompanying the paper
*Solutions to several problems on infinite sumset configurations*.
-/

namespace Kmrr25

/-- The sumset `B + C = {b + c | b ∈ B, c ∈ C}` of two sets in an additive structure. -/
def sumset {α : Type*} [Add α] (B C : Set α) : Set α := {x | ∃ b ∈ B, ∃ c ∈ C, x = b + c}

end Kmrr25
