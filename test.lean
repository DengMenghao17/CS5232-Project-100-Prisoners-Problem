import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic

/-!
Smoke test for the 100 prisoners project.

This file checks only the Lean/mathlib environment needed for the project.
It does not use Veil, Velvet, LoVe, or the course case-study libraries.
-/

namespace PrisonersSmokeTest

/-- Prisoners and drawers are both represented by `Fin 100`. -/
abbrev Person := Fin 100

/-- A room state is a permutation of the 100 drawer labels. -/
abbrev RoomState := Equiv.Perm Person

/-- Following the pointer for `t` steps means applying the permutation `t` times. -/
def follow (π : RoomState) (i : Person) (t : Nat) : Person :=
  (π ^ t) i

/-- Prisoner `i` succeeds if they return to `i` within 50 positive steps. -/
def PrisonerSuccess (π : RoomState) (i : Person) : Prop :=
  ∃ t : Nat, 1 ≤ t ∧ t ≤ 50 ∧ (π ^ t) i = i

/-- The strategy succeeds if every prisoner succeeds. -/
def StrategySuccess (π : RoomState) : Prop :=
  ∀ i : Person, PrisonerSuccess π i

/-
Basic checks: identity permutation, permutation powers, and simple tactics.
-/

example (π : RoomState) (i : Person) : follow π i 0 = i := by
  simp [follow]

example (π : RoomState) (i : Person) : follow π i 1 = π i := by
  simp [follow]

example (i : Person) : PrisonerSuccess (1 : RoomState) i := by
  refine ⟨1, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [PrisonerSuccess]

example : StrategySuccess (1 : RoomState) := by
  intro i
  refine ⟨1, ?_, ?_, ?_⟩
  · decide
  · decide
  · simp [PrisonerSuccess]

/-
Library checks: these commands should elaborate if the relevant mathlib modules
are available.
-/

#check Equiv.Perm
#check Equiv.Perm.cycleOf
#check Equiv.Perm.cycleFactors
#check Equiv.Perm.cycleFactorsFinset
#check Equiv.Perm.cycleType
#check Equiv.Perm.partition

#check Fintype.card
#check Finset.card
#check List.length

/-- A direct check that `cycleOf` can be applied to our project type. -/
def cycleOfTest (π : RoomState) (i : Person) : Equiv.Perm Person :=
  π.cycleOf i

/-- A direct check that `cycleType` can be applied to our project type. -/
def cycleTypeTest (π : RoomState) :=
  π.cycleType

end PrisonersSmokeTest
