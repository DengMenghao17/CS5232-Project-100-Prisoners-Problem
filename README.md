# Formal Verification of the 100 Prisoners Problem

This project formalises the structural core of the 100 prisoners problem in Lean 4. The room state is modelled as a permutation of `Fin 100`, and the pointer-following strategy is specified as repeated application of this permutation. The main result proves that the strategy succeeds for all prisoners exactly when all formal cycles have length at most 50.

## Files

`test.lean` is a small environment test. It checks that Lean 4 and the required mathlib components are available, including finite types, permutations, permutation powers, permutation-cycle tools, finite sets, and basic tactics.

`PrisonersModel.lean` contains the main formalisation. It defines the game state, the pointer-following strategy, the success conditions, the cycle-length predicate, the cycle equivalence lemma, and the final structural theorem.

## Structure of `test.lean`

`test.lean` is a modified version of the course test file. The original course test imported several course libraries such as Veil, Velvet, LoVe, and related case-study utilities. Since this project is based on a mathematical formalisation of the 100 prisoners problem, the test file was adjusted to use only the Lean/mathlib components needed for finite permutations and cycle reasoning.

The file imports mathlib modules for finite permutations, permutation cycles, cycle factors, cycle types, and tactics. This confirms that the local Lean environment has access to the mathematical tools used in the project.

The file defines prisoners and drawers as `Fin 100`, and defines a room state as `Equiv.Perm (Fin 100)`. It also introduces a simple pointer-following function `follow`, where following the pointer for `t` steps means applying the room-state permutation `t` times.

The basic examples check the identity permutation and simple permutation powers. These examples verify that following a permutation for zero steps returns the starting point, following it for one step applies the permutation once, and under the identity permutation every prisoner succeeds immediately.

The final part of `test.lean` uses `#check` commands to confirm that relevant mathlib names are available, including `Equiv.Perm`, `Equiv.Perm.cycleOf`, `Equiv.Perm.cycleFactors`, `Equiv.Perm.cycleFactorsFinset`, `Equiv.Perm.cycleType`, `Fintype.card`, and `Finset.card`.

In short, `test.lean` is a smoke test for the Lean/mathlib environment. It verifies that the project can use the permutation and cycle tools needed by the main model.

## Structure of `PrisonersModel.lean`

The first part defines the basic objects: `N = 100`, `MaxOpen = 50`, `Person := Fin 100`, `Drawer := Fin 100`, and `RoomState := Equiv.Perm Person`. This encodes the drawer arrangement as a permutation, where `π i = j` means drawer `i` contains label `j`.

The next part defines the pointer-following behaviour. `openedDrawer` describes which drawer a prisoner opens after a given number of pointer steps, and `seenLabel` describes which label is seen at that opening. This connects the informal strategy to repeated application of the permutation.

The success predicates then formalise the game rule. `PrisonerSuccessByOpening` states that a prisoner sees their own label within the first 50 openings, and `StrategySuccessByOpening` states that this holds for every prisoner.

The file also defines a return-time version of success. In this version, prisoner `i` succeeds if there exists a positive number `t ≤ 50` such that `(π ^ t) i = i`. The theorem `prisonerSuccessByOpening_iff_prisonerSuccess` proves that the game-level opening definition and the return-time definition are equivalent.

The cycle-length part defines `IsCycleLength`. A number `l` is the cycle length of prisoner `i` if it is the first positive time at which repeated application of the permutation returns to `i`. This matches the usual mathematical idea of the length of the cycle containing `i`.

The theorem `isCycleLength_unique` proves that the cycle length is unique. This ensures that the formal cycle-length predicate describes a single well-defined length for each prisoner.

The equivalence lemmas connect the operational game description with the cycle description. `IsDrawersOpenedUntilFound` describes the exact number of drawers opened before a prisoner first finds their own label. The theorem `drawersOpenedUntilFound_iff_isCycleLength` proves that this exact opening time is equivalent to the first positive return time. The theorem `cycle_equivalence_lemma` then states that the number of drawers opened before a prisoner first finds their own label is equal to the length of the cycle containing that prisoner.

The theorem `strategySuccess_iff_noLongCycles` proves the return-time version of the main result: all prisoners succeed if and only if every prisoner belongs to a cycle of length at most 50.

The theorem `strategySuccessByOpening_iff_noLongCycles` transfers this result back to the game-level definition. It states that all prisoners succeed under the actual opening process if and only if there is no cycle longer than 50.

The final part introduces `DisjointCycle`, a formal representation of a cycle by a representative element, a length, and a proof that this length is the first positive return time of that representative. The predicate `AllDisjointCyclesLengthAtMost` states that all such formal cycles have length at most 50.

The final theorem is `main_structural_theorem`. It states that the pointer-following strategy succeeds for all prisoners if and only if all formal disjoint cycles have length at most 50. This is the main formal result of the project.