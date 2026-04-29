import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

namespace Prisoners

/-- Number of prisoners and drawers. -/
abbrev N : Nat := 100

/-- Maximum number of drawers each prisoner may open. -/
abbrev MaxOpen : Nat := 50

/--
We use `Fin 100` for prisoner and drawer labels.

Lean labels them as `0, ..., 99`.
This is mathematically the same as the informal labels `1, ..., 100`.
-/
abbrev Person := Fin N

/-- Drawers have the same labels as prisoners. -/
abbrev Drawer := Fin N

/--
A room state is a permutation.

If `π i = j`, then drawer `i` contains label `j`.
-/
abbrev RoomState := Equiv.Perm Person

/--
The drawer opened after `step` pointer moves.

`step = 0`: prisoner `i` opens drawer `i`.

`step = 1`: prisoner `i` opens drawer `π i`.

`step = 2`: prisoner `i` opens drawer `π (π i)`.

So the opened drawer is `(π ^ step) i`.
-/
def openedDrawer (π : RoomState) (i : Person) (step : Nat) : Drawer :=
  (π ^ step) i

/--
The label seen at zero-based opening `step`.

At `step = 0`, the prisoner opens drawer `i` and sees label `π i`.

At `step = 1`, the prisoner opens drawer `π i` and sees label `π (π i)`.

Thus the seen label is `(π ^ (step + 1)) i`.
-/
def seenLabel (π : RoomState) (i : Person) (step : Nat) : Person :=
  (π ^ (step + 1)) i

/--
A direct unfolding lemma for `seenLabel`.
-/
theorem seenLabel_eq_power_succ
    (π : RoomState) (i : Person) (step : Nat) :
    seenLabel π i step = (π ^ (step + 1)) i := by
  rfl

/--
Single-prisoner success in the return-time model.

Here `t` is the number of opened drawers when prisoner `i`
finds their own label.

`t = 1` means they find their label in the first drawer.

The condition `(π ^ t) i = i` says that the pointer chain returns to
the starting prisoner after `t` label readings.
-/
def PrisonerSuccess (π : RoomState) (i : Person) : Prop :=
  ∃ t : Nat, 1 ≤ t ∧ t ≤ MaxOpen ∧ (π ^ t) i = i

/--
All prisoners succeed in the return-time model.
-/
def StrategySuccess (π : RoomState) : Prop :=
  ∀ i : Person, PrisonerSuccess π i

/--
Game-level single-prisoner success.

`step` is zero-based, so `step < 50` means the prisoner succeeds
within the first 50 openings.
-/
def PrisonerSuccessByOpening (π : RoomState) (i : Person) : Prop :=
  ∃ step : Nat, step < MaxOpen ∧ seenLabel π i step = i

/--
Game-level whole-strategy success.

Every prisoner finds their own label within the first 50 openings.
-/
def StrategySuccessByOpening (π : RoomState) : Prop :=
  ∀ i : Person, PrisonerSuccessByOpening π i

/--
The game-level definition of single-prisoner success is equivalent
to the return-time definition.
-/
theorem prisonerSuccessByOpening_iff_prisonerSuccess
    (π : RoomState) (i : Person) :
    PrisonerSuccessByOpening π i ↔ PrisonerSuccess π i := by
  constructor

  · intro h
    rcases h with ⟨step, hstep_lt, hseen⟩
    refine ⟨step + 1, ?_, ?_, ?_⟩
    · omega
    · omega
    · simpa [seenLabel] using hseen

  · intro h
    rcases h with ⟨t, ht_pos, ht_le, ht_return⟩
    refine ⟨t - 1, ?_, ?_⟩
    · omega
    · have ht_sub_add : t - 1 + 1 = t := by
        omega
      simpa [seenLabel, ht_sub_add] using ht_return

/--
The game-level whole-strategy definition is equivalent to the return-time
whole-strategy definition.
-/
theorem strategySuccessByOpening_iff_strategySuccess
    (π : RoomState) :
    StrategySuccessByOpening π ↔ StrategySuccess π := by
  constructor

  · intro h i
    exact (prisonerSuccessByOpening_iff_prisonerSuccess π i).mp (h i)

  · intro h i
    exact (prisonerSuccessByOpening_iff_prisonerSuccess π i).mpr (h i)

/--
`l` is the cycle length of prisoner `i` if:

1. `l` is positive;
2. following the permutation `l` times returns to `i`;
3. every other positive return time is at least `l`.

So `l` is the first positive time at which the pointer chain returns to `i`.
This is the length of the disjoint cycle containing `i`.
-/
def IsCycleLength (π : RoomState) (i : Person) (l : Nat) : Prop :=
  1 ≤ l ∧
  (π ^ l) i = i ∧
  ∀ t : Nat, 1 ≤ t → (π ^ t) i = i → l ≤ t

/--
The cycle containing prisoner `i` has length at most `bound`.
-/
def CycleLengthAtMost (π : RoomState) (i : Person) (bound : Nat) : Prop :=
  ∃ l : Nat, IsCycleLength π i l ∧ l ≤ bound

/--
There is no cycle longer than 50, written pointwise.

For every prisoner `i`, the cycle containing `i` has length at most 50.
-/
def NoLongCycles (π : RoomState) : Prop :=
  ∀ i : Person, CycleLengthAtMost π i MaxOpen

/--
Cycle length is unique.

If both `l` and `m` are the first positive return time of `i`,
then `l = m`.
-/
theorem isCycleLength_unique
    {π : RoomState} {i : Person} {l m : Nat}
    (hl : IsCycleLength π i l)
    (hm : IsCycleLength π i m) :
    l = m := by
  unfold IsCycleLength at hl hm
  rcases hl with ⟨hlpos, hlreturn, hlmin⟩
  rcases hm with ⟨hmpos, hmreturn, hmmin⟩
  exact le_antisymm
    (hlmin m hmpos hmreturn)
    (hmmin l hlpos hlreturn)

/--
`IsDrawersOpenedUntilFound π i t` means that `t` is exactly the number
of drawers opened before prisoner `i` first finds their own label.

This is an operational definition: it talks about labels seen while opening
drawers.
-/
def IsDrawersOpenedUntilFound
    (π : RoomState) (i : Person) (t : Nat) : Prop :=
  1 ≤ t ∧
  seenLabel π i (t - 1) = i ∧
  ∀ s : Nat, 1 ≤ s → seenLabel π i (s - 1) = i → t ≤ s

/--
Operational first-find time is equivalent to first positive return time.

This is the local bridge between the game description and the cycle-length
definition.
-/
theorem drawersOpenedUntilFound_iff_isCycleLength
    (π : RoomState) (i : Person) (t : Nat) :
    IsDrawersOpenedUntilFound π i t ↔ IsCycleLength π i t := by
  constructor

  · intro h
    rcases h with ⟨htpos, hseen, hmin⟩
    unfold IsCycleLength
    constructor
    · exact htpos
    constructor
    · have ht_sub_add : t - 1 + 1 = t := by
        omega
      simpa [seenLabel, ht_sub_add] using hseen
    · intro s hspos hsreturn
      have hs_sub_add : s - 1 + 1 = s := by
        omega
      have hseen_s : seenLabel π i (s - 1) = i := by
        simpa [seenLabel, hs_sub_add] using hsreturn
      exact hmin s hspos hseen_s

  · intro h
    unfold IsCycleLength at h
    rcases h with ⟨htpos, htreturn, hmin⟩
    unfold IsDrawersOpenedUntilFound
    constructor
    · exact htpos
    constructor
    · have ht_sub_add : t - 1 + 1 = t := by
        omega
      simpa [seenLabel, ht_sub_add] using htreturn
    · intro s hspos hseen_s
      have hs_sub_add : s - 1 + 1 = s := by
        omega
      have hsreturn : (π ^ s) i = i := by
        simpa [seenLabel, hs_sub_add] using hseen_s
      exact hmin s hspos hsreturn

/--
Cycle Equivalence Lemma.

For any prisoner `i`, if `t` is the exact number of drawers opened before
finding their own label, and `l` is the length of the disjoint cycle containing
`i`, then `t = l`.
-/
theorem cycle_equivalence_lemma
    {π : RoomState} {i : Person} {t l : Nat}
    (hopened : IsDrawersOpenedUntilFound π i t)
    (hcycle : IsCycleLength π i l) :
    t = l := by
  have htcycle : IsCycleLength π i t :=
    (drawersOpenedUntilFound_iff_isCycleLength π i t).mp hopened
  exact isCycleLength_unique htcycle hcycle

/--
If every cycle has length at most 50, then every prisoner succeeds.

This direction is direct: use the cycle length as the number of openings.
-/
theorem noLongCycles_implies_strategySuccess (π : RoomState) :
    NoLongCycles π → StrategySuccess π := by
  intro h i
  rcases h i with ⟨l, hlcycle, hle⟩
  unfold IsCycleLength at hlcycle
  rcases hlcycle with ⟨hpos, hreturn, _hminimal⟩
  exact ⟨l, hpos, hle, hreturn⟩

/--
If every prisoner succeeds within 50 openings, then every cycle has length
at most 50.

For each prisoner `i`, success gives some positive return time `t ≤ 50`.
We then take the least positive return time `l`. Since `l ≤ t`, we get
`l ≤ 50`.
-/
theorem strategySuccess_implies_noLongCycles (π : RoomState) :
    StrategySuccess π → NoLongCycles π := by
  classical
  intro h i

  rcases h i with ⟨t, htpos, htle, htreturn⟩

  let P : Nat → Prop := fun n => 1 ≤ n ∧ (π ^ n) i = i

  have hP : ∃ n : Nat, P n := by
    exact ⟨t, htpos, htreturn⟩

  let l : Nat := Nat.find hP

  have hlP : P l := by
    simpa [l] using Nat.find_spec hP

  have hlmin : ∀ n : Nat, P n → l ≤ n := by
    intro n hn
    simpa [l] using Nat.find_min' hP hn

  refine ⟨l, ?_, ?_⟩

  · unfold IsCycleLength
    constructor
    · exact hlP.1
    constructor
    · exact hlP.2
    · intro n hnpos hnreturn
      exact hlmin n ⟨hnpos, hnreturn⟩

  · exact le_trans (hlmin t ⟨htpos, htreturn⟩) htle

/--
Main structural theorem, pointwise version.

The return-time strategy succeeds for all prisoners iff there is no cycle
longer than 50.
-/
theorem strategySuccess_iff_noLongCycles (π : RoomState) :
    StrategySuccess π ↔ NoLongCycles π := by
  constructor
  · exact strategySuccess_implies_noLongCycles π
  · exact noLongCycles_implies_strategySuccess π

/--
Game-level structural theorem.

All prisoners succeed by opening at most 50 drawers iff there is no cycle
longer than 50.
-/
theorem strategySuccessByOpening_iff_noLongCycles
    (π : RoomState) :
    StrategySuccessByOpening π ↔ NoLongCycles π := by
  exact Iff.trans
    (strategySuccessByOpening_iff_strategySuccess π)
    (strategySuccess_iff_noLongCycles π)

/--
A formal disjoint cycle of `π`.

We represent the cycle by:
1. a representative element `rep`;
2. a natural number `len`;
3. a proof that `len` is the first positive return time of `rep`.

This is the local formal version of a cycle containing a representative.
-/
structure DisjointCycle (π : RoomState) where
  rep : Person
  len : Nat
  is_len : IsCycleLength π rep len

/--
All formal disjoint cycles have length at most 50.

The first part says every prisoner belongs to a cycle with a well-defined
cycle length.

The second part says every such formal cycle has length at most 50.
-/
def AllDisjointCyclesLengthAtMost (π : RoomState) : Prop :=
  (∀ i : Person, ∃ l : Nat, IsCycleLength π i l) ∧
  ∀ c : DisjointCycle π, c.len ≤ MaxOpen

/--
The pointwise no-long-cycle condition is equivalent to the formal
all-disjoint-cycles-bounded condition.
-/
theorem noLongCycles_iff_allDisjointCyclesLengthAtMost
    (π : RoomState) :
    NoLongCycles π ↔ AllDisjointCyclesLengthAtMost π := by
  constructor

  · intro h
    constructor
    · intro i
      rcases h i with ⟨l, hl, _hle⟩
      exact ⟨l, hl⟩
    · intro c
      rcases h c.rep with ⟨l, hl, hle⟩
      have hEq : c.len = l := isCycleLength_unique c.is_len hl
      simpa [hEq] using hle

  · intro h i
    rcases h.1 i with ⟨l, hl⟩
    have hle : l ≤ MaxOpen :=
      h.2 { rep := i, len := l, is_len := hl }
    exact ⟨l, hl, hle⟩

/--
Main Structural Theorem.

This is the proposal-level theorem:

The game-level pointer-following strategy succeeds for all prisoners
if and only if all formal disjoint cycles of the room-state permutation
have length at most 50.
-/
theorem main_structural_theorem
    (π : RoomState) :
    StrategySuccessByOpening π ↔ AllDisjointCyclesLengthAtMost π := by
  exact Iff.trans
    (strategySuccessByOpening_iff_noLongCycles π)
    (noLongCycles_iff_allDisjointCyclesLengthAtMost π)

/-
Sanity check:
under the identity permutation, every prisoner succeeds immediately.
-/
example : StrategySuccessByOpening (1 : RoomState) := by
  intro i
  refine ⟨0, ?_, ?_⟩
  · decide
  · simp [seenLabel]

/-
Sanity check:
under the identity permutation, every cycle has length 1.
-/
example : AllDisjointCyclesLengthAtMost (1 : RoomState) := by
  constructor

  · intro i
    refine ⟨1, ?_⟩
    unfold IsCycleLength
    constructor
    · decide
    constructor
    · simp
    · intro t ht _hret
      exact ht

  · intro c
    have hc := c.is_len
    unfold IsCycleLength at hc
    rcases hc with ⟨_hpos, _hreturn, hmin⟩
    have hle_one : c.len ≤ 1 := hmin 1 (by decide) (by simp)
    exact le_trans hle_one (by decide)

end Prisoners
