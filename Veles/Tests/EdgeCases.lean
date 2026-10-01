/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Results
import Veles.Symmetry
import Veles.Smoke
import Veles.LargeSetCover

/-!
# Edge cases and non-vacuity

The negative results are only informative if the definitions can be met. These tests check
boundary instances of the general theorems and that `Property k` does hold for `k = 1, 2`
(the problem asks for `k > 2`), so no theorem here is true because a definition is empty.
-/

open SimpleGraph Veles.J835 Veles.Results

namespace Veles.Tests

/-- `Property 2` holds (`χ(J(4,2)) = 3`): the equivalence is not vacuous. -/
theorem property_2 : Erdos835.Property 2 :=
  (property_iff_chromaticNumber 2 (by norm_num)).1 (by rw [Veles.Smoke.chromaticNumber_J42]; rfl)

/-- `Property 1` holds: `J(2,1)` is an edge, coloured with two colours. -/
theorem property_1 : Erdos835.Property 1 := by
  rw [property_iff_proper (by norm_num)]
  refine ⟨fun s => if (0 : Fin 2) ∈ s.val then 0 else 1, ?_⟩
  decide

/-- Hence a large set `LS(1, 2, 4)` of three perfect matchings exists. -/
theorem largeSet_1_2_4 : Veles.Steiner.LargeSet 1 2 4 3 :=
  (property_iff_largeSet (k := 2) (by norm_num)).1 property_2

/-- And an `S(1, 2, 4)` exists; `prime_of_steiner` then gives `3` prime, as it should. -/
theorem prime_3 : (2 + 1).Prime := prime_of_steiner (by norm_num) (steiner_of_property (by norm_num) property_2)

/-- Ma–Tang at the first composite case `k = 3` (`k + 1 = 4`). -/
example : ¬ Erdos835.Property 3 := not_property_of_not_prime (by norm_num) (by norm_num)

/-- The clique bound at `k = 1`: `2 ≤ χ(J(2,1))`. -/
example : ((1 + 1 : ℕ) : ℕ∞) ≤ J(2 * 1, 1).chromaticNumber := clique_bound (by norm_num)

/-- Derivation with `d = 0` is the identity on existence. -/
example {t k m : ℕ} (htk : t ≤ k) (hkm : k ≤ m)
    (h : Nonempty (SteinerSystems.SteinerSystem t k m)) :
    Nonempty (SteinerSystems.SteinerSystem (t - 0) (k - 0) (m - 0)) :=
  Veles.Steiner.nonempty_iterate htk hkm h 0 (Nat.zero_le _)

/-- The bridge window is exactly `7 ≤ k ≤ 192`: it fails at `k = 6` and `k = 193`. -/
example : ¬ (∃ d < 6 - 1, 6 ≤ 6 - 1 - d ∧ 6 - 1 - d ≤ 9 ∧ 2 * 6 - d < 200) := by
  rintro ⟨d, -, h1, -, -⟩; omega
example : ¬ (∃ d < 193 - 1, 6 ≤ 193 - 1 - d ∧ 193 - 1 - d ≤ 9 ∧ 2 * 193 - d < 200) := by
  rintro ⟨d, -, h1, -, h3⟩; omega
example : ∃ d < 192 - 1, 6 ≤ 192 - 1 - d ∧ 192 - 1 - d ≤ 9 ∧ 2 * 192 - d < 200 := ⟨185, by decide⟩
example : ∃ d < 7 - 1, 6 ≤ 7 - 1 - d ∧ 7 - 1 - d ≤ 9 ∧ 2 * 7 - d < 200 := ⟨0, by decide⟩

/-- The block count at the smallest nontrivial case: an `S(1, 2, 4)` has `2` blocks. -/
example (S : SteinerSystems.SteinerSystem 1 2 4) : S.blocks.card = 2 := by
  have := Veles.Steiner.card_blocks_mul S
  norm_num at this; omega

/-- Johnson's bound at small values is the number the recursion gives. -/
example : Erdos835.johnsonBound 8 4 4 = 14 := by decide
example : Erdos835.johnsonBound 4 4 2 = 2 := by decide

/-- The symmetry theorem's prime window is empty for `k = 1, 2` (so it says nothing there) and
for `k = 16` contains `19` but not `17`. -/
example : ¬ ∃ p, p.Prime ∧ 1 + 1 < p ∧ p ≤ 2 * 1 := by
  rintro ⟨p, hp, h1, h2⟩; omega
example : (19 : ℕ).Prime ∧ 16 + 1 < 19 ∧ 19 ≤ 2 * 16 := by norm_num
example : ¬ (16 + 1 < 17) := by norm_num

/-- Positive control at `t = 2`: the Fano plane is an `S(2, 3, 7)`, checked by the kernel (the
upstream sanity check uses `native_decide`). -/
def fano : SteinerSystems.SteinerSystem 2 3 7 :=
  ⟨{{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}},
   by decide +kernel, by decide +kernel⟩

/-- Hence the empty state of `S(2,3,7)` has a cover: the checker cannot certify it empty. -/
theorem not_noExt_fano : ¬ Veles.Cover.NoExt 7 3 ∅ := fun h =>
  h _ (Veles.Cover.isCover_of_steiner rfl fano)

/-- Positive control for the colour-point encoding: the large set `LS(1, 2, 4)` of three systems
gives a cover of the pre-covered state, so that state cannot be certified empty. -/
theorem not_noExt_pre_1_2_4 : ¬ Veles.Cover.NoExt (4 + 3) (2 + 1) (Veles.Bits.dec (Veles.LSC.preOf 4 3 2)) :=
  fun h => by
    obtain ⟨F, hF⟩ := Veles.LSC.isCover_of_largeSet (k := 2) (n := 4) (m := 3) (by norm_num) largeSet_1_2_4
    exact h F hF

end Veles.Tests
