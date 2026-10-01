/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Johnson835

/-!
# The frontier: bridges to other open problems

* `witness_of_property`: for `7 ≤ k ≤ 192`, `Property k` yields a
  `LargeSteinerSystemWitness` (upstream `SteinerSystems`), i.e. a solution of Epoch AI's
  FrontierMath open problem "Large Steiner Systems": derive `S(k-1, k, 2k)` `d` times, with
  `d = 0` for `k ≤ 10`, `d = k - 10` for `11 ≤ k ≤ 189` and `d = 2k - 199` for `190 ≤ k ≤ 192`.
* `steiner_4_5_of_property`: `Property k` yields an `S(4, 5, k + 5)` for `k ≥ 5`; in particular
  `Property 16` yields an `S(4, 5, 21)`, whose existence is open.
* `range_exact`: the range `7 ≤ k ≤ 192` is exactly the set of `k` for which some number of
  derivations lands in the FrontierMath window.
-/

open SteinerSystems Veles.Steiner Veles.J835

namespace Veles.Bridge

/-- The number of derivations used for the bridge. -/
def depth (k : ℕ) : ℕ := if k ≤ 10 then 0 else if k ≤ 189 then k - 10 else 2 * k - 199

theorem witness_of_property {k : ℕ} (hk7 : 7 ≤ k) (hk : k ≤ 192) (h : Erdos835.Property k) :
    Nonempty LargeSteinerSystemWitness := by
  have hS := steiner_of_property (by omega) h
  have hd : depth k ≤ k - 1 := by unfold depth; split_ifs <;> omega
  obtain ⟨S⟩ := nonempty_iterate (by omega) (by omega) hS (depth k) hd
  refine ⟨⟨2 * k - depth k, k - depth k, k - 1 - depth k, ?_, ?_, ?_, ?_, ?_, S⟩⟩ <;>
    (unfold depth; split_ifs <;> omega)

/-- `Property k` gives an `S(4, 5, k + 5)` for `k ≥ 5`. -/
theorem steiner_4_5_of_property {k : ℕ} (hk : 5 ≤ k) (h : Erdos835.Property k) :
    Nonempty (SteinerSystem 4 5 (k + 5)) := by
  have hS := steiner_of_property (by omega) h
  have := nonempty_iterate (by omega) (by omega) hS (k - 5) (by omega)
  have e1 : k - 1 - (k - 5) = 4 := by omega
  have e2 : k - (k - 5) = 5 := by omega
  have e3 : 2 * k - (k - 5) = k + 5 := by omega
  rwa [e1, e2, e3] at this

/-- The smallest open case: a `(k+1)`-colouring for `k = 16` would give an `S(4, 5, 21)`. -/
theorem steiner_4_5_21_of_property_16 (h : Erdos835.Property 16) :
    Nonempty (SteinerSystem 4 5 21) :=
  steiner_4_5_of_property (by norm_num) h

/-- Some number `d < k - 1` of derivations of `S(k-1, k, 2k)` lands in the FrontierMath window
exactly when `7 ≤ k ≤ 192`, for every `k`. -/
theorem range_exact (k : ℕ) :
    ((∃ d < k - 1, 6 ≤ k - 1 - d ∧ k - 1 - d ≤ 9 ∧ 2 * k - d < 200) ↔ (7 ≤ k ∧ k ≤ 192)) := by
  constructor
  · rintro ⟨d, hd, h1, h2, h3⟩; omega
  · rintro ⟨h1, h2⟩
    refine ⟨depth k, ?_, ?_, ?_, ?_⟩ <;> (unfold depth; split_ifs <;> omega)

end Veles.Bridge
