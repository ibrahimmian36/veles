/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Bridge
import Veles.JohnsonBound
import Veles.LargeSetCover
import Veles.UpstreamComposite
import Veles.Cert15
import Veles.LS348
import Veles.LS5612
import Veles.LS237
import Veles.LS4511

/-!
# Results

Everything below is stated with the upstream definitions (`Erdos835.Property`, `J(n, k)`,
`SteinerSystems.SteinerSystem`, `Nat.Composite`) and depends only on `propext`,
`Classical.choice` and `Quot.sound` (see `Veles/AxiomCheck.lean`).

* `no_S_4_5_15`: no Steiner system `S(4, 5, 15)` exists (certificate `Veles.Cert15`).
* `not_property_4`, `not_property_6`, `not_property_10`: the prime cases below 12.
* `not_property_of_le_15`: `Property k` fails for `3 ≤ k ≤ 15`, `k ≠ 12`.
* `not_property_12_of`: `k = 12` follows from the non-existence of `S(4, 5, 17)`
  (Östergård and Pottonen, not checked here), stated as a hypothesis.
* `Fills`: the upstream statements left as `sorry`, with their exact text, proved.
-/

open SimpleGraph SteinerSystems Veles.Cover Veles.J835 Veles.LSC

namespace Veles.Results

/-- **No Steiner system `S(4, 5, 15)` exists.** Kernel-checked certificate, no search program in
the trusted base. -/
theorem no_S_4_5_15 : IsEmpty (SteinerSystem 4 5 15) :=
  isEmpty_steiner_of_noExt rfl Veles.Cert15.noExt_empty

/-- No large set `LS(3, 4, 8)` of five systems. -/
theorem not_largeSet_3_4_8 : ¬ Veles.Steiner.LargeSet 3 4 8 5 :=
  not_largeSet_of_noExt (k := 4) (n := 8) (m := 5) (by norm_num) Veles.LS348.noExt_pre

/-- No large set `LS(2, 3, 7)` of five Fano planes (Cayley). -/
theorem not_largeSet_2_3_7 : ¬ Veles.Steiner.LargeSet 2 3 7 5 :=
  not_largeSet_of_noExt (k := 3) (n := 7) (m := 5) (by norm_num) Veles.LS237.noExt_pre

/-- No large set `LS(5, 6, 12)` of seven systems. -/
theorem not_largeSet_5_6_12 : ¬ Veles.Steiner.LargeSet 5 6 12 7 :=
  not_largeSet_of_noExt (k := 6) (n := 12) (m := 7) (by norm_num) Veles.LS5612.noExt_pre

/-- No large set `LS(4, 5, 11)` of seven systems. -/
theorem not_largeSet_4_5_11 : ¬ Veles.Steiner.LargeSet 4 5 11 7 :=
  not_largeSet_of_noExt (k := 5) (n := 11) (m := 7) (by norm_num) Veles.LS4511.noExt_pre

theorem not_property_4 : ¬ Erdos835.Property 4 := fun h =>
  not_largeSet_3_4_8 ((property_iff_largeSet (k := 4) (by norm_num)).1 h)

/-- The same conclusion by the derived route: a large set `LS(3,4,8)` derives to `LS(2,3,7)`. -/
theorem not_property_4' : ¬ Erdos835.Property 4 := fun h =>
  not_largeSet_2_3_7 (Veles.Steiner.LargeSet.derived ((property_iff_largeSet (k := 4) (by norm_num)).1 h))

theorem not_property_6 : ¬ Erdos835.Property 6 := fun h =>
  not_largeSet_5_6_12 ((property_iff_largeSet (k := 6) (by norm_num)).1 h)

/-- The same conclusion by the derived route through `LS(4, 5, 11)`. -/
theorem not_property_6' : ¬ Erdos835.Property 6 := fun h =>
  not_largeSet_4_5_11 (Veles.Steiner.LargeSet.derived ((property_iff_largeSet (k := 6) (by norm_num)).1 h))

theorem not_property_10 : ¬ Erdos835.Property 10 := fun h =>
  no_S_4_5_15.false (Veles.Bridge.steiner_4_5_of_property (k := 10) (by norm_num) h).some

theorem not_property_of_not_prime {k : ℕ} (hk : 0 < k) (h : ¬ (k + 1).Prime) :
    ¬ Erdos835.Property k := fun hP => h (prime_of_steiner hk (steiner_of_property hk hP))

/-- `k = 12` from the non-existence of `S(4, 5, 17)`, which is taken here as a hypothesis
(Östergård and Pottonen 2008; not checked in this development). -/
theorem not_property_12_of (h : IsEmpty (SteinerSystem 4 5 17)) : ¬ Erdos835.Property 12 :=
  fun hP => h.false (Veles.Bridge.steiner_4_5_of_property (k := 12) (by norm_num) hP).some

/-- `Property k` fails for every `3 ≤ k ≤ 15` except `k = 12`. -/
theorem not_property_of_le_15 (k : ℕ) (h3 : 3 ≤ k) (h15 : k ≤ 15) (h12 : k ≠ 12) :
    ¬ Erdos835.Property k := by
  interval_cases k
  all_goals first
    | exact absurd rfl h12
    | exact not_property_4
    | exact not_property_6
    | exact not_property_10
    | exact not_property_of_not_prime (by norm_num) (by norm_num)

/-- A `k` for which `Property k` fails has `k + 1 < χ(J(2k, k))`. -/
theorem lt_chromaticNumber_of_not_property {k : ℕ} (hk : 0 < k) (h : ¬ Erdos835.Property k) :
    (k : ℕ∞) + 1 < J(2 * k, k).chromaticNumber := by
  have := clique_bound hk
  push_cast at this
  exact lt_of_le_of_ne this (fun heq => h ((property_iff_chromaticNumber k hk).1 heq.symm))

namespace Fills

open Erdos835

variable {n k : ℕ}

/-! The upstream statements left as `sorry` in `FormalConjectures/ErdosProblems/835.lean`
(commit `137aec5`), with the same statement text, proved. -/

theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Property k := by
  exact Veles.J835.property_iff_chromaticNumber k hk

theorem johnsonGraph_2k_k_chromaticNumber_known_cases (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    J(2 * k, k).chromaticNumber > k + 1 := by
  exact lt_chromaticNumber_of_not_property (by omega) (not_property_of_le_15 k hk (by omega) (by omega))

theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 := by
  exact lt_chromaticNumber_of_not_property (k := 9) (by norm_num) (not_property_of_le_15 9 (by norm_num) (by norm_num) (by norm_num))

lemma indepNum_johnson_le_johnsonBound : α(J(n, k)) ≤ johnsonBound n 4 k :=
  Veles.JB.indepNum_johnson_le_johnsonBound

theorem chromaticNumber_johnson_2k_k_lower_bound (hk : 3 ≤ k) (hk' : k ≤ 8) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  exact lt_chromaticNumber_of_not_property (by omega) (not_property_of_le_15 k hk (by omega) (by omega))

theorem johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  have := lt_chromaticNumber_of_odd hk h
  push_cast at this
  exact this

theorem johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : (k + 1).Composite) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  have := lt_chromaticNumber_of_not_prime (k := k) (by omega) h.2
  push_cast at this
  exact this

end Fills

end Veles.Results
