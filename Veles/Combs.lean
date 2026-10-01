/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.CertKit

/-!
# Item lists without search

`combs v t` lists the point masks of the `t`-subsets of `range v` directly (length `C(v, t)`),
instead of filtering all `2^v` masks. `combs_good` gives the `ItemsGood` hypothesis of the
checker for every `v` and `t`, so no kernel evaluation over `2^v` masks is needed.
-/

open Finset Veles.Bits Veles.Checker

namespace Veles.CertKit

/-- Point masks of the `t`-subsets of `range v`. -/
def combs : ℕ → ℕ → List ℕ
  | 0, 0 => [0]
  | 0, _ + 1 => []
  | _ + 1, 0 => [0]
  | v + 1, t + 1 => combs v (t + 1) ++ (combs v t).map (· ||| (1 <<< v))

theorem ofMask_eq_empty {m : ℕ} : ofMask m = ∅ ↔ m = 0 := by
  constructor
  · intro h; rw [← pm_ofMask m, h]; rfl
  · rintro rfl; rfl

theorem ofMask_or_two_pow {a v : ℕ} (ha : a < 2 ^ v) :
    ofMask (a ||| (1 <<< v)) = insert v (ofMask a) := by
  ext i
  rw [mem_insert, mem_ofMask, mem_ofMask, Nat.testBit_lor, one_shl, Nat.testBit_two_pow]
  by_cases h : i = v
  · subst h; simp
  · simp [h, Ne.symm h]

theorem mem_combs : ∀ (v t m : ℕ), m ∈ combs v t ↔ m < 2 ^ v ∧ (ofMask m).card = t
  | 0, 0, m => by
    simp only [combs, List.mem_singleton, pow_zero, Nat.lt_one_iff]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, -⟩; rfl
  | 0, t + 1, m => by
    simp only [combs, List.not_mem_nil, pow_zero, Nat.lt_one_iff, false_iff, not_and]
    rintro rfl; simp [ofMask]
  | v + 1, 0, m => by
    simp only [combs, List.mem_singleton, card_eq_zero, ofMask_eq_empty]
    constructor
    · rintro rfl; exact ⟨by positivity, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  | v + 1, t + 1, m => by
    rw [combs, List.mem_append, List.mem_map, mem_combs v (t + 1) m]
    constructor
    · rintro (⟨hm, hc⟩ | ⟨a, ha, rfl⟩)
      · exact ⟨lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)), hc⟩
      · obtain ⟨ha1, ha2⟩ := (mem_combs v t a).1 ha
        refine ⟨?_, ?_⟩
        · rw [← pm_ofMask (a ||| _), ofMask_or_two_pow ha1]
          apply pm_lt
          intro i hi
          rcases mem_insert.1 hi with rfl | hi
          · exact mem_range.2 (by omega)
          · exact mem_range.2 (by have := mem_range.1 (ofMask_subset_range ha1 hi); omega)
        · rw [ofMask_or_two_pow ha1, card_insert_of_notMem, ha2]
          intro hv; have := mem_range.1 (ofMask_subset_range ha1 hv); omega
    · rintro ⟨hm, hc⟩
      by_cases hv : m.testBit v = true
      · right
        refine ⟨m % 2 ^ v, (mem_combs v t _).2 ⟨Nat.mod_lt _ (by positivity), ?_⟩, ?_⟩
        · have hsplit : ofMask m = insert v (ofMask (m % 2 ^ v)) := by
            ext i
            rw [mem_insert, mem_ofMask, mem_ofMask, Nat.testBit_mod_two_pow]
            by_cases h : i = v
            · subst h; simp [hv]
            · rcases Nat.lt_or_gt_of_ne h with h' | h'
              · simp [h, h']
              · have : m.testBit i = false :=
                  Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h'))
                simp [h, this, Nat.not_lt.2 h'.le]
          have hnot : v ∉ ofMask (m % 2 ^ v) := by
            rw [mem_ofMask, Nat.testBit_mod_two_pow]; simp
          rw [hsplit, card_insert_of_notMem hnot] at hc; omega
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_lor, one_shl, Nat.testBit_two_pow, Nat.testBit_mod_two_pow]
          by_cases h : i = v
          · subst h; simp [hv]
          · rcases Nat.lt_or_gt_of_ne h with h' | h'
            · simp [h, h', Ne.symm h]
            · have : m.testBit i = false :=
                Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) h'))
              simp [h, this, Nat.not_lt.2 h'.le, Ne.symm h]
      · left
        refine ⟨Nat.lt_pow_two_of_testBit m (fun i hi => ?_), hc⟩
        rcases Nat.eq_or_lt_of_le hi with rfl | hi
        · simpa using hv
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi))

theorem combs_good (v t : ℕ) : ItemsGood v t (combs v t) where
  mem S hS hc := (mem_combs v t (pm S)).2 ⟨pm_lt hS, by rw [ofMask_pm, hc]⟩
  lt m hm := ((mem_combs v t m).1 hm).1

end Veles.CertKit
