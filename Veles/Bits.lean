/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Cover

/-!
# Point masks

A finite set of points `T : Finset ℕ` is encoded as the number `pm T = ∑ i ∈ T, 2 ^ i`; bit `i` of
`pm T` is set exactly when `i ∈ T` (`testBit_pm`). A state (a set of items) is encoded as a number
whose bit `pm T` is set exactly when the item `T` is covered (`dec`).
-/

open Finset

namespace Veles.Bits

/-- The point mask of a finite set. -/
def pm (T : Finset ℕ) : ℕ := ∑ i ∈ T, 2 ^ i

/-- The finite set with point mask `m`. -/
def ofMask (m : ℕ) : Finset ℕ := m.bitIndices.toFinset

@[simp] theorem ofMask_pm (T : Finset ℕ) : ofMask (pm T) = T :=
  Finset.toFinset_bitIndices_sum_two_pow T

@[simp] theorem pm_ofMask (m : ℕ) : pm (ofMask m) = m :=
  Finset.sum_toFinset_bitIndices_two_pow m

theorem mem_ofMask {m i : ℕ} : i ∈ ofMask m ↔ m.testBit i := by
  simp [ofMask, Nat.mem_bitIndices]

theorem testBit_pm (T : Finset ℕ) (i : ℕ) : (pm T).testBit i = decide (i ∈ T) := by
  have := @mem_ofMask (pm T) i
  rw [ofMask_pm] at this
  by_cases h : i ∈ T <;> simp_all

theorem pm_injective : Function.Injective pm := fun a b h => by
  rw [← ofMask_pm a, h, ofMask_pm]

theorem pm_erase {B : Finset ℕ} {y : ℕ} (hy : y ∈ B) : pm (B.erase y) = pm B ^^^ 2 ^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_pm, testBit_pm, Nat.testBit_two_pow]
  by_cases h : i = y
  · subst h; simp [hy]
  · simp [h, Ne.symm h]

theorem pm_insert (T : Finset ℕ) (x : ℕ) : pm (insert x T) = pm T ||| 2 ^ x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_lor, testBit_pm, testBit_pm, Nat.testBit_two_pow]
  by_cases h : i = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem pm_lt {T : Finset ℕ} {v : ℕ} (hT : T ⊆ range v) : pm T < 2 ^ v := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_pm]
  simp only [decide_eq_false_iff_not]
  intro h; have := mem_range.1 (hT h); omega

theorem ofMask_subset_range {m v : ℕ} (hm : m < 2 ^ v) : ofMask m ⊆ range v := by
  intro i hi
  rw [mem_ofMask] at hi
  rw [mem_range]
  by_contra h
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hi
  exact absurd hi (by simp)

/-- The state encoded by `X`: the items whose bit is set. -/
def dec (X : ℕ) : Set (Finset ℕ) := {T | X.testBit (pm T) = true}

theorem mem_dec {X : ℕ} {T : Finset ℕ} : T ∈ dec X ↔ X.testBit (pm T) = true := Iff.rfl

theorem dec_lor (X Y : ℕ) : dec (X ||| Y) = dec X ∪ dec Y := by
  ext T; simp [dec]

/-- Number of set bits among the lowest `n`. -/
def popc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, b => b % 2 + popc n (b >>> 1)

theorem popc_eq_card (n m : ℕ) (hm : m < 2 ^ n) : popc n m = (ofMask m).card := by
  induction n generalizing m with
  | zero => simp at hm; subst hm; simp [popc, ofMask]
  | succ n ih =>
    have hm2 : m >>> 1 < 2 ^ n := by
      rw [Nat.shiftRight_eq_div_pow, pow_one]; rw [pow_succ] at hm; omega
    rw [popc, ih _ hm2]
    -- ofMask m = image (· + 1) (ofMask (m >>> 1)) ∪ (if bit 0 then {0} else ∅)
    have key : ofMask m = (if m % 2 = 1 then {0} else ∅) ∪ (ofMask (m >>> 1)).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext i
      rw [mem_union, mem_map, mem_ofMask]
      rcases i with _ | i
      · simp only [Nat.testBit_zero]
        split_ifs with h <;> simp [h]
      · rw [Nat.testBit_succ]
        simp only [Function.Embedding.coeFn_mk, mem_ofMask, Nat.shiftRight_eq_div_pow, pow_one]
        constructor
        · intro h; right; exact ⟨i, h, rfl⟩
        · rintro (h | ⟨j, hj, hji⟩)
          · split_ifs at h <;> simp at h
          · simp at hji; subst hji; exact hj
    rw [key, card_union_of_disjoint]
    · rw [card_map]; split_ifs with h <;> simp [h]; omega
    · rw [disjoint_left]; intro a ha hb
      split_ifs at ha
      · simp at ha; subst ha; simp at hb
      · simp at ha

end Veles.Bits
