/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Combs
import Veles.Steiner

/-!
# Large sets as exact covers

A large set `LS(k-1, k, n)` of `m` Steiner systems becomes an exact cover handled by the same
checker: add `m` colour points `n, …, n+m-1`; the block `B` of system `c` becomes the
`(k+1)`-set `B ∪ {n + c}`. Every `k`-subset of `range (n+m)` with at most one colour point is then
covered exactly once (a `k`-set of `range n` by the block of its system; a `(k-1)`-set plus colour
`c` by the block of system `c` through it), and the `k`-sets with two or more colour points, which
no such block contains, are declared covered from the start (`preOf`). So a large set is a cover of
`dec (preOf n m k)` (`isCover_of_largeSet`), and a refutation certificate for that state rules out
the large set (`not_largeSet_of_noExt`).
-/

open Finset Veles.Bits Veles.Cover Veles.Checker Veles.CertKit Veles.Steiner SteinerSystems

namespace Veles.LSC

/-- Number of colour points `n + c`, `c < m`, in the point mask `T`. -/
def hi (n m T : ℕ) : ℕ := ((List.range m).filter (fun c => (T >>> (n + c)) % 2 = 1)).length

/-- The state marking every `k`-subset of `range (n+m)` with at least two colour points. -/
def preOf (n m k : ℕ) : ℕ :=
  ((combs (n + m) k).filter (fun T => 2 ≤ hi n m T)).foldl (fun a T => a ||| (1 <<< T)) 0

theorem testBit_foldl_or (j : ℕ) : ∀ (L : List ℕ) (a : ℕ),
    (L.foldl (fun a T => a ||| (1 <<< T)) a).testBit j = true ↔ a.testBit j = true ∨ j ∈ L
  | [], a => by simp
  | T :: L, a => by
    rw [List.foldl_cons, testBit_foldl_or j L, Nat.testBit_lor, one_shl, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

/-- The colour points of `T`. -/
def colours (n : ℕ) (T : Finset ℕ) : Finset ℕ := T.filter (n ≤ ·)

theorem hi_pm {n m : ℕ} {T : Finset ℕ} (hT : T ⊆ range (n + m)) :
    hi n m (pm T) = (colours n T).card := by
  have h1 : hi n m (pm T) = ((range m).filter (fun c => n + c ∈ T)).card := by
    rw [hi]
    have : ((range m).filter (fun c => n + c ∈ T)) =
        ((List.range m).filter (fun c => (pm T >>> (n + c)) % 2 = 1)).toFinset := by
      ext c; simp [bit_iff, testBit_pm]
    rw [this, List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  rw [h1]
  have : colours n T = ((range m).filter (fun c => n + c ∈ T)).map (addLeftEmbedding n) := by
    ext i
    simp only [colours, mem_filter, mem_map, mem_range, addLeftEmbedding_apply]
    constructor
    · rintro ⟨hi, hni⟩
      have := mem_range.1 (hT hi)
      exact ⟨i - n, ⟨by omega, by rwa [Nat.add_sub_cancel' hni]⟩, by omega⟩
    · rintro ⟨c, ⟨-, hc⟩, rfl⟩; exact ⟨hc, by omega⟩
  rw [this, card_map]

theorem mem_dec_preOf {n m k : ℕ} {T : Finset ℕ} (hT : T ⊆ range (n + m)) (hk : T.card = k) :
    T ∈ dec (preOf n m k) ↔ 2 ≤ (colours n T).card := by
  rw [mem_dec, preOf, testBit_foldl_or]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩; rwa [hi_pm hT] at h
  · intro h
    exact ⟨(combs_good (n + m) k).mem T hT hk, by rwa [hi_pm hT]⟩

/-- The block of system `c` for `B`: `B ∪ {n + c}`, in `ℕ`. -/
def blk (n : ℕ) {m : ℕ} (c : Fin m) (B : Finset (Fin n)) : Finset ℕ :=
  insert (n + c.val) (B.map Fin.valEmbedding)

theorem colours_blk {n m : ℕ} (c : Fin m) (B : Finset (Fin n)) :
    colours n (blk n c B) = {n + c.val} := by
  ext i
  simp only [colours, blk, mem_filter, mem_insert, mem_map, Fin.valEmbedding_apply, mem_singleton]
  constructor
  · rintro ⟨rfl | ⟨a, -, rfl⟩, h⟩
    · rfl
    · exact absurd a.isLt (by omega)
  · rintro rfl; exact ⟨Or.inl rfl, by omega⟩

/-- A set of points below `n` pulled back to `Fin n`. -/
def toFin (n : ℕ) (T : Finset ℕ) : Finset (Fin n) := univ.filter (fun a => a.val ∈ T)

theorem map_toFin {n : ℕ} {T : Finset ℕ} (hT : ∀ i ∈ T, i < n) :
    (toFin n T).map Fin.valEmbedding = T := by
  ext i
  simp only [toFin, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hi; exact ⟨⟨i, hT i hi⟩, hi, rfl⟩

theorem subset_blk_iff {n m : ℕ} {c : Fin m} {B : Finset (Fin n)} {T : Finset ℕ}
    (hT : ∀ i ∈ T, i < n) : T ⊆ blk n c B ↔ toFin n T ⊆ B := by
  constructor
  · intro h a ha
    simp only [toFin, mem_filter, mem_univ, true_and] at ha
    rcases mem_insert.1 (h ha) with h1 | h1
    · have := a.isLt; omega
    · obtain ⟨b, hb, hba⟩ := mem_map.1 h1
      have hba' : b = a := Fin.ext (by simpa using hba)
      rwa [hba'] at hb
  · intro h i hi
    apply mem_insert_of_mem
    exact mem_map.2 ⟨⟨i, hT i hi⟩, h (by simp [toFin, hi]), rfl⟩

/-- **A large set is a cover of `dec (preOf n m k)`.** -/
theorem isCover_of_largeSet {k n m : ℕ} (hk : 0 < k) (h : LargeSet (k - 1) k n m) :
    ∃ F, IsCover (n + m) (k + 1) (dec (preOf n m k)) F := by
  classical
  obtain ⟨D, hD⟩ := h
  refine ⟨univ.biUnion (fun c : Fin m => (D c).blocks.image (blk n c)), ?_, ?_⟩
  · intro B' hB'
    simp only [mem_biUnion, mem_univ, true_and, mem_image] at hB'
    obtain ⟨c, B, hB, rfl⟩ := hB'
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases mem_insert.1 hi with rfl | hi
      · exact mem_range.2 (by have := c.isLt; omega)
      · obtain ⟨a, -, rfl⟩ := mem_map.1 hi; exact mem_range.2 (by have := a.isLt; simp; omega)
    · rw [blk, card_insert_of_notMem, card_map, (D c).block_card B hB]
      simp only [mem_map, Fin.valEmbedding_apply, not_exists, not_and]
      intro a _ h; have := a.isLt; omega
  · intro T hT hTk
    have hTk' : T.card = k := by omega
    constructor
    · intro hX B' hB' hsub
      rw [mem_dec_preOf hT hTk'] at hX
      simp only [mem_biUnion, mem_univ, true_and, mem_image] at hB'
      obtain ⟨c, B, -, rfl⟩ := hB'
      have := card_le_card (filter_subset_filter (n ≤ ·) hsub)
      rw [← colours, ← colours, colours_blk, card_singleton] at this
      omega
    · intro hX
      rw [mem_dec_preOf hT hTk'] at hX
      have hle : (colours n T).card ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
      · -- no colour point: T is a k-set of range n
        have hTn : ∀ i ∈ T, i < n := by
          intro i hi
          by_contra hni
          have : i ∈ colours n T := mem_filter.2 ⟨hi, by omega⟩
          rw [card_eq_zero.1 h0] at this; simp at this
        have hcard : (toFin n T).card = k := by
          rw [← card_map Fin.valEmbedding, map_toFin hTn, hTk']
        obtain ⟨c, hc, hu⟩ := hD _ hcard
        refine ⟨blk n c (toFin n T), ⟨?_, (subset_blk_iff hTn).2 subset_rfl⟩, ?_⟩
        · simp only [mem_biUnion, mem_univ, true_and, mem_image]; exact ⟨c, _, hc, rfl⟩
        · rintro B' ⟨hB', hsub⟩
          simp only [mem_biUnion, mem_univ, true_and, mem_image] at hB'
          obtain ⟨c', B, hB, rfl⟩ := hB'
          have hTB := (subset_blk_iff hTn).1 hsub
          have hEq : toFin n T = B :=
            eq_of_subset_of_card_le hTB (by rw [(D c').block_card B hB, hcard])
          subst hEq
          rw [hu c' hB]
      · -- exactly one colour point n + c: T = R ∪ {n + c}
        obtain ⟨p, hp⟩ := card_eq_one.1 h1
        have hpT : p ∈ T := (mem_filter.1 (hp ▸ mem_singleton_self p : p ∈ colours n T)).1
        have hpn : n ≤ p := (mem_filter.1 (hp ▸ mem_singleton_self p : p ∈ colours n T)).2
        have hpm : p < n + m := mem_range.1 (hT hpT)
        set c : Fin m := ⟨p - n, by omega⟩
        set R := T.erase p
        have hRn : ∀ i ∈ R, i < n := by
          intro i hi
          by_contra hni
          have hic : i ∈ colours n T := mem_filter.2 ⟨mem_of_mem_erase hi, by omega⟩
          rw [hp, mem_singleton] at hic
          exact (ne_of_mem_erase hi) hic
        have hRc : (toFin n R).card = k - 1 := by
          rw [← card_map Fin.valEmbedding, map_toFin hRn, card_erase_of_mem hpT, hTk']
        have hTeq : ∀ B : Finset (Fin n), T ⊆ blk n c B ↔ toFin n R ⊆ B := by
          intro B
          constructor
          · intro hsub
            apply (subset_blk_iff (c := c) hRn).1
            exact (erase_subset _ _).trans hsub
          · intro hsub i hi
            by_cases hip : i = p
            · subst hip; simp only [blk, c]; apply mem_insert.2; left; omega
            · exact (subset_blk_iff (c := c) hRn).2 hsub (mem_erase.2 ⟨hip, hi⟩)
        have hone := (D c).cover_unique _ hRc
        obtain ⟨B, hB⟩ := card_eq_one.1 hone
        have hBmem := mem_filter.1 (hB ▸ mem_singleton_self B)
        refine ⟨blk n c B, ⟨?_, (hTeq B).2 hBmem.2⟩, ?_⟩
        · simp only [mem_biUnion, mem_univ, true_and, mem_image]; exact ⟨c, B, hBmem.1, rfl⟩
        · rintro B' ⟨hB', hsub⟩
          simp only [mem_biUnion, mem_univ, true_and, mem_image] at hB'
          obtain ⟨c', B'', hB'', rfl⟩ := hB'
          -- the colour point of the block is p, so c' = c
          have hcc : c' = c := by
            have : p ∈ blk n c' B'' := hsub hpT
            rcases mem_insert.1 this with h2 | h2
            · apply Fin.ext; simp only [c]; omega
            · obtain ⟨a, -, ha⟩ := mem_map.1 h2
              have := a.isLt; simp at ha; omega
          rw [hcc] at hB'' hsub
          have : B'' ∈ (D c).blocks.filter (toFin n R ⊆ ·) := mem_filter.2 ⟨hB'', (hTeq B'').1 hsub⟩
          rw [hB, mem_singleton] at this
          rw [hcc, this]

/-- A refutation of the colour-point encoding rules out the large set. -/
theorem not_largeSet_of_noExt {k n m : ℕ} (hk : 0 < k)
    (h : NoExt (n + m) (k + 1) (dec (preOf n m k))) : ¬ LargeSet (k - 1) k n m := by
  intro hL
  obtain ⟨F, hF⟩ := isCover_of_largeSet hk hL
  exact h F hF

end Veles.LSC
