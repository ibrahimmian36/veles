/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Upstream

/-!
# Steiner systems: derived systems, block count, large sets

All statements use the upstream `SteinerSystems.SteinerSystem`.

* `derived`: the blocks through the last point, with that point removed, form an
  `S(t, k, n)` whenever the blocks of an `S(t+1, k+1, n+1)` do.
* `nonempty_iterate`: `S(t, k, n)` gives `S(t-d, k-d, n-d)` for `d ≤ t`.
* `card_blocks_mul`: `#blocks * C(k, t) = C(n, t)`, so `C(k, t)` divides `C(n, t)`.
* `LargeSet t k n m`: `m` Steiner systems `S(t, k, n)` whose block sets partition the
  `k`-subsets; `LargeSet.derived` passes to the derived parameters with the same `m`.
-/

open Finset SteinerSystems

namespace Veles.Steiner

variable {n : ℕ}

/-- The points of `B` other than the last, as a subset of `Fin n`. -/
def pull (B : Finset (Fin (n + 1))) : Finset (Fin n) := univ.filter (fun i => i.castSucc ∈ B)

/-- `R` together with the last point. -/
def lift (R : Finset (Fin n)) : Finset (Fin (n + 1)) := insert (Fin.last n) (R.map Fin.castSuccEmb)

theorem mem_pull {B : Finset (Fin (n + 1))} {i : Fin n} : i ∈ pull B ↔ i.castSucc ∈ B := by
  simp [pull]

theorem lift_pull {B : Finset (Fin (n + 1))} (h : Fin.last n ∈ B) : lift (pull B) = B := by
  ext j
  simp only [lift, mem_insert, mem_map, Fin.castSuccEmb_apply, mem_pull]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact h
    · exact hi
  · intro hj
    by_cases hl : j = Fin.last n
    · exact Or.inl hl
    · right
      exact ⟨j.castPred hl, by simpa using hj, by simp⟩

theorem pull_lift (R : Finset (Fin n)) : pull (lift R) = R := by
  ext i
  simp only [mem_pull, lift, mem_insert, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro (h | ⟨j, hj, hji⟩)
    · exact absurd h (Fin.castSucc_ne_last i)
    · rwa [← Fin.castSucc_injective _ hji]
  · intro hi; exact Or.inr ⟨i, hi, rfl⟩

theorem card_lift (R : Finset (Fin n)) : (lift R).card = R.card + 1 := by
  rw [lift, card_insert_of_notMem, card_map]
  simp only [mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
  intro i _ h; exact Fin.castSucc_ne_last i h

theorem lift_subset_iff {R : Finset (Fin n)} {B : Finset (Fin (n + 1))} :
    lift R ⊆ B ↔ Fin.last n ∈ B ∧ R ⊆ pull B := by
  constructor
  · intro h
    refine ⟨h (mem_insert_self _ _), fun i hi => mem_pull.2 (h ?_)⟩
    exact mem_insert_of_mem (mem_map_of_mem _ hi)
  · rintro ⟨hl, hR⟩ j hj
    rcases mem_insert.1 hj with rfl | hj
    · exact hl
    · obtain ⟨i, hi, rfl⟩ := mem_map.1 hj
      exact mem_pull.1 (hR hi)

/-- **Derived system** at the last point. -/
def derived {t k : ℕ} (S : SteinerSystem (t + 1) (k + 1) (n + 1)) : SteinerSystem t k n where
  blocks := (S.blocks.filter (Fin.last n ∈ ·)).image pull
  block_card B hB := by
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB
    rw [mem_filter] at hB₀
    have := card_lift (pull B₀)
    rw [lift_pull hB₀.2, S.block_card B₀ hB₀.1] at this
    omega
  cover_unique R hR := by
    have hlift : (lift R).card = t + 1 := by rw [card_lift, hR]
    have key : ((S.blocks.filter (Fin.last n ∈ ·)).image pull).filter (R ⊆ ·) =
        (S.blocks.filter (lift R ⊆ ·)).image pull := by
      ext D
      simp only [mem_filter, mem_image]
      constructor
      · rintro ⟨⟨B, ⟨hB, hl⟩, rfl⟩, hR⟩
        exact ⟨B, ⟨hB, lift_subset_iff.2 ⟨hl, hR⟩⟩, rfl⟩
      · rintro ⟨B, ⟨hB, hs⟩, rfl⟩
        obtain ⟨hl, hR⟩ := lift_subset_iff.1 hs
        exact ⟨⟨B, ⟨hB, hl⟩, rfl⟩, hR⟩
    rw [key, card_image_of_injOn, S.cover_unique _ hlift]
    intro B₁ hB₁ B₂ hB₂ h
    have h₁ := (lift_subset_iff.1 (mem_filter.1 hB₁).2).1
    have h₂ := (lift_subset_iff.1 (mem_filter.1 hB₂).2).1
    rw [← lift_pull h₁, ← lift_pull h₂]; exact congrArg lift h

/-- One derivation step on `Nonempty`. -/
theorem nonempty_derived {t k m : ℕ} (ht : 0 < t) (hk : 0 < k) (hm : 0 < m)
    (h : Nonempty (SteinerSystem t k m)) : Nonempty (SteinerSystem (t - 1) (k - 1) (m - 1)) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact ⟨derived h.some⟩

/-- **Iterated derivation**: `S(t, k, m)` gives `S(t - d, k - d, m - d)` for `d ≤ t ≤ k ≤ m`. -/
theorem nonempty_iterate {t k m : ℕ} (htk : t ≤ k) (hkm : k ≤ m)
    (h : Nonempty (SteinerSystem t k m)) :
    ∀ d ≤ t, Nonempty (SteinerSystem (t - d) (k - d) (m - d))
  | 0, _ => by simpa using h
  | d + 1, hd => by
    have := nonempty_derived (by omega) (by omega) (by omega) (nonempty_iterate htk hkm h d (by omega))
    have e1 : t - d - 1 = t - (d + 1) := by omega
    have e2 : k - d - 1 = k - (d + 1) := by omega
    have e3 : m - d - 1 = m - (d + 1) := by omega
    rwa [e1, e2, e3] at this

/-- **Block count**: every `t`-set lies in exactly one block, and every block contains
`C(k, t)` of them, so `#blocks * C(k, t) = C(m, t)`. -/
theorem card_blocks_mul {t k m : ℕ} (S : SteinerSystem t k m) :
    S.blocks.card * k.choose t = m.choose t := by
  classical
  have h1 : ∑ R ∈ (univ : Finset (Fin m)).powersetCard t, (S.blocks.filter (R ⊆ ·)).card =
      m.choose t := by
    rw [sum_congr rfl (fun R hR => S.cover_unique R (mem_powersetCard.1 hR).2)]
    simp [card_powersetCard]
  have h2 : ∑ R ∈ (univ : Finset (Fin m)).powersetCard t, (S.blocks.filter (R ⊆ ·)).card =
      ∑ B ∈ S.blocks, (B.powersetCard t).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun B _ => ?_)
    rw [← sum_filter]
    congr 1
    ext R
    simp [mem_powersetCard, and_comm]
  rw [← h1, h2, sum_congr rfl (fun B hB => by rw [card_powersetCard, S.block_card B hB]),
    sum_const, smul_eq_mul]

theorem choose_dvd {t k m : ℕ} (S : SteinerSystem t k m) : k.choose t ∣ m.choose t :=
  ⟨S.blocks.card, by rw [← card_blocks_mul S, mul_comm]⟩

/-- A **large set**: `m` Steiner systems `S(t, k, n)` whose block sets partition the
`k`-subsets of `Fin n`. -/
def LargeSet (t k n m : ℕ) : Prop :=
  ∃ D : Fin m → SteinerSystem t k n,
    ∀ s : Finset (Fin n), s.card = k → ∃! i, s ∈ (D i).blocks

/-- A derived large set is a large set, with the same number of systems. -/
theorem LargeSet.derived {t k m : ℕ} (h : LargeSet (t + 1) (k + 1) (n + 1) m) :
    LargeSet t k n m := by
  obtain ⟨D, hD⟩ := h
  refine ⟨fun i => Veles.Steiner.derived (D i), fun s hs => ?_⟩
  obtain ⟨i, hi, hu⟩ := hD (lift s) (by rw [card_lift, hs])
  have mem_iff : ∀ j, s ∈ (Veles.Steiner.derived (D j)).blocks ↔ lift s ∈ (D j).blocks := by
    intro j
    simp only [Veles.Steiner.derived, mem_image, mem_filter]
    constructor
    · rintro ⟨B, ⟨hB, hl⟩, rfl⟩; rwa [lift_pull hl]
    · intro h
      exact ⟨lift s, ⟨h, mem_insert_self _ _⟩, pull_lift s⟩
  exact ⟨i, (mem_iff i).2 hi, fun j hj => hu j ((mem_iff j).1 hj)⟩

end Veles.Steiner
