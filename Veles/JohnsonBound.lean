/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Upstream

/-!
# Johnson's bound for the Johnson graph

`indepNum_johnson_le_johnsonBound : α(J(n, k)) ≤ johnsonBound n 4 k`, the upstream statement,
proved. An independent set of `J(n+1, w+1)` is a family of `(w+1)`-sets meeting pairwise in at most
`w - 1` points. Fixing a point `x` and deleting it from the members through `x` gives an
independent set of `J(n, w)` (`pullAt`); summing over the `n + 1` points counts every member
`w + 1` times, so `(w+1) |I| ≤ (n+1) · johnsonBound n 4 w`.
-/

open Finset SimpleGraph

namespace Veles.JB

variable {n : ℕ}

/-- Delete the point `x` and renumber: the preimage of `B` under `x.succAbove`. -/
def pullAt (x : Fin (n + 1)) (B : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun i => x.succAbove i ∈ B)

theorem mem_pullAt {x : Fin (n + 1)} {B : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ pullAt x B ↔ x.succAbove i ∈ B := by simp [pullAt]

theorem insert_map_pullAt {x : Fin (n + 1)} {B : Finset (Fin (n + 1))} (hx : x ∈ B) :
    insert x ((pullAt x B).map (Fin.succAboveEmb x)) = B := by
  ext j
  simp only [mem_insert, mem_map, Fin.succAboveEmb_apply, mem_pullAt]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact hx
    · exact hi
  · intro hj
    by_cases hjx : j = x
    · exact Or.inl hjx
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjx
      exact Or.inr ⟨i, hj, rfl⟩

theorem card_pullAt {x : Fin (n + 1)} {B : Finset (Fin (n + 1))} (hx : x ∈ B) :
    (pullAt x B).card + 1 = B.card := by
  conv_rhs => rw [← insert_map_pullAt hx]
  rw [card_insert_of_notMem, card_map]
  simp only [mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
  intro i _ h; exact Fin.succAbove_ne x i h

theorem pullAt_inter (x : Fin (n + 1)) (s t : Finset (Fin (n + 1))) :
    pullAt x (s ∩ t) = pullAt x s ∩ pullAt x t := by
  ext i; simp [mem_pullAt]

theorem pullAt_injOn {x : Fin (n + 1)} {s t : Finset (Fin (n + 1))} (hs : x ∈ s) (ht : x ∈ t)
    (h : pullAt x s = pullAt x t) : s = t := by
  rw [← insert_map_pullAt hs, ← insert_map_pullAt ht, h]

/-- Every independent set of `J(n, w)` has at most `johnsonBound n 4 w` members. -/
theorem card_le_johnsonBound : ∀ (n w : ℕ) (I : Finset {s : Finset (Fin n) // s.card = w}),
    (J(n, w)).IsIndepSet (I : Set _) → I.card ≤ Erdos835.johnsonBound n 4 w
  | 0, w, I, _ => by
    show I.card ≤ 1
    apply card_le_one.2
    intro a _ b _
    apply Subtype.ext
    ext i; exact i.elim0
  | n + 1, 0, I, _ => by
    show I.card ≤ 1
    apply card_le_one.2
    intro a _ b _
    apply Subtype.ext
    rw [card_eq_zero.1 a.2, card_eq_zero.1 b.2]
  | n + 1, w + 1, I, hI => by
    show I.card ≤ if 2 * (w + 1) < 4 then 1 else (n + 1) * Erdos835.johnsonBound n 4 w / (w + 1)
    split_ifs with hw
    · -- w = 0: distinct singletons are adjacent
      apply card_le_one.2
      intro a ha b hb
      by_contra hab
      apply hI ha hb hab
      rw [johnson_adj]
      have : w = 0 := by omega
      subst this
      obtain ⟨p, hp⟩ := card_eq_one.1 a.2
      obtain ⟨q, hq⟩ := card_eq_one.1 b.2
      have hpq : p ≠ q := by
        intro h; apply hab; apply Subtype.ext; rw [hp, hq, h]
      rw [hp, hq, singleton_inter_of_notMem (by simpa using hpq)]; simp
    · -- (w+1) |I| ≤ (n+1) · johnsonBound n 4 w
      rw [Nat.le_div_iff_mul_le (by omega)]
      -- I_x: members through x, pulled back to J(n, w)
      let Ix : Fin (n + 1) → Finset {s : Finset (Fin n) // s.card = w} := fun x =>
        (I.filter (fun s => x ∈ s.val)).attach.image (fun s =>
          ⟨pullAt x s.1.val, by
            have := card_pullAt (mem_filter.1 s.2).2; rw [s.1.2] at this; omega⟩)
      have hIx : ∀ x, (Ix x).card = (I.filter (fun s => x ∈ s.val)).card := by
        intro x
        rw [card_image_of_injective, card_attach]
        intro a b h
        have h' : pullAt x a.1.val = pullAt x b.1.val := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext (pullAt_injOn (mem_filter.1 a.2).2 (mem_filter.1 b.2).2 h'))
      have hind : ∀ x, (J(n, w)).IsIndepSet (Ix x : Set _) := by
        intro x a ha b hb hab hadj
        simp only [Ix, coe_image, Set.mem_image, mem_coe, mem_attach, true_and] at ha hb
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        have hne : a'.1 ≠ b'.1 := fun h =>
          hab (Subtype.ext (congrArg (fun s : {s : Finset (Fin (n + 1)) // s.card = w + 1} =>
            pullAt x s.val) h))
        apply hI (mem_filter.1 a'.2).1 (mem_filter.1 b'.2).1 hne
        rw [johnson_adj] at hadj ⊢
        simp only at hadj
        rw [← pullAt_inter] at hadj
        have := card_pullAt (mem_inter.2 ⟨(mem_filter.1 a'.2).2, (mem_filter.1 b'.2).2⟩)
        omega
      have hsum : ∑ x : Fin (n + 1), (I.filter (fun s => x ∈ s.val)).card = ∑ _s ∈ I, (w + 1) := by
        simp only [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        refine sum_congr rfl (fun s _ => ?_)
        rw [← sum_filter, ← card_eq_sum_ones, filter_mem_eq_inter, univ_inter, s.2]
      calc I.card * (w + 1) = ∑ x : Fin (n + 1), (Ix x).card := by
            rw [sum_congr rfl (fun x _ => hIx x), hsum, sum_const, smul_eq_mul]
        _ ≤ ∑ _x : Fin (n + 1), Erdos835.johnsonBound n 4 w :=
          sum_le_sum (fun x _ => card_le_johnsonBound n w (Ix x) (hind x))
        _ = (n + 1) * Erdos835.johnsonBound n 4 w := by simp

/-- **Upstream `indepNum_johnson_le_johnsonBound`**, proved. -/
theorem indepNum_johnson_le_johnsonBound {n k : ℕ} :
    (J(n, k)).indepNum ≤ Erdos835.johnsonBound n 4 k := by
  obtain ⟨s, hs⟩ := (J(n, k)).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  exact card_le_johnsonBound n k s hs.isIndepSet

end Veles.JB
