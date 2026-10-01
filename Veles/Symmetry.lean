/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Johnson835

/-!
# No colouring with a large prime symmetry

`no_invariant_colouring`: let `k ≥ 1` and `p` a prime with `k + 1 < p ≤ 2k`. No proper
`(k+1)`-colouring of `J(2k, k)` is invariant, in the sense that colour classes go to colour
classes, under a permutation `g` of the points of order `p`.

Proof: the induced permutation of the `k+1` colours has order dividing `p`, and `p ∤ (k+1)!`, so
every colour class is fixed. `g` is a single `p`-cycle (`2k < 2p`) plus `2k - p` fixed points.
The fixed points together with the arc `x, g x, …, g^(p-k-1) x` form a `k`-set `B` with
`|B ∩ g B| = k - 1`: `B` and `g B` are adjacent with the same colour.

For `k = 16` the primes are exactly `19, 23, 29, 31` (the case of veljjanoski's forum post of
28 September 2026); `p = 17 = k + 1` is not covered, since an element of order 17 may permute the
17 colour classes cyclically.
-/

open Finset SimpleGraph Veles.J835

namespace Veles.Sym

variable {k : ℕ}

/-- The image of a vertex under a permutation of the points. -/
def act (g : Equiv.Perm (Fin (2 * k))) (B : V k) : V k :=
  ⟨B.val.map g.toEmbedding, by rw [card_map]; exact B.2⟩

/-- A proper `(k+1)`-colouring uses every colour. -/
theorem surjective_of_proper (hk : 0 < k) {c : V k → Fin (k + 1)}
    (hc : ∀ s t, J(2 * k, k).Adj s t → c s ≠ c t) : Function.Surjective c := by
  intro i
  let R : Finset (Fin (2 * k)) := univ.filter (fun a => a.val < k - 1)
  have hR : R.card = k - 1 := by
    have : R = (range (k - 1)).attachFin (fun j hj => by have := mem_range.1 hj; omega) := by
      ext a; simp [R]
    rw [this, card_attachFin, card_range]
  have h := exists_unique_colour hc hk R hR i
  obtain ⟨B, hB⟩ := card_pos.1 (by rw [h]; norm_num)
  have := (mem_filter.1 hB).1
  obtain ⟨s, hs, rfl⟩ := mem_map.1 this
  exact ⟨s, (mem_filter.1 hs).2⟩

theorem no_invariant_colouring (hk : 0 < k) {p : ℕ} (hp : p.Prime) (h1 : k + 1 < p)
    (h2 : p ≤ 2 * k) (g : Equiv.Perm (Fin (2 * k))) (hg : orderOf g = p)
    (c : V k → Fin (k + 1)) (hc : ∀ s t, J(2 * k, k).Adj s t → c s ≠ c t)
    (σ : Equiv.Perm (Fin (k + 1))) (hinv : ∀ B, c (act g B) = σ (c B)) : False := by
  classical
  -- 1. σ = 1
  have hact_pow : ∀ n B, c (⟨B.val.map (g ^ n).toEmbedding, by rw [card_map]; exact B.2⟩ : V k)
      = (σ ^ n) (c B) := by
    intro n
    induction n with
    | zero =>
      intro B
      have e : (⟨B.val.map (g ^ 0).toEmbedding, by rw [card_map]; exact B.2⟩ : V k) = B := by
        apply Subtype.ext; ext a; simp [Equiv.Perm.one_symm]
      rw [e]; rfl
    | succ n ih =>
      intro B
      have e : (⟨B.val.map (g ^ (n + 1)).toEmbedding, by rw [card_map]; exact B.2⟩ : V k) =
          act g ⟨B.val.map (g ^ n).toEmbedding, by rw [card_map]; exact B.2⟩ := by
        apply Subtype.ext
        ext a
        simp only [act, Finset.mem_map, Equiv.toEmbedding_apply, pow_succ', Equiv.Perm.mul_apply]
        constructor
        · rintro ⟨b, hb, rfl⟩; exact ⟨(g ^ n) b, ⟨b, hb, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩; exact ⟨b, hb, rfl⟩
      rw [e, hinv, ih, pow_succ', Equiv.Perm.mul_apply]
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hσp : σ ^ p = 1 := by
    apply Equiv.ext; intro i
    obtain ⟨B, rfl⟩ := surjective_of_proper hk hc i
    have h := hact_pow p B
    have e : (⟨B.val.map (g ^ p).toEmbedding, by rw [card_map]; exact B.2⟩ : V k) = B := by
      apply Subtype.ext; ext a; simp [hgp, Equiv.Perm.one_symm]
    rw [e] at h
    simp only [Equiv.Perm.one_apply]; exact h.symm
  have hσ1 : σ = 1 := by
    have hdvd : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσp
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      have : p ∣ (k + 1).factorial := by
        rw [← h, show (k + 1).factorial = Fintype.card (Equiv.Perm (Fin (k + 1))) by
          rw [Fintype.card_perm, Fintype.card_fin]]
        exact orderOf_dvd_card
      rw [hp.dvd_factorial] at this; omega
  subst hσ1
  -- 2. g is one p-cycle
  have hcyc : g.IsCycle := Equiv.Perm.isCycle_of_prime_order' (hg ▸ hp)
    (by rw [Fintype.card_fin, hg]; omega)
  have hsupp : g.support.card = p := by rw [← hcyc.orderOf, hg]
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := by
    obtain ⟨x, hx, -⟩ := hcyc; exact ⟨x, hx⟩
  -- injectivity of i ↦ g^i x below p
  have hinj : ∀ i j, i < p → j < p → (g ^ i) x = (g ^ j) x → i = j := by
    intro i j hi hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hij | hij
    · have e : (g ^ j) x = (g ^ i) ((g ^ (j - i)) x) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
      rw [e] at h
      have h' : (g ^ (j - i)) x = x := ((g ^ i).injective h).symm
      have h1 : g ^ (j - i) = 1 := (hcyc.pow_eq_one_iff' hx).2 h'
      have := Nat.le_of_dvd (by omega) (hg ▸ orderOf_dvd_of_pow_eq_one h1)
      omega
    · have e : (g ^ i) x = (g ^ j) ((g ^ (i - j)) x) := by
        rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
      rw [e] at h
      have h' : (g ^ (i - j)) x = x := (g ^ j).injective h
      have h1 : g ^ (i - j) = 1 := (hcyc.pow_eq_one_iff' hx).2 h'
      have := Nat.le_of_dvd (by omega) (hg ▸ orderOf_dvd_of_pow_eq_one h1)
      omega
  -- 3. the k-set B = fixed points ∪ arc
  set F : Finset (Fin (2 * k)) := univ.filter (fun y => g y = y) with hF
  have hFc : F.card = 2 * k - p := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * k))))
      (fun y => g y = y)
    have hs : univ.filter (fun y => ¬ g y = y) = g.support := by
      ext y; simp [Equiv.Perm.mem_support]
    rw [hs, hsupp, card_univ, Fintype.card_fin] at this
    rw [hF]; omega
  set a := p - k with ha
  let arc : ℕ → Fin (2 * k) := fun i => (g ^ i) x
  have harc_moved : ∀ i, g (arc i) ≠ arc i := fun i =>
    Equiv.Perm.mem_support.1 (Equiv.Perm.pow_apply_mem_support.2 (Equiv.Perm.mem_support.2 hx))
  have hinjOn : ∀ n, n ≤ p → Set.InjOn arc (range n : Set ℕ) := fun n hn i hi j hj h =>
    hinj i j (by simp at hi; omega) (by simp at hj; omega) h
  set A := (range a).image arc with hA
  set A1 := (range (a + 1)).image arc with hA1
  have hAc : A.card = a := by rw [hA, card_image_of_injOn (hinjOn a (by omega)), card_range]
  have hA1c : A1.card = a + 1 := by
    rw [hA1, card_image_of_injOn (hinjOn (a + 1) (by omega)), card_range]
  have hgA : A.map g.toEmbedding = (range a).image (fun i => arc (i + 1)) := by
    ext z
    simp only [hA, mem_map, mem_image, mem_range, Equiv.toEmbedding_apply, arc]
    constructor
    · rintro ⟨w, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(g ^ i) x, ⟨i, hi, rfl⟩, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
  have hunion : A ∪ A.map g.toEmbedding = A1 := by
    rw [hgA]
    ext z
    simp only [hA, hA1, mem_union, mem_image, mem_range]
    constructor
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, by omega, rfl⟩
      · exact ⟨i + 1, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.lt_or_ge i a with h | h
      · exact Or.inl ⟨i, h, rfl⟩
      · right
        refine ⟨i - 1, by omega, ?_⟩
        have hi1 : i - 1 + 1 = i := by
          have : 1 ≤ i := by omega
          omega
        rw [hi1]
  have hFdisj : ∀ z ∈ F, ∀ i, z ≠ arc i := by
    intro z hz i h
    rw [hF, mem_filter] at hz
    exact harc_moved i (h ▸ hz.2)
  have hdisjA : Disjoint F A := by
    rw [Finset.disjoint_left]; intro z hz hzA
    obtain ⟨i, -, rfl⟩ := mem_image.1 hzA
    exact hFdisj _ hz i rfl
  have hdisjA1 : Disjoint F A1 := by
    rw [Finset.disjoint_left]; intro z hz hzA
    obtain ⟨i, -, rfl⟩ := mem_image.1 hzA
    exact hFdisj _ hz i rfl
  have hmapF : F.map g.toEmbedding = F := by
    ext z
    simp only [hF, mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩; rw [hw, hw]
    · intro hz; exact ⟨z, hz, hz⟩
  have hBc : (F ∪ A).card = k := by rw [card_union_of_disjoint hdisjA, hFc, hAc]; omega
  set B : V k := ⟨F ∪ A, hBc⟩
  have hgB : (act g B).val = F ∪ A.map g.toEmbedding := by
    simp only [act, B, map_union, hmapF]
  have hcup : ((act g B).val ∪ B.val).card = k + 1 := by
    rw [hgB]
    have : F ∪ A.map g.toEmbedding ∪ (F ∪ A) = F ∪ A1 := by
      rw [← hunion]; ext z; simp only [mem_union]; tauto
    rw [this, card_union_of_disjoint hdisjA1, hFc, hA1c]; omega
  have hadj : J(2 * k, k).Adj B (act g B) := by
    rw [johnson_adj]
    have := card_union_add_card_inter (act g B).val B.val
    rw [hcup, (act g B).2, B.2, inter_comm] at this
    omega
  exact hc B (act g B) hadj (by rw [hinv]; rfl)

/-- The case `k = 16`: the primes `19, 23, 29, 31`. -/
theorem no_invariant_colouring_16 {p : ℕ} (hp : p ∈ ({19, 23, 29, 31} : Finset ℕ))
    (g : Equiv.Perm (Fin (2 * 16))) (hg : orderOf g = p)
    (c : V 16 → Fin (16 + 1)) (hc : ∀ s t, J(2 * 16, 16).Adj s t → c s ≠ c t)
    (σ : Equiv.Perm (Fin (16 + 1))) (hinv : ∀ B, c (act g B) = σ (c B)) : False := by
  have hpp : p.Prime := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hr : 16 + 1 < p ∧ p ≤ 2 * 16 := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  exact no_invariant_colouring (by norm_num) hpp hr.1 hr.2 g hg c hc σ hinv

end Veles.Sym
