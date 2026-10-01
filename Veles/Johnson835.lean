/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Steiner

/-!
# Erdős Problem 835: colourings, chromatic number, large sets

For `k ≥ 1`, with the upstream definitions:

* `clique_bound`: `k + 1 ≤ χ(J(2k, k))` (the sets `T ∪ {x}` over a `(k-1)`-set `T`);
* `property_iff_proper`: `Property k` holds iff `J(2k, k)` has a proper `(k+1)`-colouring;
* `property_iff_chromaticNumber`: `χ(J(2k, k)) = k + 1 ↔ Property k` (upstream's statement);
* `property_iff_largeSet`: `Property k ↔ LargeSet (k-1) k (2k) (k+1)`;
* `prime_of_steiner`: an `S(k-1, k, 2k)` forces `k + 1` prime (Ma and Tang's theorem, here via
  derived systems and the block count);
* `lt_chromaticNumber_of_not_prime`: `k + 1` not prime gives `k + 1 < χ(J(2k, k))`.
-/

open Finset SimpleGraph SteinerSystems Veles.Steiner

namespace Veles.J835

variable {k : ℕ}

/-- The vertex type of `J(2k, k)`. -/
abbrev V (k : ℕ) := {s : Finset (Fin (2 * k)) // s.card = k}

/-- Two distinct `k`-sets in a common `(k+1)`-set are adjacent. -/
theorem adj_of_subset {A : Finset (Fin (2 * k))} (hA : A.card = k + 1) {s t : V k}
    (hs : s.val ⊆ A) (ht : t.val ⊆ A) (hst : s ≠ t) : J(2 * k, k).Adj s t := by
  rw [johnson_adj]
  have hne : s.val ≠ t.val := fun h => hst (Subtype.ext h)
  have hu : (s.val ∪ t.val).card ≤ k + 1 := hA ▸ card_le_card (union_subset hs ht)
  have hu' : k + 1 ≤ (s.val ∪ t.val).card := by
    by_contra hlt
    have h1 : (s.val ∪ t.val).card ≤ k := by omega
    have h2 : s.val ∪ t.val = s.val :=
      (eq_of_subset_of_card_le subset_union_left (by rw [s.2]; exact h1)).symm
    have h3 : s.val ∪ t.val = t.val :=
      (eq_of_subset_of_card_le subset_union_right (by rw [t.2]; exact h1)).symm
    exact hne (h2.symm.trans h3)
  have := card_union_add_card_inter s.val t.val
  rw [s.2, t.2] at this
  omega

/-- Adjacent vertices lie in the `(k+1)`-set `s ∪ t`. -/
theorem card_union_of_adj {s t : V k} (h : J(2 * k, k).Adj s t) : (s.val ∪ t.val).card = k + 1 := by
  rw [johnson_adj] at h
  have := card_union_add_card_inter s.val t.val
  rw [s.2, t.2] at this
  omega

/-- The `k`-subsets of a `(k+1)`-set, as vertices. -/
def subsOf (A : Finset (Fin (2 * k))) : Finset (V k) := univ.filter (fun s : V k => s.val ⊂ A)

theorem card_subsOf {A : Finset (Fin (2 * k))} (hA : A.card = k + 1) : (subsOf A).card = k + 1 := by
  have : (subsOf A).map ⟨Subtype.val, Subtype.val_injective⟩ = A.powersetCard k := by
    ext u
    simp only [subsOf, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
      mem_powersetCard]
    constructor
    · rintro ⟨s, hs, rfl⟩; exact ⟨hs.subset, s.2⟩
    · rintro ⟨hu, hc⟩
      refine ⟨⟨u, hc⟩, ssubset_of_subset_of_ne hu ?_, rfl⟩
      intro h
      have hu' : u = A := h
      rw [hu'] at hc; omega
  rw [← card_map, this, card_powersetCard, hA, Nat.choose_succ_self_right]

/-- `Property k` is exactly a proper `(k+1)`-colouring of `J(2k, k)`. -/
theorem property_iff_proper (hk : 0 < k) :
    Erdos835.Property k ↔ ∃ c : V k → Fin (k + 1), ∀ s t, J(2 * k, k).Adj s t → c s ≠ c t := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun s t hst => ?_⟩
    have hA := card_union_of_adj hst
    have himg := hc _ hA
    -- the image has k+1 elements, so `c` is injective on `subsOf A`
    have hinj : Set.InjOn c (subsOf (s.val ∪ t.val) : Set (V k)) := by
      apply Finset.injOn_of_card_image_eq
      have : (subsOf (s.val ∪ t.val)).image c = univ := himg
      rw [this, card_univ, Fintype.card_fin, card_subsOf hA]
    intro heq
    have hs : s ∈ subsOf (s.val ∪ t.val) := by
      simp only [subsOf, mem_filter, mem_univ, true_and]
      refine ssubset_of_subset_of_ne subset_union_left (fun h => ?_)
      have := congrArg card h; rw [s.2, hA] at this; omega
    have ht : t ∈ subsOf (s.val ∪ t.val) := by
      simp only [subsOf, mem_filter, mem_univ, true_and]
      refine ssubset_of_subset_of_ne subset_union_right (fun h => ?_)
      have := congrArg card h; rw [t.2, hA] at this; omega
    exact hst.ne (hinj hs ht heq)
  · rintro ⟨c, hc⟩
    refine ⟨c, fun A hA => ?_⟩
    apply eq_univ_of_card
    rw [Fintype.card_fin, card_image_of_injOn]
    · exact card_subsOf hA
    intro s hs t ht heq
    by_contra hne
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hs ht
    exact hc s t (adj_of_subset hA hs.subset ht.subset hne) heq

/-- **Clique bound.** `k + 1 ≤ χ(J(2k, k))` for `k ≥ 1`. -/
theorem clique_bound (hk : 0 < k) : ((k + 1 : ℕ) : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
  -- T = the first k-1 points; the k+1 vertices T ∪ {k-1+j}
  let T : Finset (Fin (2 * k)) := univ.filter (fun i => i.val < k - 1)
  have hTc : T.card = k - 1 := by
    have : T = (range (k - 1)).attachFin (fun i hi => by
        have := mem_range.1 hi; omega) := by
      ext i; simp [T]
    rw [this, card_attachFin, card_range]
  let pt : Fin (k + 1) → Fin (2 * k) := fun j => ⟨k - 1 + j.val, by omega⟩
  have hpt : ∀ j, pt j ∉ T := fun j h => by simp [T, pt] at h
  let f : Fin (k + 1) → V k := fun j => ⟨insert (pt j) T, by rw [card_insert_of_notMem (hpt j), hTc]; omega⟩
  apply le_chromaticNumber_of_pairwise_adj (by simp) f
  intro i j hij
  have hij' : pt i ≠ pt j := fun h => hij (Fin.ext (by simpa [pt] using congrArg Fin.val h))
  refine adj_of_subset (A := insert (pt i) (insert (pt j) T)) ?_ ?_ ?_ ?_
  · rw [card_insert_of_notMem, card_insert_of_notMem (hpt j), hTc]
    · omega
    · simp only [mem_insert, not_or]; exact ⟨hij', hpt i⟩
  · intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_of_mem hx)
  · intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact mem_insert_of_mem (mem_insert_self _ _)
    · exact mem_insert_of_mem (mem_insert_of_mem hx)
  · intro h
    have : pt i ∈ insert (pt j) T := by
      have := congrArg Subtype.val h; simp only [f] at this; rw [← this]; exact mem_insert_self _ _
    rcases mem_insert.1 this with h' | h'
    · exact hij' h'
    · exact hpt i h'

/-- **Upstream `property_iff_chromaticNumber`**, proved. -/
theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    J(2 * k, k).chromaticNumber = k + 1 ↔ Erdos835.Property k := by
  rw [property_iff_proper hk]
  constructor
  · intro h
    have hc : J(2 * k, k).Colorable (k + 1) := by
      rw [← chromaticNumber_le_iff_colorable]; rw [h]; norm_cast
    obtain ⟨C⟩ := hc
    exact ⟨C, fun s t hst => C.valid hst⟩
  · rintro ⟨c, hc⟩
    apply le_antisymm
    · have : J(2 * k, k).Colorable (k + 1) := ⟨Coloring.mk c (fun h => hc _ _ h)⟩
      exact_mod_cast this.chromaticNumber_le
    · exact_mod_cast clique_bound hk

/-- The `k`-sets through a `(k-1)`-set `R` are `insert x R`, `x ∉ R`. -/
theorem exists_unique_colour {c : V k → Fin (k + 1)}
    (hc : ∀ s t, J(2 * k, k).Adj s t → c s ≠ c t) (hk : 0 < k)
    (R : Finset (Fin (2 * k))) (hR : R.card = k - 1) (i : Fin (k + 1)) :
    (((univ.filter (fun s : V k => c s = i)).map ⟨Subtype.val, Subtype.val_injective⟩).filter
      (R ⊆ ·)).card = 1 := by
  -- the candidates: g x = insert x R for x ∉ R
  have hout : (univ \ R).card = k + 1 := by rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hR]; omega
  let g : (univ \ R : Finset (Fin (2 * k))) → V k := fun x =>
    ⟨insert x.1 R, by rw [card_insert_of_notMem (mem_sdiff.1 x.2).2, hR]; omega⟩
  have hginj : Function.Injective g := by
    intro x y h
    have h' := congrArg Subtype.val h
    simp only [g] at h'
    have : x.1 ∈ insert y.1 R := h' ▸ mem_insert_self _ _
    rcases mem_insert.1 this with h1 | h1
    · exact Subtype.ext h1
    · exact absurd h1 (mem_sdiff.1 x.2).2
  -- colours of the candidates are pairwise distinct
  have hcinj : Function.Injective (c ∘ g) := by
    intro x y hxy
    by_contra hne
    have hne' : g x ≠ g y := fun h => hne (hginj h)
    apply hc (g x) (g y) _ hxy
    rw [johnson_adj]
    have hx := (mem_sdiff.1 x.2).2
    have hy := (mem_sdiff.1 y.2).2
    have hxy' : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    have : insert x.1 R ∩ insert y.1 R = R := by
      ext z; simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact absurd (h1.symm.trans h2) hxy'
        · exact h2
        · exact h1
        · exact h1
      · intro h; exact ⟨Or.inr h, Or.inr h⟩
    simp only [g]; rw [this, hR]; omega
  have hbij : Function.Bijective (c ∘ g) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hcinj, by rw [Fintype.card_coe, hout, Fintype.card_fin]⟩
  obtain ⟨x, hx, hu⟩ := hbij.existsUnique i
  rw [card_eq_one]
  refine ⟨(g x).val, ?_⟩
  ext B
  simp only [mem_filter, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_singleton]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hRs⟩
    -- s = insert y R for the y ∈ s \ R
    have hc' : (s.val \ R).card = 1 := by rw [card_sdiff_of_subset hRs, s.2, hR]; omega
    obtain ⟨y, hy⟩ := card_eq_one.1 hc'
    have hy' := mem_sdiff.1 (hy ▸ mem_singleton_self y)
    have hsy : s = g ⟨y, mem_sdiff.2 ⟨mem_univ _, hy'.2⟩⟩ := by
      apply Subtype.ext
      simp only [g]
      ext z; simp only [mem_insert]
      constructor
      · intro hz
        by_cases hzR : z ∈ R
        · exact Or.inr hzR
        · left; have : z ∈ s.val \ R := mem_sdiff.2 ⟨hz, hzR⟩; rwa [hy, mem_singleton] at this
      · rintro (rfl | hz)
        · exact hy'.1
        · exact hRs hz
    have := hu ⟨y, mem_sdiff.2 ⟨mem_univ _, hy'.2⟩⟩ (by simp only [Function.comp_apply]; rw [← hsy]; exact hs)
    rw [hsy, this]
  · rintro rfl
    refine ⟨⟨g x, hx, rfl⟩, ?_⟩
    simp only [g]; exact subset_insert _ _

/-- `Property k ↔` a large set `LS(k-1, k, 2k)` of `k+1` Steiner systems. -/
theorem property_iff_largeSet (hk : 0 < k) :
    Erdos835.Property k ↔ LargeSet (k - 1) k (2 * k) (k + 1) := by
  rw [property_iff_proper hk]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => ⟨(univ.filter (fun s : V k => c s = i)).map ⟨Subtype.val, Subtype.val_injective⟩,
      fun B hB => ?_, fun R hR => exists_unique_colour hc hk R hR i⟩, fun s hs => ?_⟩
    · obtain ⟨s, -, rfl⟩ := mem_map.1 hB; exact s.2
    · refine ⟨c ⟨s, hs⟩, ?_, ?_⟩
      · simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk]
        exact ⟨⟨s, hs⟩, rfl, rfl⟩
      · intro j hj
        simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hj
        obtain ⟨u, hu, hus⟩ := hj
        have : u = ⟨s, hs⟩ := Subtype.ext hus
        rw [← hu, this]
  · rintro ⟨D, hD⟩
    classical
    let c : V k → Fin (k + 1) := fun s => (hD s.val s.2).choose
    refine ⟨c, fun s t hst heq => ?_⟩
    have hs := (hD s.val s.2).choose_spec.1
    have ht := (hD t.val t.2).choose_spec.1
    set i := c s
    have ht' : t.val ∈ (D i).blocks := heq ▸ ht
    -- R = s ∩ t has k - 1 points and lies in two blocks of D i
    have hR : (s.val ∩ t.val).card = k - 1 := by rw [johnson_adj] at hst; omega
    have h1 := (D i).cover_unique _ hR
    have hne : s.val ≠ t.val := fun h => hst.ne (Subtype.ext h)
    have h2 : 2 ≤ ((D i).blocks.filter ((s.val ∩ t.val) ⊆ ·)).card := by
      refine (card_pair hne).symm.le.trans (card_le_card ?_)
      intro B hB
      rcases mem_insert.1 hB with rfl | hB
      · exact mem_filter.2 ⟨hs, inter_subset_left⟩
      · rw [mem_singleton] at hB; subst hB; exact mem_filter.2 ⟨ht', inter_subset_right⟩
    omega

/-- A `(k+1)`-colouring gives an `S(k-1, k, 2k)` (any colour class). -/
theorem steiner_of_property (hk : 0 < k) (h : Erdos835.Property k) :
    Nonempty (SteinerSystem (k - 1) k (2 * k)) := by
  obtain ⟨D, -⟩ := (property_iff_largeSet hk).1 h
  exact ⟨D 0⟩

/-- `p ∤ (k+p)(k+p-1)...(k+p-j+1)` for `j ≤ p - 1` when the prime `p` divides `k + 1`. -/
theorem not_dvd_descFactorial {p : ℕ} (hp : p.Prime) (hpk : p ∣ k + 1) :
    ∀ j, j + 1 ≤ p → ¬ p ∣ (k + p).descFactorial j
  | 0, _ => by rw [Nat.descFactorial_zero]; exact hp.not_dvd_one
  | j + 1, hj => by
    rw [Nat.descFactorial_succ]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · -- p ∣ k + p - j, and k + p - j = (k + 1) + (p - 1 - j) with 0 < p - 1 - j < p
      have e : k + p - j = (k + 1) + (p - 1 - j) := by omega
      rw [e] at h1
      have h3 : p ∣ p - 1 - j := (Nat.dvd_add_right hpk).1 h1
      have h4 : 0 < p - 1 - j := by omega
      exact absurd (Nat.le_of_dvd h4 h3) (by omega)
    · exact not_dvd_descFactorial hp hpk j (by omega) h1

/-- **Ma–Tang.** An `S(k-1, k, 2k)` with `k ≥ 1` forces `k + 1` prime. -/
theorem prime_of_steiner (hk : 0 < k) (h : Nonempty (SteinerSystem (k - 1) k (2 * k))) :
    (k + 1).Prime := by
  by_contra hnp
  have h2 : 2 ≤ k + 1 := by omega
  set p := (k + 1).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpk : p ∣ k + 1 := Nat.minFac_dvd _
  have hplt : p < k + 1 := by
    rcases (Nat.minFac_le (by omega : 0 < k + 1)).lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ hp) hnp
  have hp2 := hp.two_le
  -- derive k - p times: S(p - 1, p, k + p)
  have hS := nonempty_iterate (by omega) (by omega) h (k - p) (by omega)
  have e1 : k - 1 - (k - p) = p - 1 := by omega
  have e2 : k - (k - p) = p := by omega
  have e3 : 2 * k - (k - p) = k + p := by omega
  rw [e1, e2, e3] at hS
  have hdvd := choose_dvd hS.some
  rw [show p.choose (p - 1) = p by
    rw [Nat.choose_symm_of_eq_add (by omega : p = (p - 1) + 1), Nat.choose_one_right]] at hdvd
  -- p ∣ C(k+p, p-1), hence p ∣ (p-1)! * C(k+p, p-1) = descFactorial
  have : p ∣ (k + p).descFactorial (p - 1) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; exact Dvd.dvd.mul_left hdvd _
  exact not_dvd_descFactorial hp hpk (p - 1) (by have := hp.one_lt; omega) this

/-- **Upstream `johnson_chromaticNumber_composite`** (with `¬ (k+1).Prime` for `Composite`). -/
theorem lt_chromaticNumber_of_not_prime (hk : 0 < k) (h : ¬ (k + 1).Prime) :
    ((k + 1 : ℕ) : ℕ∞) < J(2 * k, k).chromaticNumber := by
  refine lt_of_le_of_ne (clique_bound hk) (fun heq => h ?_)
  exact prime_of_steiner hk (steiner_of_property hk ((property_iff_chromaticNumber k hk).1 (by
    rw [← heq]; norm_cast)))

/-- **Upstream `johnson_chromaticNumber_odd`**. -/
theorem lt_chromaticNumber_of_odd (hk : 2 < k) (h : Odd k) :
    ((k + 1 : ℕ) : ℕ∞) < J(2 * k, k).chromaticNumber := by
  refine lt_chromaticNumber_of_not_prime (by omega) (fun hp => ?_)
  obtain ⟨m, rfl⟩ := h
  have : 2 ∣ 2 * m + 1 + 1 := ⟨m + 1, by ring⟩
  rcases hp.eq_one_or_self_of_dvd 2 this with h2 | h2 <;> omega

end Veles.J835
