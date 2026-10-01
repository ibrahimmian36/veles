/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Upstream

/-!
# Exact covers by blocks

The semantic core of the certificates. Points are natural numbers below `v`. An *item* is a
`(k-1)`-subset of `range v`, a *block* a `k`-subset. Given a set `X` of items already covered,
`IsCover v k X F` says the blocks `F` cover every item outside `X` exactly once and no item of `X`.
A Steiner system `S(k-1, k, v)` is exactly a cover of the empty state (`isCover_of_steiner`).

Two rules turn a search tree into a proof that no cover exists (`NoExt`):
* `noExt_branch`: pick an uncovered item `T`; the block covering it is `insert x T` for some `x`,
  and it must be compatible with `X`; if no compatible choice extends, nothing does.
* `noExt_of_map`: a bijection of `range v` that carries `X` onto `Y` carries covers of `X` to
  covers of `Y`; so if `Y` has none, neither has `X`.
-/

open Finset

namespace Veles.Cover

/-- `F` covers exactly the items outside `X`. -/
def IsCover (v k : ℕ) (X : Set (Finset ℕ)) (F : Finset (Finset ℕ)) : Prop :=
  (∀ B ∈ F, B ⊆ range v ∧ B.card = k) ∧
  ∀ T ⊆ range v, T.card + 1 = k →
    (T ∈ X → ∀ B ∈ F, ¬ T ⊆ B) ∧ (T ∉ X → ∃! B, B ∈ F ∧ T ⊆ B)

/-- No cover of the items outside `X` exists. -/
def NoExt (v k : ℕ) (X : Set (Finset ℕ)) : Prop := ∀ F, ¬ IsCover v k X F

/-- The items of a block: the block with one point removed. -/
def items (B : Finset ℕ) : Set (Finset ℕ) := {T | ∃ y ∈ B, T = B.erase y}

theorem mem_items_iff {k : ℕ} {B T : Finset ℕ} (hB : B.card = k) :
    T ∈ items B ↔ T ⊆ B ∧ T.card + 1 = k := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨erase_subset _ _, by rw [card_erase_of_mem hy, ← hB]; have := card_pos.2 ⟨y, hy⟩; omega⟩
  · rintro ⟨hTB, hT⟩
    have hc : (B \ T).card = 1 := by rw [card_sdiff_of_subset hTB]; omega
    obtain ⟨y, hy⟩ := card_eq_one.1 hc
    have hyB : y ∈ B := (mem_sdiff.1 (hy ▸ mem_singleton_self y)).1
    have hyT : y ∉ T := (mem_sdiff.1 (hy ▸ mem_singleton_self y)).2
    refine ⟨y, hyB, ?_⟩
    ext z
    simp only [mem_erase]
    constructor
    · intro hz; exact ⟨fun h => hyT (h ▸ hz), hTB hz⟩
    · rintro ⟨hzy, hzB⟩
      by_contra hzT
      have : z ∈ B \ T := mem_sdiff.2 ⟨hzB, hzT⟩
      rw [hy, mem_singleton] at this
      exact hzy this

/-- A `k`-set containing a `(k-1)`-set `T` is `insert x T` for a point `x ∉ T`. -/
theorem eq_insert_of_card {k : ℕ} {B T : Finset ℕ} (hTB : T ⊆ B) (hB : B.card = k)
    (hT : T.card + 1 = k) : ∃ x ∈ B, x ∉ T ∧ B = insert x T := by
  have hc : (B \ T).card = 1 := by rw [card_sdiff_of_subset hTB]; omega
  obtain ⟨x, hx⟩ := card_eq_one.1 hc
  have hx' := mem_sdiff.1 (hx ▸ mem_singleton_self x)
  refine ⟨x, hx'.1, hx'.2, ?_⟩
  ext z
  simp only [mem_insert]
  constructor
  · intro hz
    by_cases hzT : z ∈ T
    · exact Or.inr hzT
    · left
      have : z ∈ B \ T := mem_sdiff.2 ⟨hz, hzT⟩
      rwa [hx, mem_singleton] at this
  · rintro (rfl | hz)
    · exact hx'.1
    · exact hTB hz

/-- **Branch rule.** -/
theorem noExt_branch {v k : ℕ} {X : Set (Finset ℕ)} {T : Finset ℕ} (hT : T ⊆ range v)
    (hTk : T.card + 1 = k) (hTX : T ∉ X)
    (h : ∀ x < v, x ∉ T → (∀ y ∈ insert x T, (insert x T).erase y ∉ X) →
      NoExt v k (X ∪ items (insert x T))) :
    NoExt v k X := by
  intro F hF
  obtain ⟨B, ⟨hBF, hTB⟩, huniq⟩ := (hF.2 T hT hTk).2 hTX
  obtain ⟨hBv, hBk⟩ := hF.1 B hBF
  obtain ⟨x, hxB, hxT, rfl⟩ := eq_insert_of_card hTB hBk hTk
  have hxv : x < v := mem_range.1 (hBv hxB)
  refine h x hxv hxT ?_ (F.erase (insert x T)) ⟨?_, ?_⟩
  · -- compatibility: no item of the block is already covered
    intro y hy hyX
    have hsub : (insert x T).erase y ⊆ range v := (erase_subset _ _).trans hBv
    have hcard : ((insert x T).erase y).card + 1 = k := by
      rw [card_erase_of_mem hy, ← hBk]; have := card_pos.2 ⟨y, hy⟩; omega
    exact (hF.2 _ hsub hcard).1 hyX _ hBF (erase_subset _ _)
  · intro B' hB'
    exact hF.1 B' (mem_of_mem_erase hB')
  · intro T' hT' hT'k
    constructor
    · rintro (hX | hI) B' hB' hsub
      · exact (hF.2 T' hT' hT'k).1 hX B' (mem_of_mem_erase hB') hsub
      · by_cases hX : T' ∈ X
        · exact (hF.2 T' hT' hT'k).1 hX B' (mem_of_mem_erase hB') hsub
        · obtain ⟨_, _, hu⟩ := (hF.2 T' hT' hT'k).2 hX
          have h1 := hu B' ⟨mem_of_mem_erase hB', hsub⟩
          have h2 := hu (insert x T) ⟨hBF, ((mem_items_iff hBk).1 hI).1⟩
          exact (ne_of_mem_erase hB') (h1.trans h2.symm)
    · intro hnot
      have hX : T' ∉ X := fun h => hnot (Or.inl h)
      have hI : T' ∉ items (insert x T) := fun h => hnot (Or.inr h)
      obtain ⟨B'', ⟨hB''F, hB''⟩, hu⟩ := (hF.2 T' hT' hT'k).2 hX
      have hne : B'' ≠ insert x T := by
        rintro rfl; exact hI ((mem_items_iff hBk).2 ⟨hB'', hT'k⟩)
      refine ⟨B'', ⟨mem_erase.2 ⟨hne, hB''F⟩, hB''⟩, ?_⟩
      rintro B' ⟨hB'F, hB'⟩
      exact hu B' ⟨mem_of_mem_erase hB'F, hB'⟩

/-- **Relabelling rule.** A map `f` injective on `range v` and into `range v` that sends the
items of `X` exactly to the items of `Y` transfers `NoExt` from `Y` to `X`. -/
theorem noExt_of_map {v k : ℕ} {X Y : Set (Finset ℕ)} (f : ℕ → ℕ)
    (hinj : Set.InjOn f (range v)) (hmap : ∀ i < v, f i < v)
    (hXY : ∀ T ⊆ range v, T.card + 1 = k → (T ∈ X ↔ T.image f ∈ Y)) (hY : NoExt v k Y) :
    NoExt v k X := by
  intro F hF
  have hmaps : Set.MapsTo f (range v : Set ℕ) (range v : Set ℕ) := fun i hi => by
    simp only [coe_range, Set.mem_Iio] at hi ⊢; exact hmap i hi
  have hsurj : Set.SurjOn f (range v : Set ℕ) (range v : Set ℕ) :=
    Finset.surjOn_of_injOn_of_card_le f hmaps hinj le_rfl
  -- images of subsets of `range v`
  have img_sub : ∀ {S : Finset ℕ}, S ⊆ range v → S.image f ⊆ range v := fun hS z hz => by
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hz
    exact mem_range.2 (hmap a (mem_range.1 (hS ha)))
  have img_card : ∀ {S : Finset ℕ}, S ⊆ range v → (S.image f).card = S.card := fun hS =>
    card_image_of_injOn (fun a ha b hb h => hinj (mem_coe.2 (hS ha)) (mem_coe.2 (hS hb)) h)
  have img_le : ∀ {S S' : Finset ℕ}, S ⊆ range v → S' ⊆ range v →
      (S.image f ⊆ S'.image f ↔ S ⊆ S') := fun hS hS' => by
    constructor
    · intro h z hz
      obtain ⟨w, hw, hwz⟩ := mem_image.1 (h (mem_image_of_mem f hz))
      have := hinj (mem_coe.2 (hS' hw)) (mem_coe.2 (hS hz)) hwz
      exact this ▸ hw
    · exact image_subset_image
  -- every item of `range v` is the image of an item
  have preimg : ∀ {T' : Finset ℕ}, T' ⊆ range v →
      ∃ T ⊆ range v, T.image f = T' := fun {T'} hT' => by
    refine ⟨(range v).filter (fun i => f i ∈ T'), filter_subset _ _, ?_⟩
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hz
      exact (mem_filter.1 ha).2
    · intro hz
      obtain ⟨a, ha, haz⟩ := hsurj (mem_coe.2 (hT' hz))
      exact mem_image.2 ⟨a, mem_filter.2 ⟨mem_coe.1 ha, haz ▸ hz⟩, haz⟩
  apply hY (F.image (fun B => B.image f))
  refine ⟨?_, ?_⟩
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨hBv, hBk⟩ := hF.1 B hB
    exact ⟨img_sub hBv, (img_card hBv).trans hBk⟩
  · intro T' hT' hT'k
    obtain ⟨T, hT, rfl⟩ := preimg hT'
    have hTk : T.card + 1 = k := (img_card hT) ▸ hT'k
    have hiff := hXY T hT hTk
    constructor
    · intro hY' B' hB' hsub
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      exact (hF.2 T hT hTk).1 (hiff.2 hY') B hB ((img_le hT (hF.1 B hB).1).1 hsub)
    · intro hY'
      obtain ⟨B, ⟨hBF, hTB⟩, hu⟩ := (hF.2 T hT hTk).2 (fun h => hY' (hiff.1 h))
      refine ⟨B.image f, ⟨mem_image_of_mem _ hBF, image_subset_image hTB⟩, ?_⟩
      rintro B'' ⟨hB''F, hB''⟩
      obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB''F
      rw [hu B₀ ⟨hB₀, (img_le hT (hF.1 B₀ hB₀).1).1 hB''⟩]

/-- A Steiner system `S(k-1, k, v)` (in the upstream sense) is a cover of the empty state. -/
theorem isCover_of_steiner {t k v : ℕ} (hk : t + 1 = k) (S : SteinerSystems.SteinerSystem t k v) :
    IsCover v k ∅ (S.blocks.image (fun B => B.map Fin.valEmbedding)) := by
  refine ⟨?_, ?_⟩
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    refine ⟨fun z hz => ?_, by rw [card_map]; exact S.block_card B hB⟩
    obtain ⟨a, -, rfl⟩ := mem_map.1 hz
    exact mem_range.2 a.isLt
  · intro T hT hTk
    refine ⟨fun h => absurd h (Set.notMem_empty T), fun _ => ?_⟩
    -- pull `T` back to `Fin v`
    set R : Finset (Fin v) := univ.filter (fun a => a.val ∈ T) with hR
    have hRT : R.map Fin.valEmbedding = T := by
      ext z
      simp only [mem_map, hR, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hz; exact ⟨⟨z, mem_range.1 (hT hz)⟩, hz, rfl⟩
    have hRc : R.card = t := by
      have := congrArg card hRT; rw [card_map] at this; omega
    have h1 := S.cover_unique R hRc
    obtain ⟨B, hB⟩ := card_eq_one.1 h1
    have hBmem : B ∈ S.blocks.filter (R ⊆ ·) := hB ▸ mem_singleton_self B
    rw [mem_filter] at hBmem
    refine ⟨B.map Fin.valEmbedding, ⟨mem_image_of_mem _ hBmem.1, hRT ▸ map_subset_map.2 hBmem.2⟩, ?_⟩
    rintro B'' ⟨hB''F, hB''⟩
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB''F
    have : R ⊆ B₀ := by rw [← hRT] at hB''; exact map_subset_map.1 hB''
    have hmem : B₀ ∈ S.blocks.filter (R ⊆ ·) := mem_filter.2 ⟨hB₀, this⟩
    rw [hB, mem_singleton] at hmem
    rw [hmem]

/-- If the empty state has no cover, no Steiner system `S(k-1, k, v)` exists. -/
theorem isEmpty_steiner_of_noExt {t k v : ℕ} (hk : t + 1 = k) (h : NoExt v k ∅) :
    IsEmpty (SteinerSystems.SteinerSystem t k v) :=
  ⟨fun S => h _ (isCover_of_steiner hk S)⟩

end Veles.Cover
