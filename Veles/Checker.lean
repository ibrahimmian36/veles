/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Bits

/-!
# The certificate checker

A certificate for `NoExt v (t + 1) (dec X)` is a stream of 16-bit fields, packed 256 to a word:

* a nonzero field `T` is a branch on the item with point mask `T`: the checker verifies that `T`
  is a `t`-subset of `range v` not yet covered, then replays one subtree for each compatible block
  `T ∪ {x}`, `x` ascending (`kids`);
* a zero field is followed by two fields `p j`: the checker verifies that the permutation
  `perms[p]` maps the current state exactly onto `targets[j]`, whose `NoExt` is a hypothesis.

`node_sound` is the soundness theorem: a successful replay proves `NoExt`. The checker is plain
structural recursion on a fuel argument, so `decide +kernel` evaluates it in the kernel.
-/

open Finset Veles.Bits Veles.Cover

namespace Veles.Checker

/-- The items of the block with point mask `B`, as a state: bit `B xor 2^y` for each `y ∈ B`. -/
def itemsOf (v B : ℕ) : ℕ :=
  (List.range v).foldl
    (fun m y => if (B >>> y) % 2 = 1 then m ||| (1 <<< (B ^^^ (1 <<< y))) else m) 0

/-- The image of the point mask `m` under the permutation `σ` of `range v`. -/
def permMask (σ : List ℕ) (v m : ℕ) : ℕ :=
  (List.range v).foldl (fun a y => if (m >>> y) % 2 = 1 then a ||| (1 <<< σ.getD y 0) else a) 0

/-- `σ` lists a permutation of `range v`. -/
def validPerm (v : ℕ) (σ : List ℕ) : Bool :=
  σ.length == v && σ.all (fun i => decide (i < v)) && decide σ.Nodup

/-- Checker context: parameters and the data that reductions refer to. -/
structure Ctx where
  v : ℕ
  t : ℕ
  itemList : List ℕ
  perms : List (List ℕ)
  targets : List ℕ

/-- The image of the state `X` under `σ`, computed over the item list. -/
def permState (c : Ctx) (σ : List ℕ) (X : ℕ) : ℕ :=
  c.itemList.foldl (fun a m => if (X >>> m) % 2 = 1 then a ||| (1 <<< permMask σ c.v m) else a) 0

/-- Stream of 16-bit fields. -/
structure St where
  words : List ℕ
  cur : ℕ
  left : ℕ

def read (s : St) : Option (ℕ × St) :=
  if s.left = 0 then
    match s.words with
    | [] => none
    | w :: ws => some (w % 65536, ⟨ws, w >>> 16, 255⟩)
  else some (s.cur % 65536, ⟨s.words, s.cur >>> 16, s.left - 1⟩)

/-- Check a reduction: permutation `p` maps `X` onto target `j`. -/
def reduceOk (c : Ctx) (X p j : ℕ) : Bool :=
  validPerm c.v (c.perms.getD p []) && decide (j < c.targets.length) &&
    decide (permState c (c.perms.getD p []) X = c.targets.getD j 0)

mutual
/-- Replay one node on state `X`. -/
def node (c : Ctx) : ℕ → ℕ → St → Option St
  | 0, _, _ => none
  | f + 1, X, s =>
    match read s with
    | none => none
    | some (T, s') =>
      if T = 0 then
        match read s' with
        | none => none
        | some (p, s'') =>
          match read s'' with
          | none => none
          | some (j, s3) => if reduceOk c X p j = true then some s3 else none
      else if T < 2 ^ c.v ∧ popc c.v T = c.t ∧ (X >>> T) % 2 = 0 then kids c f X T 0 s'
      else none
/-- Replay the children `T ∪ {x}`, `x' ≥ x`, of a branch on `T`. -/
def kids (c : Ctx) : ℕ → ℕ → ℕ → ℕ → St → Option St
  | 0, _, _, _, _ => none
  | f + 1, X, T, x, s =>
    if x < c.v then
      if (T >>> x) % 2 = 0 ∧ itemsOf c.v (T ||| (1 <<< x)) &&& X = 0 then
        match node c f (X ||| itemsOf c.v (T ||| (1 <<< x))) s with
        | none => none
        | some s' => kids c f X T (x + 1) s'
      else kids c f X T (x + 1) s
    else some s
end

/-! ## Bit facts -/

theorem bit_iff (m y : ℕ) : (m >>> y) % 2 = 1 ↔ m.testBit y = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]; simp

theorem bit_zero_iff (m y : ℕ) : (m >>> y) % 2 = 0 ↔ m.testBit y = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]; simp

theorem one_shl (n : ℕ) : 1 <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, one_mul]

theorem testBit_foldl_items (B j : ℕ) :
    ∀ (L : List ℕ) (m : ℕ),
      (L.foldl (fun m y => if (B >>> y) % 2 = 1 then m ||| (1 <<< (B ^^^ (1 <<< y))) else m) m).testBit j
        = true ↔ m.testBit j = true ∨ ∃ y ∈ L, B.testBit y = true ∧ j = B ^^^ 2 ^ y
  | [], m => by simp
  | y :: L, m => by
    rw [List.foldl_cons, testBit_foldl_items B j L]
    split_ifs with h
    · rw [Nat.testBit_lor, one_shl, one_shl, Nat.testBit_two_pow]
      rw [bit_iff] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h1 | h2) | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨y, Or.inl rfl, h, h2.symm⟩
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h4.symm)
        · exact Or.inr ⟨z, hz, h3, h4⟩
    · rw [bit_iff] at h
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl h1
        · exact absurd h3 h
        · exact Or.inr ⟨z, hz, h3, h4⟩

theorem mem_dec_itemsOf {v : ℕ} {B T : Finset ℕ} (hB : B ⊆ range v) :
    T ∈ dec (itemsOf v (pm B)) ↔ T ∈ items B := by
  rw [mem_dec, itemsOf, testBit_foldl_items]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range, testBit_pm,
    decide_eq_true_eq]
  constructor
  · rintro ⟨y, -, hy, h⟩
    exact ⟨y, hy, pm_injective (h.trans (pm_erase hy).symm)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, mem_range.1 (hB hy), hy, pm_erase hy⟩

theorem dec_lor_itemsOf {v X : ℕ} {B : Finset ℕ} (hB : B ⊆ range v) :
    dec (X ||| itemsOf v (pm B)) = dec X ∪ items B := by
  rw [dec_lor]; ext T; rw [Set.mem_union, Set.mem_union, mem_dec_itemsOf hB]

theorem compat_iff {v X : ℕ} {B : Finset ℕ} (hB : B ⊆ range v) :
    itemsOf v (pm B) &&& X = 0 ↔ ∀ y ∈ B, B.erase y ∉ dec X := by
  constructor
  · intro h y hy hX
    have h1 : B.erase y ∈ dec (itemsOf v (pm B)) := (mem_dec_itemsOf hB).2 ⟨y, hy, rfl⟩
    have : (itemsOf v (pm B) &&& X).testBit (pm (B.erase y)) = true := by
      rw [Nat.testBit_land]; exact Bool.and_eq_true_iff.2 ⟨h1, hX⟩
    rw [h, Nat.zero_testBit] at this; exact absurd this (by simp)
  · intro h
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_land, Nat.zero_testBit]
    by_contra hne
    have hj : (itemsOf v (pm B)).testBit j = true ∧ X.testBit j = true := by
      simpa using hne
    have hT : ofMask j ∈ dec (itemsOf v (pm B)) := by rw [mem_dec, pm_ofMask]; exact hj.1
    obtain ⟨y, hy, hyT⟩ := (mem_dec_itemsOf hB).1 hT
    exact h y hy (by rw [← hyT, mem_dec, pm_ofMask]; exact hj.2)

/-! ## Permutations -/

theorem testBit_foldl_perm (σ : List ℕ) (m j : ℕ) :
    ∀ (L : List ℕ) (a : ℕ),
      (L.foldl (fun a y => if (m >>> y) % 2 = 1 then a ||| (1 <<< σ.getD y 0) else a) a).testBit j
        = true ↔ a.testBit j = true ∨ ∃ y ∈ L, m.testBit y = true ∧ j = σ.getD y 0
  | [], a => by simp
  | y :: L, a => by
    rw [List.foldl_cons, testBit_foldl_perm σ m j L]
    split_ifs with h
    · rw [Nat.testBit_lor, one_shl, Nat.testBit_two_pow]
      rw [bit_iff] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h1 | h2) | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨y, Or.inl rfl, h, h2.symm⟩
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h4.symm)
        · exact Or.inr ⟨z, hz, h3, h4⟩
    · rw [bit_iff] at h
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl h1
        · exact absurd h3 h
        · exact Or.inr ⟨z, hz, h3, h4⟩

theorem permMask_pm {σ : List ℕ} {v : ℕ} {S : Finset ℕ} (hS : S ⊆ range v) :
    permMask σ v (pm S) = pm (S.image (fun i => σ.getD i 0)) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [testBit_pm]
  apply Bool.eq_iff_iff.2
  rw [permMask, testBit_foldl_perm]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_range, testBit_pm,
    decide_eq_true_eq, mem_image]
  constructor
  · rintro ⟨y, -, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, mem_range.1 (hS hy), hy, rfl⟩

theorem validPerm_spec {v : ℕ} {σ : List ℕ} (h : validPerm v σ = true) :
    Set.InjOn (fun i => σ.getD i 0) (range v) ∧ ∀ i < v, σ.getD i 0 < v := by
  simp only [validPerm, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hall⟩, hnd⟩ := h
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ ha),
      List.getElem?_eq_getElem (hlen ▸ hb), Option.getD_some] at hab
    exact (List.Nodup.getElem_inj_iff hnd).1 hab
  · intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some]
    exact hall _ (List.getElem_mem _)

/-- Hypotheses on the context under which a replay is sound. -/
structure Ctx.Good (c : Ctx) : Prop where
  items_mem : ∀ S ⊆ range c.v, S.card = c.t → pm S ∈ c.itemList
  items_lt : ∀ m ∈ c.itemList, m < 2 ^ c.v
  targets : ∀ j < c.targets.length, NoExt c.v (c.t + 1) (dec (c.targets.getD j 0))

theorem testBit_permState (c : Ctx) (σ : List ℕ) (X j : ℕ) :
    ∀ (L : List ℕ) (a : ℕ),
      (L.foldl (fun a m => if (X >>> m) % 2 = 1 then a ||| (1 <<< permMask σ c.v m) else a) a).testBit j
        = true ↔ a.testBit j = true ∨ ∃ m ∈ L, X.testBit m = true ∧ j = permMask σ c.v m
  | [], a => by simp
  | y :: L, a => by
    rw [List.foldl_cons, testBit_permState c σ X j L]
    split_ifs with h
    · rw [Nat.testBit_lor, one_shl, Nat.testBit_two_pow]
      rw [bit_iff] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h1 | h2) | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨y, Or.inl rfl, h, h2.symm⟩
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h4.symm)
        · exact Or.inr ⟨z, hz, h3, h4⟩
    · rw [bit_iff] at h
      simp only [List.mem_cons]
      constructor
      · rintro (h1 | ⟨z, hz, h3⟩)
        · exact Or.inl h1
        · exact Or.inr ⟨z, Or.inr hz, h3⟩
      · rintro (h1 | ⟨z, rfl | hz, h3, h4⟩)
        · exact Or.inl h1
        · exact absurd h3 h
        · exact Or.inr ⟨z, hz, h3, h4⟩

theorem reduceOk_sound {c : Ctx} (hc : c.Good) {X p j : ℕ} (h : reduceOk c X p j = true) :
    NoExt c.v (c.t + 1) (dec X) := by
  simp only [reduceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hv, hj⟩, heq⟩ := h
  set σ := c.perms.getD p []
  obtain ⟨hinj, hmap⟩ := validPerm_spec hv
  refine noExt_of_map (fun i => σ.getD i 0) hinj hmap ?_ (heq ▸ hc.targets j hj)
  intro T hT hTk
  have hTc : T.card = c.t := by omega
  rw [mem_dec, mem_dec, permState, testBit_permState]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · intro hX
    exact ⟨pm T, hc.items_mem T hT hTc, hX, (permMask_pm hT).symm⟩
  · rintro ⟨m, hm, hXm, hpm⟩
    have hmv := hc.items_lt m hm
    have hS := ofMask_subset_range hmv
    rw [← pm_ofMask m, permMask_pm hS] at hpm
    have himg := pm_injective hpm
    have : T = ofMask m := by
      ext z
      constructor
      · intro hz
        have : σ.getD z 0 ∈ (ofMask m).image (fun i => σ.getD i 0) := himg ▸ mem_image_of_mem _ hz
        obtain ⟨w, hw, hwz⟩ := mem_image.1 this
        have := hinj (mem_coe.2 (hS hw)) (mem_coe.2 (hT hz)) hwz
        exact this ▸ hw
      · intro hz
        have : σ.getD z 0 ∈ T.image (fun i => σ.getD i 0) := himg.symm ▸ mem_image_of_mem _ hz
        obtain ⟨w, hw, hwz⟩ := mem_image.1 this
        have := hinj (mem_coe.2 (hT hw)) (mem_coe.2 (hS hz)) hwz
        exact this ▸ hw
    rw [this, pm_ofMask]; exact hXm

/-! ## Soundness -/

theorem sound (c : Ctx) (hc : c.Good) : ∀ f : ℕ,
    (∀ X s s', node c f X s = some s' → NoExt c.v (c.t + 1) (dec X)) ∧
    (∀ X T x s s', kids c f X T x s = some s' →
      ∀ x', x ≤ x' → x' < c.v → (T >>> x') % 2 = 0 → itemsOf c.v (T ||| (1 <<< x')) &&& X = 0 →
        NoExt c.v (c.t + 1) (dec (X ||| itemsOf c.v (T ||| (1 <<< x'))))) := by
  intro f
  induction f with
  | zero => exact ⟨fun _ _ _ h => by simp [node] at h, fun _ _ _ _ _ h => by simp [kids] at h⟩
  | succ f ih =>
    obtain ⟨ihn, ihk⟩ := ih
    refine ⟨?_, ?_⟩
    · intro X s s' h
      rw [node] at h
      rcases hr : read s with _ | ⟨T, s1⟩
      · rw [hr] at h; simp at h
      rw [hr] at h
      simp only at h
      split_ifs at h with hT0 hTok
      · rcases hr2 : read s1 with _ | ⟨p, s2⟩
        · rw [hr2] at h; simp at h
        rw [hr2] at h; simp only at h
        rcases hr3 : read s2 with _ | ⟨j, s3⟩
        · rw [hr3] at h; simp at h
        rw [hr3] at h; simp only at h
        split_ifs at h with hok
        exact reduceOk_sound hc hok
      · obtain ⟨hTv, hTc, hTX⟩ := hTok
        have hsub := ofMask_subset_range hTv
        have hcard : (ofMask T).card = c.t := (popc_eq_card c.v T hTv).symm.trans hTc
        refine noExt_branch hsub (by omega) ?_ ?_
        · rw [mem_dec, pm_ofMask]; rw [bit_zero_iff] at hTX; simp [hTX]
        · intro x hx hxT hcompat
          have hxb : (T >>> x) % 2 = 0 := by
            rw [bit_zero_iff, ← pm_ofMask T, testBit_pm]; simpa using hxT
          have hB : insert x (ofMask T) ⊆ range c.v := insert_subset (mem_range.2 hx) hsub
          have hBm : T ||| (1 <<< x) = pm (insert x (ofMask T)) := by
            rw [pm_insert, pm_ofMask, one_shl]
          have hc' : itemsOf c.v (T ||| (1 <<< x)) &&& X = 0 := by
            rw [hBm, compat_iff hB]; exact hcompat
          have := ihk X T 0 s1 s' h x (Nat.zero_le _) hx hxb hc'
          rwa [hBm, dec_lor_itemsOf hB] at this
    · intro X T x s s' h x' hxx' hx'v hbit hcomp
      rw [kids] at h
      split_ifs at h with hxv hcond
      · rcases hn : node c f (X ||| itemsOf c.v (T ||| (1 <<< x))) s with _ | s1
        · rw [hn] at h; simp at h
        rw [hn] at h; simp only at h
        rcases Nat.eq_or_lt_of_le hxx' with rfl | hlt
        · exact ihn _ _ _ hn
        · exact ihk X T (x + 1) s1 s' h x' hlt hx'v hbit hcomp
      · rcases Nat.eq_or_lt_of_le hxx' with rfl | hlt
        · exact absurd ⟨hbit, hcomp⟩ hcond
        · exact ihk X T (x + 1) s s' h x' hlt hx'v hbit hcomp
      · omega

/-- A successful replay from state `X` proves that `X` has no extension. -/
theorem node_sound {c : Ctx} (hc : c.Good) {f X : ℕ} {s s' : St}
    (h : node c f X s = some s') : NoExt c.v (c.t + 1) (dec X) :=
  (sound c hc f).1 X s s' h

end Veles.Checker
