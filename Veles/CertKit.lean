/-
Copyright (c) 2026 Millennium Research.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Veles.Checker

/-!
# Glue for generated certificates

`stateOf v bs` is the state covered by the blocks with point masks `bs`; `itemsList v t` lists the
point masks of the `t`-subsets of `range v`; `noExt_of_replay` turns a kernel-checked replay into
`NoExt`, given `NoExt` for every reduction target.
-/

open Finset Veles.Bits Veles.Cover Veles.Checker

namespace Veles.CertKit

/-- The state covered by a list of blocks (point masks). -/
def stateOf (v : ℕ) (bs : List ℕ) : ℕ := bs.foldl (fun a B => a ||| itemsOf v B) 0

/-- The point masks of the `t`-subsets of `range v`. -/
def itemsList (v t : ℕ) : List ℕ := (List.range (2 ^ v)).filter (fun m => popc v m == t)

/-- What the soundness proof needs of an item list. -/
structure ItemsGood (v t : ℕ) (il : List ℕ) : Prop where
  mem : ∀ S ⊆ range v, S.card = t → pm S ∈ il
  lt : ∀ m ∈ il, m < 2 ^ v

theorem itemsList_good (v t : ℕ) : ItemsGood v t (itemsList v t) where
  mem S hS hc := by
    have hlt := pm_lt hS
    simp only [itemsList, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨hlt, by rw [popc_eq_card v _ hlt, ofMask_pm, hc]⟩
  lt m hm := by
    simp only [itemsList, List.mem_filter, List.mem_range] at hm; exact hm.1

theorem itemsGood_of_eq {v t : ℕ} {il : List ℕ} (h : il = itemsList v t) : ItemsGood v t il :=
  h ▸ itemsList_good v t

/-- Every target has no extension. -/
def AllNo (v k : ℕ) : List ℕ → Prop
  | [] => True
  | Y :: l => NoExt v k (dec Y) ∧ AllNo v k l

theorem allNo_getD {v k : ℕ} : ∀ {ts : List ℕ}, AllNo v k ts →
    ∀ j < ts.length, NoExt v k (dec (ts.getD j 0))
  | [], _, j, hj => absurd hj (by simp)
  | Y :: l, ⟨hY, hl⟩, j, hj => by
    rcases j with _ | j
    · simpa using hY
    · simpa using allNo_getD hl j (by simpa using hj)

theorem noExt_of_replay {v t : ℕ} {il : List ℕ} (hil : ItemsGood v t il) {ps : List (List ℕ)}
    {ts : List ℕ} (hts : AllNo v (t + 1) ts) {f X : ℕ} {s : St}
    (h : (node ⟨v, t, il, ps, ts⟩ f X s).isSome = true) : NoExt v (t + 1) (dec X) := by
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 h
  exact node_sound (c := ⟨v, t, il, ps, ts⟩) ⟨hil.mem, hil.lt, allNo_getD hts⟩ hs'

theorem dec_zero : dec 0 = ∅ := by ext T; simp [dec]

theorem stateOf_nil (v : ℕ) : stateOf v [] = 0 := rfl

end Veles.CertKit
