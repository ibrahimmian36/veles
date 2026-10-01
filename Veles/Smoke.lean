import Veles.Upstream

/-!
# Smoke test

`J(4, 2)` has chromatic number 3 (the case k = 2 of Erdős Problem 835, where the
answer is yes), and the sets `T ∪ {x}`, `x ∉ T`, are pairwise adjacent in `J(n, k)`
when `#T + 1 = k`.
-/

open Finset SimpleGraph

namespace Veles.Smoke

instance instDecidableAdjJohnson {n k : ℕ} : DecidableRel J(n, k).Adj :=
  fun s t => decidable_of_iff (#(s.val ∩ t.val) + 1 = k) (by rw [johnson_adj])

/-- For `#T + 1 = k` and distinct `x, y ∉ T`, the sets `T ∪ {x}` and `T ∪ {y}` meet in `T`,
so they are adjacent in `J(n, k)`. -/
theorem johnson_adj_insert {n k : ℕ} {T : Finset (Fin n)} (hT : #T + 1 = k) {x y : Fin n}
    (hx : x ∉ T) (hy : y ∉ T) (hxy : x ≠ y)
    (hsx : #(insert x T) = k) (hsy : #(insert y T) = k) :
    J(n, k).Adj ⟨insert x T, hsx⟩ ⟨insert y T, hsy⟩ := by
  simp only [johnson_adj]
  have : insert x T ∩ insert y T = T := by
    ext z; simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | h, rfl | h'⟩ <;> first | exact absurd rfl hxy | assumption
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
  rw [this, hT]

/-- The colour of a pair: the index of the perfect matching of `Fin 4` containing it. -/
def c3 (s : {s : Finset (Fin 4) // #s = 2}) : Fin 3 :=
  if s.val = {0, 1} ∨ s.val = {2, 3} then 0 else if s.val = {0, 2} ∨ s.val = {1, 3} then 1 else 2

theorem c3_proper : ∀ v w, J(4, 2).Adj v w → c3 v ≠ c3 w := by decide

/-- A proper 3-colouring of `J(4, 2)`. -/
def col3 : J(4, 2).Coloring (Fin 3) := Coloring.mk c3 (fun h => c3_proper _ _ h)

/-- `χ(J(4, 2)) = 3`. -/
theorem chromaticNumber_J42 : J(4, 2).chromaticNumber = 3 := by
  apply le_antisymm (col3.colorable.chromaticNumber_le)
  let f : Fin 3 → {s : Finset (Fin 4) // #s = 2} :=
    ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{1, 2}, by decide⟩]
  exact le_chromaticNumber_of_pairwise_adj (by simp) f (by unfold Pairwise; decide)

end Veles.Smoke
