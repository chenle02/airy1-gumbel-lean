/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Airy1GumbelContrib.Fdd.FddOp

/-!
# Time-shift invariance of the fdd determinant

Shift invariance `F_{I+c} = F_I`.  The candidate CDF `airy1FinCdf I x`
sees the time set only through the sorted list of times, and from that list only through the
consecutive gaps (padding `1` after the last time) and the level attached to each time.
Translating every time by `c` translates the sorted list (`sort_map_addRight`), leaves every
gap unchanged (`(s + c) − (t + c) = s − t`, `fddEntries_map_add`), and — once the levels are
relabelled along the translation — leaves the `(level, gap)` entry list, hence the determinant,
unchanged.

* `airy1FinCdf_eq_of_sort_eq_map_add`: the core statement for any `J` whose sorted list is the
  translate of `I`'s, with levels matched along `t ↦ t + c`.
* `airy1FinCdf_shift_of_eq` (`J = I.map (addRightEmbedding c)`) and
  `airy1FinCdf_shift_image_of_eq` (`J = I.image (· + c)`): consumer forms with an arbitrary
  level vector `y` on the shifted set agreeing with `x` along the translation.
* `airy1FinCdf_shift`: the explicit relabelling `y s = x (s − c)`.

No probabilistic content: stationarity of the process law is derived from this in the main
package (finite-dimensional marginals of the shifted law agree, then uniqueness of the
projective limit).
-/

namespace AiryFdd

/-- The determinant attached to an entry list depends only on the list (the positivity and
padding certificates are propositions). -/
theorem cdfOfEntries_congr {L L' : List (ℝ × ℝ)} (h : L = L') (hp : ∀ y ∈ L, 0 < y.2)
    (hl : ∀ e L₀, L = e :: L₀ → lastGap e L₀ = 1) (hp' : ∀ y ∈ L', 0 < y.2)
    (hl' : ∀ e L₀, L' = e :: L₀ → lastGap e L₀ = 1) :
    cdfOfEntries L hp hl = cdfOfEntries L' hp' hl' := by
  subst h; rfl

/-- Translating a time list by `c` leaves its `(level, gap)` entries unchanged once the levels
are relabelled along the translation. -/
theorem fddEntries_map_add (lev lev' : ℝ → ℝ) (c : ℝ) :
    ∀ ts : List ℝ, (∀ t ∈ ts, lev' (t + c) = lev t) →
      fddEntries lev' (ts.map (· + c)) = fddEntries lev ts
  | [], _ => rfl
  | [t], h => by simp [fddEntries, h t List.mem_cons_self]
  | t :: s :: L, h => by
    have ih := fddEntries_map_add lev lev' c (s :: L)
      (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons, fddEntries] at ih ⊢
    rw [ih, h t List.mem_cons_self, add_sub_add_right_eq_sub]

/-- Sorting commutes with translation. -/
theorem sort_map_addRight (I : Finset ℝ) (c : ℝ) :
    (I.map (addRightEmbedding c)).sort (· ≤ ·) = (I.sort (· ≤ ·)).map (· + c) := by
  rw [← Finset.map_sort (f := addRightEmbedding c) (s := I) (r := (· ≤ ·)) (r' := (· ≤ ·))
    (fun a _ b _ => by simp)]
  rfl

/-- Sorting commutes with translation (`Finset.image` form). -/
theorem sort_image_add (I : Finset ℝ) (c : ℝ) :
    (I.image (· + c)).sort (· ≤ ·) = (I.sort (· ≤ ·)).map (· + c) := by
  rw [← sort_map_addRight, Finset.map_eq_image]
  rfl

/-- **Core shift invariance.** If the sorted times of `J` are those of `I` translated by `c`,
and the levels agree along `t ↦ t + c`, then `F_J(y) = F_I(x)`. -/
theorem airy1FinCdf_eq_of_sort_eq_map_add {I J : Finset ℝ} (c : ℝ) (x : I → ℝ) (y : J → ℝ)
    (hJ : J.sort (· ≤ ·) = (I.sort (· ≤ ·)).map (· + c))
    (hxy : ∀ t (ht : t ∈ I) (ht' : t + c ∈ J), y ⟨t + c, ht'⟩ = x ⟨t, ht⟩) :
    airy1FinCdf J y = airy1FinCdf I x := by
  unfold airy1FinCdf
  refine cdfOfEntries_congr ?_ _ _ _ _
  unfold finEntries
  rw [hJ]
  refine fddEntries_map_add _ _ c _ fun t ht => ?_
  have hI : t ∈ I := (Finset.mem_sort _).1 ht
  have hJt : t + c ∈ J := by
    rw [← Finset.mem_sort (· ≤ ·), hJ]
    exact List.mem_map_of_mem ht
  simp only [levelFn, hJt, hI, ↓reduceDIte, hxy t hI hJt]

/-- **Shift invariance** (`Finset.map` form): `F_{I+c}(y) = F_I(x)` whenever the level
vector `y` on the translated time set agrees with `x` along `t ↦ t + c`. -/
theorem airy1FinCdf_shift_of_eq (I : Finset ℝ) (c : ℝ) (x : I → ℝ)
    (y : I.map (addRightEmbedding c) → ℝ)
    (hxy : ∀ t (ht : t ∈ I), y ⟨t + c, Finset.mem_map_of_mem _ ht⟩ = x ⟨t, ht⟩) :
    airy1FinCdf (I.map (addRightEmbedding c)) y = airy1FinCdf I x :=
  airy1FinCdf_eq_of_sort_eq_map_add c x y (sort_map_addRight I c) fun t ht _ => hxy t ht

/-- **Shift invariance** (`Finset.image` form). -/
theorem airy1FinCdf_shift_image_of_eq (I : Finset ℝ) (c : ℝ) (x : I → ℝ)
    (y : I.image (· + c) → ℝ)
    (hxy : ∀ t (ht : t ∈ I), y ⟨t + c, Finset.mem_image_of_mem _ ht⟩ = x ⟨t, ht⟩) :
    airy1FinCdf (I.image (· + c)) y = airy1FinCdf I x :=
  airy1FinCdf_eq_of_sort_eq_map_add c x y (sort_image_add I c) fun t ht _ => hxy t ht

/-- A point of the translated time set, shifted back, lies in the original time set. -/
theorem sub_mem_of_mem_map_addRight {I : Finset ℝ} {c s : ℝ}
    (hs : s ∈ I.map (addRightEmbedding c)) : s - c ∈ I := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hs
  simpa using ha

/-- **Shift invariance** with the explicit relabelling `y s = x (s − c)`:
`F_{I+c}(x(· − c)) = F_I(x)`. -/
theorem airy1FinCdf_shift (I : Finset ℝ) (c : ℝ) (x : I → ℝ) :
    airy1FinCdf (I.map (addRightEmbedding c))
        (fun s => x ⟨s.1 - c, sub_mem_of_mem_map_addRight s.2⟩) = airy1FinCdf I x :=
  airy1FinCdf_shift_of_eq I c x _ fun t _ => congrArg x (Subtype.ext (add_sub_cancel_right t c))

end AiryFdd
