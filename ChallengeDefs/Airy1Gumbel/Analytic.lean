/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Sort

/-!
# Statement vocabulary, part 1: the Airy₁ finite-dimensional distribution functions

This module is part of the trusted statement of the comparator check (`Challenge.lean`). It
imports Mathlib only, contains no proof of anything, and defines, in Mathlib's vocabulary, the
function `airy1FinCdf I x` that the paper's Airy₁ finite-dimensional distribution functions are
read as: for a finite time set `I` and levels `x`, the Fredholm determinant
`det(I − J̃)_{L²(ℝ)}` of the path-integral operator of Quastel and Remenik (PTRF 2013, Theorem 1,
read through their trace-class conjugate `J̃`).

The objects, in order:

* the heat kernel `p_T(v) = (4πT)^{-1/2} e^{-v²/(4T)}`;
* the Airy function `Ai` (DLMF 9.4.1, through Mathlib's regularized hypergeometric function
  `₀F̃₁`), its restriction to `ℝ`, and the backward Airy kernel
  `g_T(s) = e^{-(2/3)T³ - Ts} Ai(s + T²)`;
* the kernels of the path integral: `Λ e^{τΔ}` for a list of `(level, gap)` entries, the hitting
  kernel `H = p_S − Λ e^{τΔ}`, and the weighted factors `V` and `W` at the conjugation weight
  `a = 2S`, where `S` is the total time;
* `kernelOp K`: the bounded operator on `L²(ℝ)` whose action is integration against the kernel
  `K`, characterized by that property (`Classical.epsilon`; for a square-integrable kernel it is
  the unique such operator);
* the entire Fredholm determinant `det(1 − zA) = ∑_{s finite} (−z)^{|s|} det A[s, s]`, the
  principal-minor series in a Hilbert basis (Simon, *Trace Ideals*, Theorem 3.10);
* `airy1FinCdf I x`: sort `I`, take consecutive time gaps with padding `1` after the last time,
  and evaluate `det(1 − V W)` at `z = 1`; the empty time set gives `1`.

Every definition here restates, with the same formula, the definition of the same name in the
companion package; the only change is that `kernelOp` replaces an operator built from a proof of
square integrability by the operator characterized by its action, so that no proof enters the
statement.
-/

noncomputable section

namespace Airy1GumbelSpec

open MeasureTheory Set

/-! ## Heat kernel and Airy function -/

/-- The heat kernel `p_T(v) = (4πT)^{-1/2} e^{-v²/(4T)}`. -/
def heatKernel (T v : ℝ) : ℝ :=
  (4 * Real.pi * T)^(-1/2 : ℝ) * Real.exp (-v^2 / (4 * T))

local notation "F̃₀₁(" b ")" => Complex.regularizedHGFun 0 {(b : ℂ)}

/-- The Airy function of the first kind (DLMF 9.4.1 with `ζ = z³/9`):
`Ai(z) = 3^{-2/3} ₀F̃₁(; 2/3; z³/9) − 3^{-4/3} z ₀F̃₁(; 4/3; z³/9)`. -/
def airyAi (z : ℂ) : ℂ :=
  (3 : ℂ) ^ (-2 / 3 : ℂ) * F̃₀₁(2 / 3) (z ^ 3 / 9) -
    (3 : ℂ) ^ (-4 / 3 : ℂ) * z * F̃₀₁(4 / 3) (z ^ 3 / 9)

/-- The Airy function on the real line. -/
def airyAiReal (x : ℝ) : ℝ := (airyAi (x : ℂ)).re

/-- The backward Airy kernel `g_T(s) = e^{-(2/3)T³ - Ts} Ai(s + T²)`. -/
def backwardAiry (T s : ℝ) : ℝ :=
  Real.exp (-(2/3)*T^3 - T*s) * airyAiReal (s + T^2)

/-! ## Kernels of the path integral -/

/-- The weight `φ(x) = (1 + x²)^{1/2}`. -/
def phiWeight (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

/-- The weighted kernel `W_{T,a}(z, y) = φ(z)^{-1} e^{az} g_T(z + y) e^{ay}`. -/
def wKernel (T a : ℝ) (zy : ℝ × ℝ) : ℝ :=
  (phiWeight zy.1)⁻¹ * Real.exp (a * zy.1) * backwardAiry T (zy.1 + zy.2) *
    Real.exp (a * zy.2)

/-- The composite kernel `(K ⋆ K')(x, y) = ∫ K(x, z) K'(z, y) dz`. -/
def compKernel (K K' : ℝ × ℝ → ℝ) (xy : ℝ × ℝ) : ℝ :=
  ∫ z : ℝ, K (xy.1, z) * K' (z, xy.2)

/-- The heat kernel as a kernel on `ℝ × ℝ`: `(u, v) ↦ p_t(u − v)`. -/
def heatKerTwo (t : ℝ) : ℝ × ℝ → ℝ := fun p => heatKernel t (p.1 - p.2)

/-- The one-level kernel of `Λ e^{τΔ}`: `1_{u ≤ x} p_τ(u − v)`. -/
def lamKer1 (x τ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Iic x).indicator (fun _ => (1 : ℝ)) p.1 * heatKernel τ (p.1 - p.2)

/-- The total time `S` of a nonempty list of `(level, gap)` entries: the sum of the gaps. -/
def gapSum : ℝ × ℝ → List (ℝ × ℝ) → ℝ
  | e, [] => e.2
  | e, y :: L => e.2 + gapSum y L

/-- The kernel of `Λ e^{τΔ}` for a list of `(level, gap)` entries, by recursion on the list:
`1_{u ≤ x₁} (p_{t₁} ⋆ K_{rest})(u, v)`. -/
def lamKerN : ℝ × ℝ → List (ℝ × ℝ) → ℝ × ℝ → ℝ
  | e, [] => lamKer1 e.1 e.2
  | e, y :: L => fun p => (Iic e.1).indicator (fun _ => (1 : ℝ)) p.1
      * compKernel (heatKerTwo e.2) (lamKerN y L) p

/-- The hitting kernel `H = p_S − Λ e^{τΔ}` of a list of entries. -/
def hitKerN (e : ℝ × ℝ) (L : List (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ :=
  heatKernel (gapSum e L) (p.1 - p.2) - lamKerN e L p

/-- The weighted kernel `V(u, v) = e^{-au} H(u, v) e^{-av} φ(v)`. -/
def fddVKer (H : ℝ × ℝ → ℝ) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-a * p.1) * H p * Real.exp (-a * p.2) * phiWeight p.2

/-! ## Integral operators and the Fredholm determinant -/

/-- The bounded operator on `L²(ℝ)` given by integration against the kernel `K`:
`(T f)(x) = ∫ K(x, y) f(y) dy` for almost every `x`, for every `f`. For a square-integrable `K`
there is exactly one such operator. -/
def kernelOp (K : ℝ × ℝ → ℝ) : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  Classical.epsilon fun T : Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) =>
    ∀ f : Lp ℝ 2 (volume : Measure ℝ), (T f : ℝ → ℝ) =ᵐ[volume] fun x => ∫ y, K (x, y) * f y

/-- The `n`-time operator `J̃ = V W` for a nonempty list of `(level, gap)` entries, at the
conjugation weight `a = 2S` (`S` the total time). -/
def fddOp (e : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] Lp ℝ 2 (volume : Measure ℝ) :=
  kernelOp (fddVKer (hitKerN e L) (2 * gapSum e L)) ∘L
    kernelOp (wKernel (gapSum e L) (2 * gapSum e L))

section FredholmDeterminant

open scoped Classical InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The index type of a Hilbert basis of `E` chosen once and for all. -/
def canonicalIndex (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :=
  Classical.choose (exists_hilbertBasis (𝕜 := 𝕜) (E := E))

/-- A Hilbert basis of `E` chosen once and for all. -/
def canonicalBasis (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : HilbertBasis (canonicalIndex 𝕜 E) 𝕜 E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := 𝕜) (E := E)))

/-- The principal minor `det [⟪b i, A (b j)⟫]_{i, j ∈ s}` of `A` in the basis `b`. -/
def detMinor {ι : Type*} (b : HilbertBasis ι 𝕜 E) (A : E →L[𝕜] E) (s : Finset ι) : 𝕜 :=
  Matrix.det (Matrix.of fun i j : s => ⟪b i, A (b j)⟫_𝕜)

/-- The entire Fredholm determinant `det(1 − zA)` in the basis `b`, as the principal-minor series
`∑_s (−z)^{|s|} det A[s, s]`. -/
def fredholmDetIn {ι : Type*} (b : HilbertBasis ι 𝕜 E) (A : E →L[𝕜] E) (z : 𝕜) : 𝕜 :=
  ∑' s : Finset ι, (-z) ^ s.card * detMinor b A s

/-- The entire Fredholm determinant `det(1 − zA)` in the chosen Hilbert basis. For a trace-class
`A` the series converges absolutely and does not depend on the basis. -/
def fredholmDet (A : E →L[𝕜] E) (z : 𝕜) : 𝕜 :=
  fredholmDetIn (canonicalBasis 𝕜 E) A z

end FredholmDeterminant

/-! ## The finite-dimensional distribution functions -/

/-- `(level, gap)` entries of an increasing list of times: consecutive differences, and the
padding `1` after the last time. -/
def fddEntries (lev : ℝ → ℝ) : List ℝ → List (ℝ × ℝ)
  | [] => []
  | [t] => [(lev t, 1)]
  | t :: s :: L => (lev t, s - t) :: fddEntries lev (s :: L)

/-- The level at time `t` (the `else` branch is never used for `t ∈ I`). -/
def levelFn (I : Finset ℝ) (x : I → ℝ) (t : ℝ) : ℝ :=
  if h : t ∈ I then x ⟨t, h⟩ else 0

/-- The `(level, gap)` entries of a finite time set, sorted increasingly. -/
def finEntries (I : Finset ℝ) (x : I → ℝ) : List (ℝ × ℝ) :=
  fddEntries (levelFn I x) (I.sort (· ≤ ·))

/-- **The Airy₁ finite-dimensional distribution function** `F_I(x) = det(I − J̃)` (Quastel and
Remenik, PTRF 2013, Theorem 1, path-integral form): for the sorted times of `I` with levels `x`,
the entire Fredholm determinant of `J̃ = V W` at `z = 1`; `F_∅ = 1`. -/
def airy1FinCdf (I : Finset ℝ) (x : I → ℝ) : ℝ :=
  match finEntries I x with
  | [] => 1
  | e :: L => fredholmDet (fddOp e L) 1

end Airy1GumbelSpec
