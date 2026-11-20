/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
/-

# Airy1GumbelContrib: general-purpose library for the Airy₁–Gumbel formalization

General-purpose results (special functions, operator theory, Fredholm determinants, the
Airy₁ finite-dimensional distributions) used by the `Airy1Gumbel` package, written with a
view to upstreaming to mathlib. Authored by Le Chen.

- `Gumbel/`: `Airy1GumbelContrib/Gumbel/Gumbel.lean` — standard Gumbel distribution.
- `Airy/`: `Airy1GumbelContrib/Airy/Airy.lean`, `AiryODE.lean`, `AiryReal.lean` —
  Airy Ai/Bi as entire functions, ODE `y'' = xy` (complex and real), DLMF values and
  signs at 0. `BesselK13.lean` — the Schläfli integral for `K_{1/3}`, its positivity,
  and the Laplace-localization bound `K_{1/3}(z) ≤ C z^{-1/2} e^{-z}` (the K-side of the
  Airy upper bound). `AiryBessel.lean` — the s-substitution
  J-decomposition `K_{1/3}(z) = ((2/z)^{1/3} J₁(z) + (2/z)^{-1/3} J₂(z))/2` with
  continuity/integrability of the J-kernels, the Bessel equation, the change of
  variables `y'' = xy` for `y(x) = √(x/3) K((2/3) x^{3/2})`, and the Γ-reflection
  matching constants. `AiryAsymptotics.lean` — the small-`z` asymptotics of the
  J-pieces (`schlaefliJ2_const`, `schlaefliJ2_sub_tendsto`, `schlaefliJ1_isBigO`).
  `AiryUniqueness.lean` — the abstract half-line uniqueness lemma
  `airy_ode_uniqueness` for the Airy ODE `W'' = xW` (Grönwall on the pair
  `(W, W')`). `AiryIdentity.lean` — the matching limits at `x = 0`
  (`airyBesselY_tendsto_zero_right`, `airyBesselY_slope_tendsto`) and the
  **DLMF 9.6.1 identity** `airyBesselY x = π · airyAiReal x` for `0 < x`
  (`airyBesselY_eq_pi_airyAiReal`, `airyAiReal_eq_airyBesselY_div_pi`).
  `AiryLaplace.lean` — the positive half of the paper's Airy–Laplace bound:
  `∫₀^∞ e^{2βu} Ai(u)² du ≤ C e^{(2/3) β³}` for `1 ≤ β` (`airyAiReal_laplace_half`),
  via `u = v²`, the squared bound `Ai(v²)² ≤ C₂ (1+v²)^{-1/2} e^{-(4/3) v³}`, and the
  exact factorization `2βv² - (4/3)v³ = (2/3)β³ - (2/3)(v-β)²(β+2v)`.
  `AiryLaplaceFull.lean` — `|Ai|` bounded on `ℝ₋` by energy monotonicity
  (`airyAiReal_abs_le_nonpos`) and the **full Airy–Laplace bound**
  `∫_ℝ e^{2βu} Ai(u)² du ≤ C e^{(2/3) β³}` for `1 ≤ β` (`airyAiReal_laplace`).
  `AiryLeading.lean` — the exact leading asymptotics at `+∞` (the Laplace method on the
  Schläfli integral): `schlaefliK13_isEquivalent`, `airyAiReal_isEquivalent`,
  `deriv_airyAiReal_isEquivalent`, and the tail integral
  `integral_airyAiReal_isEquivalent` — this is where `κ = 4√2/3` and `C* = 2^{1/4}/√π`
  are *derived*.
  `AiryContour.lean` — the contour form of `Ai` (DLMF 9.5.4): for every `c > 0`,
  `Ai(z) = (1/2π) ∫_ℝ exp((c+is)³/3 − z(c+is)) ds` on all of `ℂ`
  (`airyContour_eq_airyAi`; real form `airyAiReal_eq_integral`), via the Airy equation for
  the integral, initial data from Γ-integrals on the ray `arg t = π/3`, and Taylor-series
  uniqueness; this is step A1 of the Airy-transform construction (steps A1–A6 below).
  `AiryFourier.lean` — the Fourier transform of `Ai` as a tempered distribution: with
  Mathlib's `𝓕`, `𝓕 Ai = exp(i(2π·)³/3)` in `𝓢'(ℝ, ℂ)` (`fourier_airyAiDist`; weak forms
  `integral_airyAi_mul_fourier`, `integral_airyAi_mul_fourier_schwartz`), via Gaussian
  regularisation and the contour form on the moving line `Re t = δ²`; step A2.
  `AiryTransform.lean` — the Airy transform `B₀ f(x) = ∫ Ai(x+y) f(y) dy` on `𝓢(ℝ, ℂ)` as the
  CLM `𝓕⁻(ψ · 𝓕(f(−·)))` (`airyTransformCLM`, kernel form `airyTransformCLM_apply`) and its
  `L²` isometry on `𝓢` (`integral_norm_sq_airyTransformCLM`); step A3 and the Schwartz half of
  A4 (no `L²` extension here).
  `AiryTransformL2.lean` — the Airy transform as an `L²` contraction on `L¹ ∩ L²`:
  `‖∫ Ai(· + y) k(y) dy‖₂ ≤ ‖k‖₂` (`eLpNorm_airyTransformFun_le`; real form
  `eLpNorm_integral_airyAiReal_mul_le`), via Fatou from the Schwartz isometry (no `L²`
  extension of `B₀` built); the Airy-only part of step A5.
- `Gaussian/`: `Airy1GumbelContrib/Gaussian/MillsRatio.lean` — Gaussian tail / Mills-ratio
  asymptotics (exact two-term identity, `=O` expansion, asymptotic equivalence).
- `HilbertSchmidt/`: `Airy1GumbelContrib/HilbertSchmidt/HilbertSchmidt.lean`, `KernelHS.lean` —
  Hilbert–Schmidt enorm (basis-independent), L² kernels ⇒ HS with norm equality.
- `TraceClass/`: `Airy1GumbelContrib/TraceClass/TraceClass.lean` — trace-class operators via
  Hilbert–Schmidt factorization: two-sided-ideal closure, HS ⇒ compact, trace with
  basis independence and cyclicity. `Airy1GumbelContrib/TraceClass/FredholmTwo.lean` —
  the 2-regularized Fredholm determinant
  `det₂(1 + zK) = exp(∑_{m≥2} (−1)^{m+1} z^m tr(K^m)/m)` for Hilbert–Schmidt `K`:
  trace-class powers `K^m` (m ≥ 2), the trace bound `‖tr(K^m)‖ ≤ ‖K‖₂^m`, absolute
  convergence on the disk `‖z‖·‖K‖₂ < 1`, radius ≥ `‖K‖₂⁻¹`, `det₂ K 0 = 1`,
  derivative `0` at `0`, differentiability on the disk. The entire extension
  of `det₂` is not built here (see the module's scope note; the entire `det₁` is in
  `FredholmDet/`).
  `Airy1GumbelContrib/TraceClass/FredholmOne.lean` — the 1-regularized Fredholm
  determinant `det₁(1 − zA)` for trace-class `A` on the Plemelj disk: trace
  linearity, `det₁(I−A) = e^{−Tr A} det₂(1−A)`, Simon cyclicity
  `det₁(1 − zAB) = det₁(1 − zBA)`, the remainder
  `1 − det₁(1−A) = tr A + O(‖A‖₂² e^{‖A‖₂})`, and the det₂-tail HS-Lipschitz bound
  (telescoping; the m = 1 obstruction is documented in the module's scope note).
- `AiryKernel/`: `Airy1GumbelContrib/AiryKernel/AiryKernel.lean` — the Airy–Hankel operator
  `airyHankel s` on `L²(ℝ₊)`, the Airy operator `airyKernelOp s = A(s) A(s)†` (trace
  class, Hilbert–Schmidt norm → 0 as `s → ∞`), the global bound `|Ai u| ≤ C e^{−u}`,
  and the diagonal energy identity `airyAiReal_sq_integral`.
  `Airy1GumbelContrib/AiryKernel/BackwardAiry.lean` — the backward Airy kernel
  `backwardAiry T s = e^{−(2/3)T³ − Ts} Ai(s + T²)` (the paper's `g_T`), the
  backward heat equation, and the four heat–Airy convolution identities:
  `heat_airy_conv`, `heat_airy_conv_moment`, `heat_airy_conv_tail`,
  `heat_airy_conv_backward`.
  `Airy1GumbelContrib/AiryKernel/GaussianSaddle.lean` — the Gaussian/saddle calculus
  library: Gaussian tail bounds, `heatKernel_conv_cdf` (the paper's heat–CDF convolution
  identity), `heatKernel_semigroup`, and the saddle analysis `saddleF_ge`
  (`F(δ) ≥ J_M(r) + (δ−δ*)²/2`).
  `Airy1GumbelContrib/AiryKernel/ConjugateUPhi.lean` — the paper's `U_a Φ` bound:
  `‖U_a Q_{M,T} P_L U_a Φ‖₂ ≤ C_T (1+M+L)^K e^{La²+Ta²−a³}`
  (`uphi_hs_le`), via the factorization `(U_a Q U_a Φ) ∘ ℬ_{L,a}`, the ratio bound
  `φ(w)/φ(z) ≤ 1+|z−w|`, and the Young `L²` convolution bound with
  `k(v) = (1+|v|)e^{av}p_L(v)` (the final Schur bound, `integral_kUPhi_le`).
  `Airy1GumbelContrib/AiryKernel/TraceExpansion.lean` — the trace expansion core of
  the paper's sharp one-block tail: the conjugated operator
  `Ã_{M,T} = V_{T,a} W_{T,a}` (trace class, HS product bound), the trace formula
  `Tr Ã = ∫∫ Q_{M,T}(x,z) g_T(z+x)`, the scalar split, the exact heat-form identity
  `Tr Ã = −2T·Ai'(2M) + ∫_{2M}^∞ Ai + ℰ_{M,T}`, and the
  `O_T` remainder bound `|ℰ_{M,T}| ≤ C_T M^{−3/4} e^{−2TM − (2/3)(2M)^{3/2}}`
  (`errorMT_abs_le`).
  `Airy1GumbelContrib/AiryKernel/TailAsymptotic.lean` — the sharp-tail assembly:
  the `O(1/z)` rates for the
  Schläfli integrals (`schlaefliK13_sub_lead_abs_le`,
  `neg_deriv_schlaefliK13_sub_lead_abs_le`), the Airy-derivative rate
  `neg_deriv_airyAiReal_sub_lead_isBigO`, the exact constant identities
  `two_mul_leadAiDeriv_two_mul` (`2·leadAi′(2M) = ρ(M)`) and
  `leadIntegral_two_mul_eq_rhoM_div`, the trace expansion
  `traceAiryTilde_sub_traceLead_isLittleO`, the det₁ remainder
  `one_sub_detOneAiryTilde_sub_trace_isLittleO`, and the
  two-term sharp tail `piT_sub_traceLead_isLittleO`
  (`π_T(M) = Tρ(M) + ρ(M)/(4M) + o(ρ(M)/M)`) with the Quastel–Remenik determinant
  identity for `π_T` carried as the hypothesis field `hpi` (discharged in `AiryKernel/TraceWeight`).
  `Airy1GumbelContrib/AiryKernel/Touching.lean` — the paper's touching-block estimate in
  determinant form: the lead cancellation
  `2·traceLead M 1 − traceLead M 2 = ρ(M)/(4M)`, and for
  `touchDet = 2π₁ − π₂` (with `π_T = 1 − det₁(1 − Ã_{·,T})`) the remainder
  `touchDet_sub_isLittleO`, the corollary `touchDet_isEquivalent`
  (`touchDet ~ ρ/(4M)`) and the bound `touchDet_isBigO`, from the sharp one-block tail at
  `T = 1, 2`.
  `Airy1GumbelContrib/AiryKernel/TraceWeight.lean` — weight independence of the
  conjugated Airy operator (compare [QuastelRemenik2012], in their trace-class proposition):
  `Ã_a^(m+1) = kernelOperator(e^{-ax} K_m e^{ay})`,
  `trace_pow_airyTildeOp_indep`, `fredholmDetOne_airyTildeOp_indep`, and
  `detOneAiryTilde_one_eq_weight_two` (Quastel–Remenik's own weight a = 2 at T = 1).
- `TwoInterval/`: `Airy1GumbelContrib/TwoInterval/TwoIntervalOps.lean` — the two-interval
  operator algebra: the kernels of `K₁`, `K₂`, `C_r`, `K_∪`, the
  decomposition `K̃∪ = K̃₁ + K̃₂ − C̃_r` (`twoIntKCup_decomp`), and
  the conditional trace cancellation `trace_twoIntKCup`.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalTrace.lean` — the two-interval trace
  formula and four-sector decomposition: the kernel
  factorization `C̃_r = A_r W_{S,a}` (`crKerT_eq_compKernel_aRKer_wSKer`), the
  HS-product trace formula `Tr C̃_r = ∫∫ A_r(x,w) W_{S,a}(w,x)`
  (`trace_crKerT_eq`, conditional on the `MemLp` interface discharged in
  `TwoIntervalMembership`), the weight cancellation `Tr C̃_r = Tr C_r`, and the sector split
  `trace_crKerT_eq_sectors`.
  `Airy1GumbelContrib/TwoInterval/FRExponents.lean` — the FR-sector exponent
  calculus: the `d`-split quadratic lower bounds
  `h1Exp_ge_quadratic_of_d_nonneg`/`h1Exp_ge_quadratic_of_d_neg` (replacing the paper's
  Hessian/Taylor estimate by a sharper elementary argument with mass
  `O(sqrt L) e^{-J}`), the negative-Airy `G_1`/`G_{2,-}` packages with the
  genuine chi-largeness `frI1Minus_E0_ge`/`frI2Minus_E20_ge`, the
  `H_2~ = F + v^2/2` reduction (`h2Tilde_eq_saddleF_add`), the reflected heat–CDF identity
  `heatKernel_conv_cdf_Ioi`, the Chernoff bounds `frI1_Jbound`/`frI2_Kbound`/
  `frI2_gamma_int_le`, and the absorption `saddleJ_le_rpow`.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalMembership.lean` — the membership
  discharges: `L²`/trace-class membership of
  `K̃₁`, `K̃₂`, `C̃_r`, `K̃∪` (`memLp_k1KerT`/`isTraceClass_k1KerT`, …,
  `memLp_kcupKerT`/`isTraceClass_kcupKerT`), the `L² → L²` CLM packaging
  (`conjHeatCLM`, `enorm_conjHeatCLM_le`), and the discharged trace cancellation
  `trace_twoIntKCup_discharged` with only the admissibility
  side condition `r + 3 ≤ a` remaining as hypothesis.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalDetRem.lean` — the det₁-linearization
  algebra and the determinant-side steps of the paper's two-interval estimate:
  the three-determinant combination `joint_detOne_comb_twoInt_eq`
  (on the discharged trace cancellation), the HS bounds
  `twoInt_k1_bounds`/`twoInt_k2_bounds`/`twoInt_kcup_bounds`, the packaged
  `twoInt_stepThree`, and the remainder bound `joint_detOne_comb_abs_le`.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalSumEst.lean` — the summation
  estimates: the κ-identity `kappa_rpow_identity`, the geometric-majorant package, and the
  two `o(ρ(M))` statements
  `stepFive_first_sum_ratio_tendsto_zero` and
  `stepFive_second_sum_ratio_tendsto_zero`.
  `Airy1GumbelContrib/TwoInterval/SectorRR.lean` — the RR-sector trace bound:
  the Airy bound packages, the `±` split
  `trSectorRR_eq_plus_add_minus` (MemLp-conditional), the junk-safe
  pair change of variables `integral_pair_sym_antisym` (Jacobian 4),
  the Chernoff-envelope dominator collapse, the RR+ saddle bound
  `trSectorRRplus_abs_le` (`O(e^{−J_M(r)})`), the RR−
  boundary bound `trSectorRRminus_abs_le` (`O(e^{−cM²})`),
  and the main bound `trSectorRR_abs_le` (`|Tr C_r^{RR}| ≤ C₁e^{−J} + C₂e^{−cM²}`).
  `Airy1GumbelContrib/TwoInterval/SectorFR.lean` — the FR-sector trace bound:
  the `D₁`/`D₂` kernel split
  `trSectorFR_eq_frI1_add_frI2`, the exact inner
  evaluations `frI1_eq` (heat–CDF closed form `frJ1`) and `frI2_eq`
  (the `K(α,γ)` convolution `frK2`), the `±` domination packages
  `abs_frI1_le`/`abs_frI2_le`, the four piece bounds, and the main bound
  `abs_trSectorFR_le_absorbed` (`|Tr C_r^{FR}| ≤ C_χ(1+r)^{1/2}e^{−J_M(r)}`),
  with fully discharged corollaries
  (`abs_trSectorFR_le_absorbed_discharged`, `MemLp` discharged at `a = √(2M)`).
  `Airy1GumbelContrib/TwoInterval/SectorRF.lean` — the RF sector by involution:
  the factor symmetries
  `qRKerTwo_symm`/`qFKerTwo_symm`/`bAiryKer_symm`, the pointwise involution
  `sectorIntegrand_RF_eq_FR_involution`, the trace equality
  `trSectorRF_eq_trSectorFR` (the inner `(y,z)` swap plus one outer
  `(x,w)` swap with the four-sector dominator transported across `Prod.swap`), and
  the main bound `abs_trSectorRF_le_absorbed`
  (`|Tr C_r^{RF}| ≤ C_χ(1+r)^{1/2}e^{−J_M(r)}`) plus discharged corollary.
  `Airy1GumbelContrib/TwoInterval/SectorFF.lean` — the FF sector:
  the free-kernel evaluations, the four-piece split
  `trSectorFF_eq_sum_pieces` on the outer `(x,w)` half-lines, the inner
  collapses (a Gaussian-integral identity on `T_{--}`, never a full collapse there; semigroup
  collapses on the mixed pieces and `T_{++}`), the piece bounds
  `trSectorFF{mm,pm,mp,pp}_abs_le`, and the main bound `trSectorFF_abs_le`
  (`|Tr C_r^{FF}| ≤ C_χ e^{−J_M(r)}`, no `(1+r)^{1/2}`
  factor; conditional on the `MemLp` interface).
  `Airy1GumbelContrib/TwoInterval/TwoIntervalTraceBound.lean` — the trace
  assembly: the RR
  absorption helper `exp_neg_mul_sq_le_exp_neg_saddleJ`, the sector-sum core
  `abs_sector_sum_le`, and the main bounds `abs_trace_crKerT_le` (conditional on
  the `MemLp` interface) and `abs_trace_crKerT_le_discharged`
  (`|Tr C̃_r| ≤ C_χ(1+r)^{1/2}e^{−J_M(r)}` at `a = √(2M)`), plus `abs_trCr_le`.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalTraceSign.lean` — the near-sign lower
  bound for the same trace (input N1 of the two-interval sign bound): barrier Gaussian
  decay of `Q` and `QP_rQ` (`qPrQKer_le_gauss_left/right`), the pointwise domination of the
  negative part of the trace integrand, the conditional `trace_crKerT_ge_neg`,
  and the discharged statements `trace_crKerT_ge_neg_discharged`
  (`Tr C̃_r ≥ −C e^{−M²/16}`) and `trace_crKerT_ge_neg_discharged_a`
  (`Tr C̃_r ≥ −C e^{−a⁴/64}`, `a = √(2M)`, i.e. `−o(ρ²)`).
  `Airy1GumbelContrib/TwoInterval/TwoIntervalShift.lean` — the second-block
  determinant equals the first (the paper's joint-block lemma: cyclicity +
  the heat–Airy identity): `fredholmDetOne_k2KerT_eq_k1KerT`, with the
  right-factor composition `kernelOperator_wKernel_comp_conjHeatCLM` and
  the congruence helper `fredholmDetOne_congr`.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalPlemelj.lean` — the exact algebra of the
  Plemelj-exponent argument for the two-interval sign bound: `det₁(I−K) = exp(−τ_K)`,
  the δ identity
  `joint_detOne_comb_eq_plemelj`, the second-order expansion `plemeljDelta_eq`
  (`δ = −tr C + tr(AB) − tr(AC) − tr(BC) + ½tr C² + cubic tails`), the cubic tail
  bound `abs_plemeljTail3_le`, and the assembly `twoInt_joint_ge_plemelj` /
  `twoInt_joint_ge_plemelj_eventually` (`X ≥ π₁² − d₁²Δ`, N1 and HS bounds
  discharged, N2/N3 as hypotheses), plus sign/association corollaries.
  `Airy1GumbelContrib/TwoInterval/TwoIntervalN3.lean` — the Hilbert–Schmidt decay of
  `C̃_r` at the weight `a = √(2M)` (input N3 of the sign bound): the two-barrier bound
  `qPrQKer_le_barrier` (`QP_rQ ≤ (4π)^{−1/2} G(x)G(w)`, `G = e^{−((M−x)⁺)²/4}`),
  the square integral `integral_aRKer_sq_le`, the conditional `hsNorm_crKerT_le`,
  and the discharged statement `hsNorm_crKerT_le_discharged`
  (`‖C̃_r‖₂ ≤ C e^{−(2/3)a³ − rM}`, `a = √(2M)`, `1 ≤ r ≤ χa`).
  `Airy1GumbelContrib/TwoInterval/TwoIntervalN2.lean` — the decorrelation bound
  for the two blocks (input N2 of the sign bound): the forward heat–Airy identity
  `heatAiryConv_any` (`W₁P_{1+r} = P_rB₀`), the `W`-kernel bound for every real `T`
  (`wKernel_sq_integral_le_any`), the sharp asymmetric-weight `Q` bound
  `vAsym_sq_integral_le`, the weight-free trace `trace_k1k2_eq_integral`, the
  two-weight split `trace_k1k2_le`, and the discharged statement
  `trace_k1k2_le_discharged` (`tr(K̃₁K̃₂) ≤ C(1+2M²)(1+256M)e^{−(4/3)a³ − 2ar²}`).
  `Airy1GumbelContrib/TwoInterval/TwoIntervalSign.lean` — the two-interval sign
  bound by the Plemelj argument: N1–N3 fed into the Plemelj assembly and
  compared with the sharp one-block tail (`π₁ ≥ ρ/2`, `ρ² = C_*²M^{1/2}e^{−(4/3)a³}`) by the
  absorption `plemeljMargin_le`; main statements `twoInt_joint_ge_assoc_eventually`
  (`X ≥ (1 − ε)π₁²`, every `ε > 0`) and `twoInt_joint_pos_eventually` (`X > 0`),
  eventually in `M`, uniformly for `1 ≤ r ≤ χ√(2M)`, `χ < 1`.
- `FredholmDet/` (the entire Fredholm determinant `det(1 − zA)` of a trace-class operator):
  `Airy1GumbelContrib/FredholmDet/Multiplicativity.lean` — multiplicativity of the
  entire Fredholm determinant (Simon, *Trace Ideals*, Thm 3.5(a)):
  `fredholmDet_add_sub_comp` (`det(1 − (A + B − AB)) = det(1 − A) det(1 − B)` for
  finite trace norm), the coupling form `fredholmDet_add_sub_smul_comp`, and
  `fredholmDet_ne_zero_of_isUnit` (`1 − A` invertible ⇒ `det(1 − A) ≠ 0`). Method:
  right finite sections `A Pₛ` (exact matrix determinants, `Matrix.det_mul`),
  trace-norm convergence `‖A Pₛ − A‖₁ → 0`, and the trace-norm Lipschitz bound of
  `SimonBound`; rank-one non-vacuity witness `Probe.probe_multiplicativity`.
  `Airy1GumbelContrib/FredholmDet/KernelDet.lean` — kernel-operator compatibility of the
  entire determinant: the Taylor coefficients `c₀ = 1`,
  `c₁ = −tr A`, `c₂ = ((tr A)² − tr A²)/2` (`fredholmDet_taylor_two`; minor series
  regrouped fiberwise over `(i, j) ↦ {i, j}`, Parseval); for a composite `L²(ℝ²)`
  kernel `L = K ⋆ K'`, the trace link `tr T_L = ∫ L(x, x)` and the `n = 1, 2` Fredholm
  expansion terms `c₁ = −∫ L(x, x)`, `c₂ = ½ ∫_{ℝ²} det[L(xᵢ, xⱼ)]`; Quastel–Remenik tie-in
  for `airyTildeOp` and the two-interval `kcupOp` (trace class, finite trace norm,
  coefficients). The general-`n` expansion is not proved.
  `Airy1GumbelContrib/FredholmDet/TracePowDet.lean` — the entire determinant depends only on
  the traces of powers: `fredholmDet_eq_of_trace_pow_eq`
  (`tr Aᵐ = tr Bᵐ` for all `m ≥ 1` ⇒ `det(1 − zA) = det(1 − zB)` for every `z`; disk agreement
  with `fredholmDetOne` plus the identity theorem); checks re-deriving cyclicity
  (`fredholmDet_comp_comm'`) and non-vacuity (`trace_eq_of_fredholmDet_eq`).
  `Airy1GumbelContrib/FredholmDet/DetIsometry.lean` — determinants across an isometric
  embedding: for a linear isometry `J : E → F`, trace-class `X` on `F` and `Y` on `E`
  with `X ∘ J = J ∘ Y` and `X` vanishing on `(range J)ᗮ`, `det(1 − zX) = det(1 − zY)` for every
  `z` (`fredholmDet_eq_of_isometry_intertwine`; Hilbert-basis extension of `J(b)` and minor
  reindexing).
  Block-operator determinant algebra on the `L²` product `WithLp 2 (E × F)` (generic and
  convention-free; used by the two-time analysis in `TwoTime/`):
  `Airy1GumbelContrib/FredholmDet/TraceClassAdd.lean` — trace class is closed under addition
  (`IsTraceClass.add`, `IsTraceClass.sub`): finite canonical index ⇒ every operator is
  Hilbert–Schmidt; infinite ⇒ `WithLp 2 (E × E) ≃ₗᵢ E` (`exists_prod_self_equiv`, adapted Hilbert
  basis and `ι ⊕ ι ≃ ι`), transporting `HSFactorization.add`; plus the cross-space bounded ideal
  `IsHilbertSchmidt.sandwich`.
  `Airy1GumbelContrib/FredholmDet/BlockDet.lean` — rectangular Sylvester
  `det_E(1 − zAB) = det_F(1 − zBA)` for Hilbert–Schmidt `A : F → E`, `B : E → F`
  (`fredholmDet_comp_comm_rect`; bounded-factor variants `_rect_right`, `_rect_left`); the block
  operator `blockOp A B C D` with block multiplication, corner trace-class constructors
  (`IsRectTraceClass` off the diagonal), `isTraceClass_blockOp`, `trace_blockOp`
  (`tr = tr A + tr D`); block-triangular determinants `fredholmDet_blockOp_upper`/`_lower`
  (`det(1 − z[[A, X], [0, D]]) = det(1 − zA)·det(1 − zD)`); and the block Schur step
  `fredholmDet_blockOp_schur'` (`R(1 − A) = 1` ⇒ `det(1 − [[A, B], [C, D]]) =
  det(1 − A)·det(1 − (D + CRB))`; `_of_norm_lt_one` via `Units.oneSub`).
- `Fdd/` (the `n`-time Airy₁ finite-dimensional distribution operator):
  `Airy1GumbelContrib/Fdd/GaussTools.lean` — Gaussian closed forms (Chernoff form via
  completed square + Chapman–Kolmogorov), the weight bound `1 + v² ≤ C(e^{δv} + e^{−δv})`,
  half-plane/quadrant plane-integrability dominators, `memLp_of_sq_le`.
  `Airy1GumbelContrib/Fdd/FddKernel.lean` — the `n`-time discrete hitting kernel
  `hitKerN = p_S − Λ e^{τΔ}` over a `(level, gap)` list (the kernel `Λ` of
  [QuastelRemenik2013]), `0 ≤ H ≤ p_S`, and the one-step recursion on `u ≤ x₁`.
  `Airy1GumbelContrib/Fdd/FddVBound.lean` — `memLp_fddVKer`: the weighted kernel
  `e^{−au} H e^{−av} φ(v)` is `L²(ℝ²)` for all real levels, positive gaps and `a > 0`
  (union/Chernoff bound `hitKerN_le_eBnd` by induction on the list).
  `Airy1GumbelContrib/Fdd/FddOp.lean` — `fddOp` (`T_V ∘ T_W` at `a = 2S`, padding 1),
  trace class and finite trace norm, the composite-kernel identity
  `compKernel_fddVKer_wKernel`, and the candidate CDF
  `airy1FinCdf I x = det(I − J̃)` (sorted `Finset`, positive gaps by construction, `F_∅ = 1`),
  with sanity checks (`airy1FinCdf_empty`, `airy1FinCdf_singleton`,
  `compKernel_fddVKer_one_level`: the one-time kernel is the conjugate of `1_{u>x} Ai(u+y)`).
  No probabilistic property of `airy1FinCdf` is proved here.
  `Airy1GumbelContrib/Fdd/FddIndep.lean` — the composite
  kernel `H ⋆ g_S = Ai(u + y) − (Λ ⋆ g_{S−τ})(u, y)` (`compKernel_hitKerN_bAiry`, τ-free);
  same levels and interior gaps (`SamePad`) give the same operator `fddOpAt` at any common
  admissible weight; `fredholmDet (fddOpAt … a)` is independent of the weight `a ≥ S + 1`
  (traces of all powers are weight-free, then `fredholmDet_eq_of_trace_pow_eq`); hence
  `airy1FinCdf` is unchanged at any admissible padding and weight
  (`airy1FinCdf_eq_fredholmDet_fddOpAt`).
  `Airy1GumbelContrib/Fdd/FddCont.lean` — continuity of the fdd
  determinant in the levels, jointly (`continuous_airy1FinCdf`: `Continuous (airy1FinCdf I)`;
  list form `continuous_fddDetLev`, levels by position via `zipLev`), by a uniform `L²`
  majorant on bounded level sets (`sq_fddVKer_le_domF`), pointwise kernel convergence off the
  null sets `u = x_k`, dominated convergence and `tendsto_fredholmDet_comp` with the fixed `W`
  factor. Analytic core of dropping a time: with `EReal` levels (`P̄_{+∞} = I`,
  `levSet_top`), if every level
  converges in `EReal` to a limit `≠ ⊥` (e.g. `x_k → +∞`), `‖V(xₙ) − V(x)‖₂ → 0` and the
  determinant converges (`tendsto_fddDetLev_ereal`); the Chapman–Kolmogorov identification of
  that limit with the dropped-time list is not done here.
  `Airy1GumbelContrib/Fdd/FddDrop.lean` — consistency, dropping a time:
  `tendsto_airy1FinCdf_erase` (for any `t ∈ I`, `x_t → +∞` with the other levels
  converging gives `F_I → F_{I∖{t}}`; `update` form `tendsto_airy1FinCdf_update`) and
  `tendsto_airy1FinCdf_one` (all levels `→ +∞` gives `F_I → 1`). Interior/last time: the `⊤`
  level merges adjacent heat factors (`lamKerT_erase`, Chapman–Kolmogorov), then padding and
  weight independence; first time: `H_n = p_{g₁} ⋆ H_{n−1}` (`hitKerT_head_top`) and
  `W_S ⋆ V_n = W_{S−g₁} ⋆ V_{n−1}` (`compKernel_wKernel_fddVKer_heat`), then cyclicity twice
  (`fredholmDet_swap_heat`) and weight independence.
  `Airy1GumbelContrib/Fdd/FddGOE.lean` — the `n = 1` GOE anchor:
  `airy1FinCdf {t} x = det(I − P_x B₀ P_x)_{L²(ℝ)}` (`airy1FinCdf_singleton_eq_goe`; outer
  weight moved across `T_W T_V`, two cyclicity steps; `P_x B₀ P_x` trace class) and, through
  the shift–extension isometry `L²(0, ∞) → L²(ℝ)`, Ferrari–Spohn's
  `airy1FinCdf {t} x = det(I − B_{2x})_{L²(0,∞)}`, `B_s(a, b) = Ai(a + b + s)`
  (`airy1FinCdf_singleton_eq_fsGOE`). That this determinant is `F_GOE(2x)` is the cited
  Ferrari–Spohn identity, not proved here.
  `Airy1GumbelContrib/Fdd/FddShift.lean` — time-shift invariance: the determinant sees
  the time set only through sorted gaps and levels, so `F_{I+c} = F_I`
  (`airy1FinCdf_shift`, explicit relabelling `y s = x (s − c)`; `airy1FinCdf_shift_of_eq` /
  `airy1FinCdf_shift_image_of_eq` for any `y` agreeing with `x` along `t ↦ t + c`; core
  `airy1FinCdf_eq_of_sort_eq_map_add`, with `sort_map_addRight`: sorting commutes with translation).
- `SmallWeight/` (two-time estimates):
  `Airy1GumbelContrib/SmallWeight/FddSmallWeight.lean` — the fdd operator at any weight `a > S`
  (`fddOpLt`, equal to `fddOpAt` by `rfl` on `a ≥ S + 1`): the relaxed `W`-kernel bound
  `∫∫ W_{T,a}² ≤ C e^{(2/3)T³−2aT²}/(a−T)` for `T < a ≤ T + 1` (`wKernel_sq_integral_le_small`,
  `memLp_wKernel_lt`), weight independence for all weights `> S`, and
  `airy1FinCdf_eq_fredholmDet_fddOpLt` (any padding, any weight `> S`).
  `Airy1GumbelContrib/SmallWeight/TwoTimeDefect.lean` — forward two-time CDF defect:
  `|F_{{x}}(a) − F_{{x,x+t}}(a, b)| ≤ C(m₀) e^{−(b−a)²/(8t)}` for `−m₀ ≤ a ≤ b`, `0 < t ≤ 1`
  (`airy1FinCdf_twoTime_defect`; shape form `airy1FinCdf_twoTime_defect_shape`), from the
  weight-parametric `airy1FinCdf_twoTime_defect_le` (any padding `τ`, weight `w > t + τ`,
  explicit constants `defectConst`, `oneTimeConst`): one frame and one `W` for both
  determinants, the defect kernel `1_{u≤a}∫p_t(u−x)1_{x>b}p_τ(x−v)dx` bounded by a Chernoff-free
  Gaussian split, closed-form Gaussian integrals, and the Lipschitz determinant bound.
  `Airy1GumbelContrib/SmallWeight/TwoTimeDefectRev.lean` — reverse order: `|F_{{x+t}}(b) −
  F_{{x,x+t}}(a, b)| ≤ C(m₀) e^{−(a−b)²/(8t)}` for `−m₀ ≤ b ≤ a` (`airy1FinCdf_twoTime_defect_rev`,
  weight-parametric `airy1FinCdf_twoTime_defect_rev_le`), via the first-time-`⊤` kernel and
  `fredholmDet_swap_heat`; no time reversal.
  `Airy1GumbelContrib/SmallWeight/SmallWeightDefect.lean` — the two-time defect at
  small weight with explicit dependence on the truncation level: for `M ≥ 2`, gaps
  `0 < t ≤ 1/(2M)` and levels `≥ −2M`, both orders hold with `C_M = exp(K M^{5/2})`
  (`smallWeight_fwdDefectBoundOn`, `smallWeight_revDefectBoundOn`, combined
  `smallWeight_defect_headline`), frame `τ = 1/M`, `w = 2(t + τ)`; `log C_M = o(M³)`
  (`isLittleO_log_smallWeightDefectConst`). Gap-restricted shapes `FwdDefectBoundOn L δ C`,
  `RevDefectBoundOn L δ C` (the `t ≤ 1` forms at `δ = 1`).
- `Mesh/` (dyadic mesh limit):
  `Airy1GumbelContrib/Mesh/MeshLimit.lean` — the constant-level fdd on the dyadic mesh
  `I_n = {x + kT/2ⁿ : k < 2ⁿ}` (`meshSet`, `mem_meshSet`, `sort_meshSet`): with padding `T/2ⁿ`
  the entries are `(M, T/2ⁿ)` repeated `2ⁿ` times, total time exactly `T` (`gapSum_meshTail`),
  and `F_{I_n}(M, …, M) = det(I − meshOp M T n)` at weight `2T` for `T ≥ 1`
  (`airy1FinCdf_meshSet`); `meshOp` and `airyTildeOp M T (2T)` share the `W` factor
  `wKernel T (2T)` (`meshOp_eq`). Under the named kernel hypotheses `MeshHittingLimit M T`
  ((K1) `H_n ≤ Q_{M,T}` a.e., (K2) `H_n → Q_{M,T}` a.e., `H_n = meshHitKer M T n`; `0 ≤ H_n` is
  a theorem), dominated convergence gives `∫∫(V_n − V)² → 0`
  (`tendsto_integral_sq_meshVKer`), hence `det(I − meshOp M T n) → det(I − Ã_{M,T})`
  (`tendsto_fredholmDet_meshOp`) and `F_{I_n}(M, …, M) → det(I − Ã_{M,T})`
  (`tendsto_airy1FinCdf_meshSet`). Orientation checks at `n = 0`: `meshHitKer_zero_le_qMT`,
  `not_qMT_le_meshHitKer_zero`. (K1)/(K2) themselves are proved in the next two modules,
  by dyadic reflection.
  `Airy1GumbelContrib/Mesh/Skeleton.lean` — the Brownian skeleton of the discrete
  hitting kernel: for a Mathlib `IsPreBrownianReal` process with measurable coordinates and step
  `h = 2g`, the law of `u + X_{(k+1)h}` on `{u + X_{jh} ≤ M, j ≤ k}` (`X = B − B 0`) has density
  `lamKerN (M, g) (replicate k (M, g)) (u, ·)` (`measure_skelSet`; induction along the
  `lamKerN` cons-recursion, weak Markov `indepFun_shift` at time `h` composed with finitely many
  coordinates, Tonelli); `N(μ, 2g)` has density `heatKernel g (μ − ·)`
  (`gaussianReal_eq_withDensity_heatKernel`).
  `Airy1GumbelContrib/Mesh/Reflection.lean` — reflection for a Mathlib `IsBrownianReal` process
  with measurable coordinates (`τ = 2T`, grid `jτ/2ⁿ`, start `u < M`): first-crossing
  decomposition (`compl_survSet_eq`), the symmetric flip of the post-crossing increment
  (`measure_flip`, `measure_firstSet_flip`; fixed-time independence only, no strong Markov),
  the pathwise overshoot bound from uniform continuity on `[0, τ]` (`exists_grid_incr_lt`,
  `eventually_mem_reflSet`), the reflection principle in CDF form
  `P(crossing, u + X_τ ≤ v) = P(u + X_τ ≥ 2M − v)` for `v ≤ M` (`measure_crossSet_inter_Iic`),
  the crossing law has density `Q_{M,T}(u, ·)` (`measure_crossSet_inter`), the mesh kernels as
  densities (`measure_survSet_inter`, `measure_compl_survSet_inter`), and the kernel fact
  `MeshHittingLimit M T` for every `M` and `T > 0` (`meshHittingLimit_of_isBrownianReal`):
  (K1) from `(survSet n)ᶜ ⊆ crossSet`, (K2) by monotone convergence of the densities and
  equality of total masses, `u > M` exact (`meshHitKer_eq_qMT_of_lt`), Tonelli on `ℝ²`. The
  Brownian inhabitant is supplied by the main package (`Airy1Gumbel.meshHittingLimit`).
  `Airy1GumbelContrib/Mesh/TwoBlockMesh.lean` — the two-interval determinant from the
  two-block mesh: two unit blocks `[x, x+1]`,
  `[x+1+r, x+2+r]`, constant level `M`, mesh level `m ≥ 1`, `g = 2⁻ᵐ`: the union mesh has
  entries `(M, g)^{×(2ᵐ−1)}, (M, g+r), (M, g)^{×2ᵐ}` (`cupList`, total time `2 + r`,
  `gapSum_cupList`), so the fdd operator `cupOp` is admissible at weight `a` iff `r + 3 ≤ a`
  (at `a = √(2M)` the `kcupKerT` guard). Kernel calculus: `lamKerN_append` (concatenated
  entries compose), `lamKerN_bump` (a longer last gap composes with `p_r`), hence
  `Λ^∪_m = Λ_m ⋆ (P_r ⋆ Λ_m)` (`lamKerN_cupList`) and `H^∪_m = p_{2+r} − Λ_m ⋆ (P_r ⋆ Λ_m)`
  (`cupHitKer_eq`) against `D_r = p_{2+r} − Λ ⋆ (P_r ⋆ Λ)` (`dRKer_eq_heat_sub`). From the
  one-block `MeshHittingLimit M 1`: `H^∪_m ≤ D_r` a.e. (`ae_cupHitKer_le_dRKer`) and
  `H^∪_{n+1} → D_r` a.e. (`ae_tendsto_cupHitKer`; generic `ae_tendsto_compKernel`,
  `ae_compKernel_mono`), so with the shared right factor `W_{2+r,a}`
  (`cupOp_eq`, `kernelOperator_kcupKerT_eq`) `det(I − cupOp) → det(I − K̃∪)`
  (`tendsto_fredholmDet_cupOp`); the union-mesh fdd identity `airy1FinCdf_cupSet`; combined
  `tendsto_airy1FinCdf_cupSet`.
- `TwoTime/` (the Airy-specific two-time analysis: block-determinant form of the two-time
  CDF and its sharp trace-norm estimates; the generic block-operator determinant algebra it
  uses is in `FredholmDet/TraceClassAdd` and `FredholmDet/BlockDet`).
  `Airy1GumbelContrib/TwoTime/BlockDetGOE.lean` — instance check on `L²(ℝ) ⊕ L²(ℝ)` with the
  `Fdd/FddGOE` `goeOp` blocks (`fredholmDet_blockOp_goeOp_eq_mul_airy1FinCdf`).
  `Airy1GumbelContrib/TwoTime/TwoTimeSplit.lean` — multiplication operators
  `mulOp` on `L²(ℝ)` and their composition with kernel operators; `IsHilbertSchmidt.add'` across
  spaces; the two-time kernel split `V = m·s₁ + r ⋆ s₂` (`fddVKer_two_level_eq`,
  `kernelOperator_fddVKer_two_level`).
  `Airy1GumbelContrib/TwoTime/TwoTimeBlock.lean` — the four trace-class blocks
  `B = goeOp x₁`, `qOp`, `k21Op`, `dOp` and their factor identities (`block11_eq` … `block22_eq`).
  `Airy1GumbelContrib/TwoTime/TwoTimeBridge.lean` — the block-determinant form: `fddOp = ℛ ∘ 𝒞`,
  bounded-factor rectangular Sylvester, `airy1FinCdf {t₀, t₁} = det(I − [[B, Q], [K₂₁, D]])`
  (`airy1FinCdf_pair_eq_blockDet`, `airy1FinCdf_pair_const_eq_blockDet`).
  `Airy1GumbelContrib/TwoTime/TwoTimeSchur.lean` — block Schur/LU
  factorisation `airy1FinCdf {t₀, t₁} = det(I − B)·det(I − Z) = F_{t₀}(x₁)·det(I − Z)` with
  `Z = D + K₂₁ R Q` for any left inverse `R` of `1 − B` (Neumann `goeResolvent` under
  `‖B‖ < 1`, `‖R‖ ≤ (1 − ‖B‖)⁻¹`), `Z` trace class; the exact excess
  `F_{0,d}(w, w) − f² = f·(det(I − Z) − det(I − B))` and the Simon-Lipschitz excess bound
  `|F − f²| ≤ |f|·2‖Z − B‖₁·exp(2(‖Z‖₁ + ‖B‖₁))`; `Z − B = (D − B) + K₂₁ R Q` with trace-norm
  triangle bounds (`airy1FinCdf_pair_eq_schur`, `abs_airy1FinCdf_pair_const_sub_sq_le`).
  `Airy1GumbelContrib/TwoTime/TwoTimeL2.lean`, `TwoTimeKernel.lean`, `TwoTimeEst.lean` — the
  trace-norm estimates: integrability of the `Q`/`D` inner sections, the kernel identity
  `D − B = −K₂₁T` at equal levels
  (`dOp_sub_goeOp`, `K₂₁T` one `L²` kernel), the tuned heat split `K₂₁ = K_a ⋆ K_b`
  (`γ = s + √(2w + s²)`), and the trace-norm estimates (K1)–(K5): `‖K₂₁‖₁, ‖K₂₁T‖₁ ≤ C e^{−Ψ + 16(1+w+d²)}`,
  `‖Q‖ ≤ C e^{(9/2)d}`, `‖B‖₁ ≤ C`, `‖B‖ ≤ 1/2` for `w ≥ w₀`, and
  `‖(D − B) + K₂₁RQ‖₁ ≤ C e^{−I(w) − 2wd + 20(1+w+d²)}` for `‖R‖ ≤ 2`.
  `Airy1GumbelContrib/TwoTime/TwoTimeSharp.lean` — sharp-Ψ form of the estimates: heat time `τ = 1/(1+w+d)²`, giving `‖K₂₁‖₁, ‖K₂₁T‖₁ ≤ C(1+w+d)e^{−Ψ}`, `‖Q‖ ≤ C(1+d)` and `‖(D − B) + K₂₁RQ‖₁ ≤ C(1+w+d)²e^{−Ψ}` for `w ≥ 1/2`, `‖R‖ ≤ 2`.
  `Airy1GumbelContrib/TwoTime/TwoTimeSharpSqrt.lean` — square-root prefactor for the sharp-Ψ estimates: keeping `c₀(τ) ≤ D` gives `‖K₂₁‖₁, ‖K₂₁T‖₁ ≤ C√(1+w+d)e^{−Ψ}`; the Chernoff rate `1/√(1+d)` gives `‖Q‖ ≤ C√(1+d)`; hence `‖(D − B) + K₂₁RQ‖₁ ≤ C√(1+w+d)√(1+d)e^{−Ψ} ≤ C(1+w+d)e^{−Ψ}` for `w ≥ 1/2`, `‖R‖ ≤ 2` (the bound `‖Q‖ ≤ 1` is in `TwoTimeQNorm`).
  `Airy1GumbelContrib/TwoTime/TwoTimeSharpD.lean` — prefactor `√(1+d)` for the sharp-Ψ estimates: `c₀(τ) ≤ D ≤ 2γ²` cancels the factor `(1/(2γ))²`, so `‖K₂₁‖₁, ‖K₂₁T‖₁ ≤ √2·C♯e^{−Ψ}` with no polynomial prefactor; hence `‖(D − B) + K₂₁RQ‖₁ ≤ C√(1+d)e^{−Ψ}` for `w ≥ 1/2`, `‖R‖ ≤ 2` (the `√(1+d)` is from `‖Q‖ ≤ C√(1+d)`).
  `Airy1GumbelContrib/TwoTime/TwoTimeQNorm.lean` — `‖Q‖ ≤ 1` for all levels and `d > 0` (`norm_qOp_le_one`): the factorisation `Q = P₁B₀P̄₁e^{dΔ}P₂` (`integral_qKer_mul_eq`), the heat contraction (`eLpNorm_qHeatFun_le`) and the `L¹ ∩ L²` Airy bound of `Airy/AiryTransformL2`; removes the source of the `√(1+d)` prefactor (step A5).
  `Airy1GumbelContrib/TwoTime/TwoTimeSharpE.lean` — no polynomial prefactor for the sharp-Ψ estimates (step A6): with `‖Q‖ ≤ 1` (`norm_qOp_le_one`), `‖(D − B) + K₂₁RQ‖₁ ≤ 3√2·C♯e^{−Ψ}` for `w ≥ 1/2`, `d > 0`, `‖R‖ ≤ 2` (`traceENorm_twoTimeExcess_le_e`; `‖Q‖ ≤ 1` via the `L¹ ∩ L²` Airy contraction, not full unitarity).
  `Airy1GumbelContrib/TwoTime/TwoTimeNonvanishing.lean` — nonvanishing witnesses: `qKer`, `dKer` are nonzero at some `(u, m)` past the cuts (Laplace concentration at `y = x₁` as `m → ∞`; `exists_qKer_ne_zero`, `exists_dKer_ne_zero`).
  `Airy1GumbelContrib/TwoTime/TwoTimeOpNonvanishing.lean` — operator-level nonvanishing `qOp_ne_zero`, `dOp_ne_zero`: a zero kernel operator kills all rational interval integrals of a.e. section (`ae_forall_rat_setIntegral_Ioo_eq_zero`), and the inner integral is continuous in `m` past the cut (`continuousOn_blkInner`).
Pinned to mathlib master `cfc55fc5` (Lean v4.35.0).
-/
import Airy1GumbelContrib.Gumbel.Gumbel
import Airy1GumbelContrib.Airy.Airy
import Airy1GumbelContrib.Airy.AiryODE
import Airy1GumbelContrib.Airy.AiryReal
import Airy1GumbelContrib.Airy.BesselK13
import Airy1GumbelContrib.Airy.AiryBessel
import Airy1GumbelContrib.Airy.AiryAsymptotics
import Airy1GumbelContrib.Airy.AiryUniqueness
import Airy1GumbelContrib.Airy.AiryIdentity
import Airy1GumbelContrib.Airy.AiryLaplace
import Airy1GumbelContrib.Airy.AiryLaplaceFull
import Airy1GumbelContrib.Gaussian.MillsRatio
import Airy1GumbelContrib.HilbertSchmidt.HilbertSchmidt
import Airy1GumbelContrib.HilbertSchmidt.KernelHS
import Airy1GumbelContrib.TraceClass.TraceClass
import Airy1GumbelContrib.TraceClass.FredholmTwo
import Airy1GumbelContrib.TraceClass.FredholmOne
import Airy1GumbelContrib.Airy.AiryLeading
import Airy1GumbelContrib.Airy.AiryContour
import Airy1GumbelContrib.Airy.AiryFourier
import Airy1GumbelContrib.Airy.AiryTransform
import Airy1GumbelContrib.Airy.AiryTransformL2
import Airy1GumbelContrib.AiryKernel.AiryKernel
import Airy1GumbelContrib.AiryKernel.BackwardAiry
import Airy1GumbelContrib.AiryKernel.Conjugates
import Airy1GumbelContrib.AiryKernel.ConjugateW
import Airy1GumbelContrib.AiryKernel.Conjugate2to2
import Airy1GumbelContrib.AiryKernel.ConjugateV
import Airy1GumbelContrib.AiryKernel.TraceProduct
import Airy1GumbelContrib.AiryKernel.GaussianSaddle
import Airy1GumbelContrib.AiryKernel.ConjugateUPhi
import Airy1GumbelContrib.AiryKernel.TraceExpansion
import Airy1GumbelContrib.AiryKernel.TailAsymptotic
import Airy1GumbelContrib.AiryKernel.Touching
import Airy1GumbelContrib.TwoInterval.TwoIntervalOps
import Airy1GumbelContrib.TwoInterval.TwoIntervalTrace
import Airy1GumbelContrib.TwoInterval.TwoIntervalMembership
import Airy1GumbelContrib.TwoInterval.FRExponents
import Airy1GumbelContrib.TwoInterval.TwoIntervalDetRem
import Airy1GumbelContrib.TwoInterval.TwoIntervalSumEst
import Airy1GumbelContrib.TwoInterval.SectorRR
import Airy1GumbelContrib.TwoInterval.SectorFR
import Airy1GumbelContrib.TwoInterval.SectorRF
import Airy1GumbelContrib.TwoInterval.SectorFF
import Airy1GumbelContrib.TwoInterval.TwoIntervalTraceBound
import Airy1GumbelContrib.TwoInterval.TwoIntervalTraceSign
import Airy1GumbelContrib.TwoInterval.TwoIntervalPlemelj
import Airy1GumbelContrib.TwoInterval.TwoIntervalN3
import Airy1GumbelContrib.TwoInterval.TwoIntervalN2
import Airy1GumbelContrib.TwoInterval.TwoIntervalSign
import Airy1GumbelContrib.AiryKernel.TraceWeight
import Airy1GumbelContrib.TwoInterval.TwoIntervalShift
import Airy1GumbelContrib.FredholmDet.Hadamard
import Airy1GumbelContrib.FredholmDet.EntireDet
import Airy1GumbelContrib.FredholmDet.MatrixPlemelj
import Airy1GumbelContrib.FredholmDet.DiskAgreement
import Airy1GumbelContrib.FredholmDet.RankOneWitness
import Airy1GumbelContrib.FredholmDet.TraceNorm
import Airy1GumbelContrib.FredholmDet.SimonBound
import Airy1GumbelContrib.FredholmDet.Multiplicativity
import Airy1GumbelContrib.FredholmDet.KernelDet
import Airy1GumbelContrib.Fdd.GaussTools
import Airy1GumbelContrib.Fdd.FddKernel
import Airy1GumbelContrib.Fdd.FddVBound
import Airy1GumbelContrib.Fdd.FddOp
import Airy1GumbelContrib.Fdd.FddIndep
import Airy1GumbelContrib.Fdd.FddCont
import Airy1GumbelContrib.Fdd.FddDrop
import Airy1GumbelContrib.Fdd.FddGOE
import Airy1GumbelContrib.Fdd.FddShift
import Airy1GumbelContrib.SmallWeight.FddSmallWeight
import Airy1GumbelContrib.SmallWeight.TwoTimeDefect
import Airy1GumbelContrib.SmallWeight.TwoTimeDefectRev
import Airy1GumbelContrib.SmallWeight.SmallWeightDefect
import Airy1GumbelContrib.Mesh.MeshLimit
import Airy1GumbelContrib.Mesh.Skeleton
import Airy1GumbelContrib.Mesh.Reflection
import Airy1GumbelContrib.Mesh.TwoBlockMesh
import Airy1GumbelContrib.FredholmDet.TracePowDet
import Airy1GumbelContrib.FredholmDet.DetIsometry
import Airy1GumbelContrib.FredholmDet.TraceClassAdd
import Airy1GumbelContrib.FredholmDet.BlockDet
import Airy1GumbelContrib.TwoTime.BlockDetGOE
import Airy1GumbelContrib.TwoTime.TwoTimeSplit
import Airy1GumbelContrib.TwoTime.TwoTimeBlock
import Airy1GumbelContrib.TwoTime.TwoTimeBridge
import Airy1GumbelContrib.TwoTime.TwoTimeSchur
import Airy1GumbelContrib.TwoTime.TwoTimeL2
import Airy1GumbelContrib.TwoTime.TwoTimeKernel
import Airy1GumbelContrib.TwoTime.TwoTimeEst
import Airy1GumbelContrib.TwoTime.TwoTimeNonvanishing
import Airy1GumbelContrib.TwoTime.TwoTimeOpNonvanishing
import Airy1GumbelContrib.TwoTime.TwoTimeSharp
import Airy1GumbelContrib.TwoTime.TwoTimeSharpSqrt
import Airy1GumbelContrib.TwoTime.TwoTimeSharpD
import Airy1GumbelContrib.TwoTime.TwoTimeQNorm
import Airy1GumbelContrib.TwoTime.TwoTimeSharpE
