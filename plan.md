# Plan: Gaussian mixture priors satisfy the weighted-L¹ convergence hypothesis

Status: Phases 0–1 implemented and verified (see below); Phase 2 Step 0 is implemented
and verified (`modulus_tendsto_integrable` + `weighted_modulus_tendsto_integrable`,
public and axiom-audited; full build green, zero `sorry`); Steps 1–7 of Phase 2 are
planning documents.

**Correction round (latest session, after the Step-0 build).** A review pass found and
fixed real mathematical defects in this document (the code was unaffected — Step 0 was
finished to match the corrected mathematics):

1. Proof-strategy §2's quantization display went straight from the Jensen/Tonelli bound
   to `sup_s ∫ w(x)|φ_σ(x+s) − φ_σ(x)|dx`, **silently dropping the weight shift** `w(y+t)`
   created by the substitution `y = x − t`; its "only `δ/σ → 0` is needed" claim also
   omitted the requirement `σ → 0`, and it leaned on per-σ continuity of translation
   which is *not uniform in σ* along the diagonal (the Phase 2 design decisions already
   say so).
2. Phase 2 Step 3's displayed first term had the same weight-shift defect. Keeping the
   resulting `‖t‖·L₁` term — bounded by the **R-free** `M_f = ∫ ‖t‖ f`, not by
   `sup_{t∈B_R} ‖t‖ ≤ R√n` — is what keeps the `R_K → ∞` diagonal valid.
3. The ε/3 (§2) vs ε/2 (Step 6) budget wording was reconciled (both are valid; they
   correspond to different term splittings).
4. Step 0's statement/architecture text was rewritten to the proven form: `f(x+u)` sign
   (the (T)-lemma uses `f(x−u)`; equivalent by `u ↦ −u`), integer thresholds `K`/`K−1`
   (the tail lemma is stated at natural `k`, with `‖u‖ < 1`), core via
   `modulus_tendsto_integrable` scaled by `(1+K)`, budgets `ε/2 + ε/8 + ε/4`.
5. Stale statuses (header, Phase 2 header, deliverables, Step 0 status block) and
   gotcha 7 were updated; the final-round tactic gotchas are appended at the end.

## Goal

Prove that the hypothesis `hw` of `cme_uniform_balls_R` in `Main.lean` (weighted-L¹
convergence of the priors) is **satisfied by sequences of Gaussian mixture model (GMM)
priors**, and thereby unlock `cme_uniform_balls_R` for the estimator setting in which the
priors are GMMs.

Precise target theorem (to be added as a new file, working name
`ApproximationByGMM.lean`):

> **Theorem (GMM density in weighted L¹).** Let `f : EuclideanSpace ℝ (Fin n) → ℝ` be a
> probability density function (`IsPdf f`) with finite first moment
> `MeasureTheory.Integrable (fun h => ‖h‖ * f h) volume`. Then there exists a sequence
> `g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ` such that
> 1. every `g K` is a pdf (`IsPdf (g K)`);
> 2. every `g K` is a **finite Gaussian mixture**: there are `m : ℕ`, weights
>    `w : Fin m → ℝ` with `w i ≥ 0`, `∑ w i = 1`, and locations
>    `μ : Fin m → Fin n → ℝ` such that
>    `g K = fun x => ∑ i, w i • multivariateGaussianPDF n (μ i) (σ_K² • 1) _ x`,
>    i.e. each component is a Gaussian with common isotropic covariance `σ_K² I`
>    (`σ_K > 0`, and `σ_K → 0`; the locations are bounded uniformly in `K`);
> 3. `g` converges to `f` in weighted L¹:
>    `∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀,
>      ∫⁻ h, ENNReal.ofReal ((1 + ‖h‖) * |f h - g K h|) ∂volume < ENNReal.ofReal ε`.

The convergence mode in (3) is **exactly** the hypothesis `hw` of `cme_uniform_balls_R`
(same `∫⁻`/`ofReal` phrasing), so the composition

    GMM-density theorem  +  cme_uniform_balls_R  ⟹
      for every pdf prior `f` with finite first moment there is a *GMM* prior sequence
      `fhK` such that the CMEs `cmeR … (fhK K)` converge to `cmeR … fh` locally uniformly
      (uniformly on every closed ball in `ℝ^m`).

should be stated as a final corollary.

Corollary target (immediate, Phase 0): if the true prior `fh` is itself a finite GMM,
then `cme_uniform_balls_R` applies **today**, with the constant sequence
`fhK K = fh` (see Phase 0 below).

## Motivation

* `cme_uniform_balls_R` is the fully general-`A` convergence theorem of the
  formalization: for the model `y = A h + n` with an *arbitrary* `m × n` observation
  matrix `A` (no invertibility, no rank condition), priors `f^(K)` converging to `f`
  in weighted L¹ give locally uniform convergence of the conditional mean estimates
  `ĥ^(K) → ĥ`.
* Its only "soft spot" (user's words): it is not yet clear that any nontrivial sequence
  of priors satisfies `hw` — in particular, that **Gaussian mixture models** do. GMMs
  are the priors used by the estimator of Koller–Fesl–Turan–Utschick 2022 (IEEE TSP,
  cited in `README.md`), which is the motivating application of the whole
  formalization.
* Folklore ("mixtures approximate any density") is true but in the *wrong mode*:
  the literature gives L¹ or uniform-on-compacta convergence, not weighted L¹. This
  plan documents why that gap is real (see "Why the paper's Theorem 5 is not enough")
  and how to close it.

## What is already available

### In the repository (`Main.lean`)

* `IsPdf` (line ~141): the pdf predicate — pointwise nonnegativity and total mass 1
  w.r.t. `volume` on `EuclideanSpace ℝ (Fin n)`.
* `integral_multivariateGaussianPDF_one` (line ~778): the multivariate Gaussian pdf
  integrates to 1. **Key reusable asset**: a finite GMM `∑ i, w i • pdf(μ_i, Σ)` is a
  pdf by finite-sum interchange plus this lemma, with no further probability theory.
* `multivariateGaussianPDF`, `noiseDensR`, `fyPDFR`, `cmeR`: the model definitions.
* `cme_uniform_balls_R` (line ~4935): the consumer of the hypothesis `hw`; public.
* The phrasing convention for `hw`: the integral is the `∫⁻` (Lebesgue integral into
  `ℝ≥0∞`) of `ENNReal.ofReal ((1 + ‖h‖) * |f h - g K h|)`, compared against
  `ENNReal.ofReal ε`. This is deliberately non-vacuous: the real Bochner integral of a
  non-integrable nonnegative function vanishes in Mathlib, so a real-integral hypothesis
  would be free. Any new statement must reuse this phrasing verbatim.

### In Mathlib (v4.35.0)

* Convolution on `EuclideanSpace`/normed groups and its L^p theory; approximate-identity
  ("mollifier") results: `f ∈ L^p`, `1 ≤ p < ∞`, `∫ g = 1` imply `f ⋆ g t → f` in L^p
  as `t → 0`. (Plain, unweighted.)
* Continuity of translation of a *fixed* `L^p` function (`s ↦ g(· + s)` continuous into
  `L^p`), and the elementary Gaussian facts already used throughout `Main.lean`
  (`Real.exp`, `CFC.sqrt`, positive-definiteness manipulations).
* `MeasureTheory.Integrable` domination/monotone machinery used pervasively in
  `Main.lean` (`Integrable.mono'`, `integral_mono_of_nonneg`, `lintegral` API).

### In the literature (context, not formalized)

* Nguyen–Nguyen–Chamroukhi–McLachlan 2020,
  *"Approximation by finite mixtures of continuous density functions that vanish at
  infinity"* (the PDF/TXT in the repository). Its mixture class `M_g^m` is
  `h(x) = ∑_{i≤m} c_i σ_i^{-n} g((x − μ_i)/σ_i)` with arbitrary weights `c ∈ Δ^{m-1}`;
  with a Gaussian kernel `g` this is exactly a GMM family. Its Theorem 5(a): for any
  `f ∈ C₀` there is a sequence in `M_g^m` with `‖f − h_m‖_{L¹} → 0`.
* Bacharoglau 2010 and related work give *quantitative rates* for bounded `f`
  (sup-norm O(K^{-2/d}) type). Rates are out of scope here (see Non-goals).

## Why the paper's Theorem 5(a) is not enough (documented gap)

Two gaps separate Theorem 5(a) from the hypothesis `hw`:

1. **Class mismatch.** Theorem 5(a) assumes `f ∈ C₀` (continuous and vanishing at
   infinity). `cme_uniform_balls_R` assumes only `IsPdf f` + finite first moment
   (`hfmom`) — and that is the right class, because finite first moment is what makes
   the posterior mean well-defined. Note `C₀` pdfs may have infinite first moment (then
   `cme_uniform_balls_R` does not even apply), and pdfs with finite first moment need
   not be continuous. Neither class contains the other.

2. **Mode-of-convergence gap (genuine trap).** Weighted-L¹ convergence does **not**
   follow from L¹ convergence plus bounded moments of the approximants.
   Counterexample: `f^(K) = (1 − δ_K) f + δ_K q_K` with `q_K` a smooth bump of mass 1
   near `‖x‖ ≈ K` and `δ_K = 1/K`. Then
   `‖f − f^(K)‖₁ ≤ 2 δ_K → 0`, the first moments `∫ ‖x‖ f^(K)` stay uniformly bounded,
   but `∫ (1 + ‖x‖) |f − f^(K)| ≥ δ_K (1 + K) ≈ 1 ↛ 0`.
   Consequently one cannot bridge Theorem 5(a) to `hw` by adding a moment side-condition
   on the approximants; the weighted statement needs its own proof. (This same
   counterexample also shows that *global* uniform convergence of the CMEs is false
   under `hw`-type hypotheses — documented in the `main_theorem`/README discussions.)

Moral support is still real: Theorem 5(a) says the *statement* is morally true, and our
construction below yields a stronger result (larger class, stronger mode) by elementary
means, without needing `f` continuous or vanishing.

## Proof strategy

Write `w(x) = 1 + ‖x‖`, `φ_σ` = the Gaussian pdf with mean `0` and covariance `σ² I_n`
(i.e. `multivariateGaussianPDF n 0 (σ² • 1) _`; positive definite for `σ > 0`;
`∫ φ_σ = 1` by `integral_multivariateGaussianPDF_one`). Fix `f` a pdf with
`∫ w · f < ∞`. The construction is a two-step smoothing–quantization argument; no
continuity or decay of `f` is used.

1. **Smoothing (weighted).** For `f ∈ L¹` with `∫ ‖x‖ f < ∞`:
   `∫ w · |f − f ⋆ φ_σ| → 0` as `σ → 0`.
   Method: truncate `f` at radius `R` (small weighted tail, since `∫ w f < ∞`), use the
   plain-L¹ mollifier convergence on the truncated piece (Mathlib), and control the
   weighted error on the annulus by `∫ (1 + ‖x‖) |f ⋆ φ_σ|`-type bounds using
   `∫ ‖x‖ (f ⋆ φ_σ) ≤ ∫ ‖x‖ f + ∫ ‖y‖ φ_σ(y) dy =: ∫ ‖x‖ f + c σ`
   (subadditivity of the first moment under convolution).

2. **Quantization (lattice cells).** For lattice spacing `δ ≪ σ`, define the index map
   `latticeIdx δ(t) = ⌊t/δ⌋` (`Fin n → ℤ`, componentwise) and the rounding map
   `Q_δ(t) = δ • ⌊t/δ⌋` (componentwise; a measurable, piecewise-constant map with
   `‖Q_δ(t) − t‖ ≤ δ√n`). For an integer box half-width `N = ⌈R/δ⌉₊`, let
   `S(N) := Fintype.piFinset (fun _ : Fin n => Finset.Ico (-(N : ℤ)) (N : ℤ))` be the
   `Finset` of integer grid vectors in `[-N, N)^n`, with cells
   `cell(δ, k) = {t | latticeIdx δ t = k}`, centers `x_k = δ • k`, and weights
   `W_k = ∫_{cell(δ, k)} f`. Define the covered box as the disjoint union
   `box(δ, N) := ⋃_{k ∈ S(N)} cell(δ, k) = [-Nδ, Nδ)^n ⊇ [-R, R]^n`
   (defining the box as the union of the `Ico` cells avoids upper-boundary `t_i = R`
   off-by-one issues and makes pairwise disjointness and `integral_biUnion_finset`
   immediate). Define
   `f_K(x) = ∑_{k ∈ S(N)} W_k φ_σ(x − x_k) + (1 − c) φ_σ(x)` where `c = ∫_{box} f` — a
   **finite** mixture, and an integral identity
   `∑_{k ∈ S(N)} W_k φ_σ(x − x_k) = ∫_{box} f(t) φ_σ(x − Q_δ(t)) dt` holds
   (finite sum ↔ integral interchange via `integral_biUnion_finset`).
   Then, writing `s(t) := t − Q_δ(t)` (`‖s(t)‖ ≤ δ√n`) and substituting `y = x − t`
   in the inner integral on `box`,
   `‖f_K − f ⋆ φ_σ‖_{L¹(w)}
      ≤ ∫_{box} f(t) · ∫ w(x) |φ_σ(x − Q_δ(t)) − φ_σ(x − t)| dx dt
        + (1 − c) ∫ w(x) φ_σ(x) dx + ∫_{box^c} f(t) ∫ w(x) φ_σ(x − t) dx dt
      ≤ ∫_{box} f(t) · [ weightedModulus n φ_σ (Q_δ t − t) + ‖t‖ · L₁(s(t)/σ) ] dt
        + (1 + σM₁) · [ (1 − c) + ∫_{box^c} w f ]`,
   where `weightedModulus n g u := ∫ w(x) |g(x − u) − g x| dx` (the code's definition;
   `weightedModulus n φ_σ (Q_δ t − t) = ∫ w(y) |φ_σ(y+s(t)) − φ_σ(y)| dy`) and
   `L₁(v) := ∫ |φ_1(y+v) − φ_1(y)| dy ≤ weightedModulus n φ_1 (−v)`; the steps use
   `w(y+t) ≤ w(y) + ‖t‖`, `∫ |φ_σ(y+s) − φ_σ(y)| dy = L₁(s/σ)` and the evenness of `φ_σ`.
   **[corrected — the previous display jumped straight to
   `sup_{‖s‖ ≤ δ√n} ∫ w(x) |φ_σ(x + s) − φ_σ(x)| dx`, dropping the weight shift
   `w(y+t) → w(y)`; and the loss term must NOT be bounded by pulling `‖t‖ ≤ R√n` out
   (an `R`-dependent factor would destroy the `R_K → ∞` diagonal) — integrated against
   `f` it is `∫_{box} ‖t‖ f(t) dt ≤ M_f := ∫ ‖t‖ f`, independent of `R`. Moreover, in Lean
   we avoid `sSup` over uncountable balls altogether by unpacking `Metric.tendsto_nhds`
   on `weightedModulus n φ_1` to get a uniform pointwise `< η` bound whenever
   `δ√n/σ < r`.]**
   Both terms → 0 as `σ → 0` and `δ/σ → 0` by the **scaled-modulus** estimate of
   Phase 2 Step 3 (`weightedModulus_gaussian_scale`). Continuity of translation in
   weighted L¹ for a *fixed* kernel is legitimate for each fixed `σ`
   (`∫ w φ_σ < ∞`, Gaussians have moments of all orders) but is **not uniform in `σ`**,
   so it cannot be used along the diagonal — the point made in the Phase 2 design
   decisions. Note the kernel bandwidth `σ` and the cell size `δ` play *independent*
   roles: both `σ → 0` and `δ/σ → 0` are required (along the diagonal
   `δ_K/σ_K = σ_K`, so a single condition); no further bandwidth–cell-size matching
   (that is only needed for sup-norm approximation, which we do not attempt).

3. **Mixtures are pdfs.** `∫ f_K = ∑_j w_j = ∫_{box} f =: c`, which is `< 1` in
   general — so the literal `f_K` is NOT a pdf. Fix (settled design decision, see the
   Phase 2 section): add a **residual weight `1 − c` at the origin lattice point**
   (`0` is a lattice point since `Q_δ 0 = 0`); then the mass is
   `∑_j w_j + (1 − ∑_j w_j) = 1` and nonnegativity needs only `c ≤ 1`. The mass
   computation is a finite sum of `∫ φ_σ = 1` terms (via
   `integral_multivariateGaussianPDF_one`).

4. **Tails.** Cover only a box `B_R` with `∫_{‖x‖ > R} w f` small (possible since
   `∫ w f < ∞`). Outside the covered region, `f_K`'s mass comes only from boundary
   cells and Gaussian leakage `m_σ = ∫ ‖y‖ φ_σ(y) dy`, both controlled by the choice
   ordering: pick `R` (tail of `f`), then `σ` (smoothing + leakage), then `δ ≪ σ`
   (translation continuity), then let `K → ∞` along a diagonal enumeration of the
   triples `(R, σ, δ)`. Every error term is `< ε/3` in this three-piece sketch
   (smoothing / quantization / tails); the execution-level assembly of Phase 2 Step 6
   folds the tails into the quantization budget and uses a two-term triangle with
   `< ε/2` per term.

5. **Assembly.** Combine 1–4 into the target theorem, then compose with
   `cme_uniform_balls_R` for the CME corollary.

Formalization-relevant remark: the mixture produced has **common covariance `σ² I`**
across components and uniformly bounded locations — a (large but honest) subset of
GMMs. General component covariances are not needed.

## Phases

### Phase 0 — GMM priors, today (~40 lines) — **DONE**

**Status: implemented in `ApproximationByGMM.lean` (verified; axiom-audited in
`AxiomCheck.lean`).** If the true prior `f` is itself a finite Gaussian mixture, take the
*constant* sequence `fhK K = f`. Then `|f − f^(K)| = 0` and `hw` holds trivially;
`f^(K)` are pdfs via the mixture-mass lemma. Composed with `cme_uniform_balls_R`.

Deliverables (as implemented):
* `gmmPDF n k Cov hC w μ`: the mixture definition; `IsMixtureWeights w`: the weight
  predicate (nonnegative, summing to one).
* `isPdf_gmmPDF`: a finite Gaussian mixture is an `IsPdf` (mass via
  `integral_multivariateGaussianPDF_one` + finite-sum interchange).
* `integrable_norm_mul_gmmPDF`: the `hfmom` hypothesis of `cme_uniform_balls_R` is
  **automatic** for GMM priors (any weights/locations): the centered first moment comes
  from `integral_gaussian_bounded` (A = 1, y = 0) plus evenness of the centered Gaussian,
  then translation (`h ↦ toLp 2 (h + c)` preserves integrability) and the domination
  `‖h‖ ≤ ‖h − m‖ + ‖m‖`.
* `cme_convergence_of_gmm_prior`: the composed corollary — for a GMM prior and
  **any** sequence `fhK` converging to it in the weighted-L¹ sense, the CMEs converge
  locally uniformly, for arbitrary `m, n, A`. (Note: the sequence must be allowed to be
  arbitrary — with the constant sequence on both sides the conclusion would be
  degenerate, the difference of the CMEs being identically zero. The added value over
  `cme_uniform_balls_R` is precisely the automatic discharge of `IsPdf` and `hfmom` for
  the GMM prior.)
* Supporting lemmas: `multivariateGaussianPDF_pos`, `integral_gaussianPDF`,
  `isPdf_multivariateGaussianPDF`, `multivariateGaussianPDF_sub_mean` (pdf(m)(x) =
  pdf(0)(x + (−m))), `multivariateGaussianPDF_neg`, `integral_toLp_trans_right`,
  `lintegral_toLp_trans_right`, `integrable_toLp_shift`.

Formalization notes discovered during Phase 0 (relevant for Phases 1–2):
* In the module system, **public defs are opaque to importing modules** unless marked
  `@[expose]`. `IsPdf` and `multivariateGaussianPDF` are now `@[expose]`d in `Main.lean`
  (needed for unfolding/anonymous-constructor use downstream); a public `theorem`
  proven by bare `rfl` additionally requires every definition it unfolds to be exposed.
* `Integrable` is `AEStronglyMeasurable ∧ HasFiniteIntegral` (`.1`/`.2`);
  `Integrable.congr`'s pointwise hypothesis is oriented `old = new`; for transporting
  integrability across the translation `h ↦ toLp 2 (h + c)` use
  `Measurable.enorm` + `lintegral_toLp_trans_right` (see `integrable_toLp_shift`).

Limitation: the sequence is constant, so it only helps when the true prior *is* a GMM.
For general `f`, Phases 1/2 are needed.

### Phase 1 — continuum-mixture sequence (~150–250 lines) — **DONE**

**Status (final, this round): Phase 1 is complete.** The smoothed-prior sequence
`smoothedPriorSeq n f C hC K = gaussSmoothed … (1/(K+1))` satisfies the `hw` hypothesis of
`cme_uniform_balls_R`, and the composed corollary `cme_uniform_balls_smoothed_prior` is proven.
Everything below is historical progress narrative.

**Final round (this session) — what was proven:**
1. `integrable_joint_smooth_prior` (ψ-first joint, the missing piece from last round):
   the `hkey` product-merge chain needed THREE `← ENNReal.ofReal_mul` rewrites in
   innermost-first order — but with the caveat that the hypothesis of each
   `ofReal_mul` instance PINS its first factor (`?a`), so the rewrite only fires at
   occurrences whose first ofReal-factor matches that hypothesis's argument; the LHS
   merge (`0 ≤ 1+‖x‖`) must come LAST. After the merges, the real inequality needs
   `rw [← mul_assoc]` (the RHS is right-nested; forward `mul_assoc` fails) and then
   `mul_le_mul_of_nonneg_right hle hfxnn`. The outer chain must mirror the original
   theorem: `refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner) ?_` with
   `hinner` as a NAMED ∀-term (the two-bullet `le_trans` version leaves
   `lt_of_le_of_lt`'s middle argument an unsolved metavariable at elaboration time),
   then one const-pull bullet with the meas hypothesis as a flat-lambda `have hpullmeas`
   (inline `.mul` meas-args elaborate to non-beta-reduced product-of-lambdas and the
   rewrite fails to match).
2. `measurable_gaussSmoothed`: `fun_prop` for the joint needs the
   `Measurable (mollifier …)` hypothesis in context (`have hψmeas := measurable_mollifier …`);
   the result via `(hGxmeas.stronglyMeasurable.integral_prod_right').measurable`.
3. `smoothedPriorSeq`: `fun K => gaussSmoothed … (1/(K+1))` — use the shape
   `(1:ℝ)/((K:ℝ) + 1)` everywhere (matches `tendsto_one_div_add_atTop_nhds_zero_nat`);
   `0 <` by `div_pos one_pos (by positivity)`.
4. `integrable_weighted_abs_diff_gaussSmoothed`:
   `Integrable ((1+‖x‖) · |f − gaussSmoothed|)` by `mono'` against
   `(1+‖x‖)·f + (1+‖x‖)·gaussSmoothed`. Key: the second dominating piece is the
   `x`-marginal of the ψ-first joint —
   `(integrable_joint_smooth_prior …).integral_prod_right` gives exactly
   `∫ u, ψ(u)·((1+‖x‖)·f(x−u)) du` integrable, and the pointwise bridge
   `(1+‖x‖)·gaussSmoothed x = ∫ u, ψ(u)·((1+‖x‖)·f(x−u)) du` needs NO slice
   integrability because `MeasureTheory.integral_const_mul` is UNCONDITIONAL for
   RCLike (`∫ r·f = r·∫f`, no hypothesis); the congr is a typed `have hsplit`
   closed by `exact integral_congr_ae` (NEVER `rw [integral_congr_ae …]` — the
   rewrite's RHS-function stays a metavar and the inner `by ring` fails);
   `Integrable.mono'`'s bound is `‖f x‖ ≤ g x` (RHS UN-normed); `Measurable.abs`
   does not exist in this Mathlib — let `fun_prop` build the abs-measurability
   (it needs `Measurable (gaussSmoothed …)` in context).
5. `hw_smoothedPriorSeq`: the ∫⁻-form `hw` — apply `weighted_smoothing_tendsto_seq`
   along `σ K = 1/(K+1)` (`hσ0 := tendsto_one_div_add_atTop_nhds_zero_nat`), then per-K
   `ofReal_integral_eq_lintegral_ofReal (hKint K) (hwnn K)` bridges `ofReal (∫ w K) =
   ∫⁻ ofReal (w K)`, and the ε-threshold comes from
   `Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hconv ε hε)` + `Real.dist_eq` +
   `abs_of_nonneg (∫ w K ≥ 0)`; close with `(ENNReal.ofReal_lt_ofReal_iff hε).mpr`
   (there is NO unconditional `ENNReal.ofReal_lt_ofReal` — only the
   `ofReal_lt_ofReal_iff (h : 0 < q)` iff-forms).
6. `cme_uniform_balls_smoothed_prior`: `cme_uniform_balls_R m n S hS A f hpdf hfmom
   (smoothedPriorSeq n f C hC) (fun K => isPdf_gaussSmoothed … (1/(K+1)) …)
   (hw_smoothedPriorSeq …) r hr` — the `IsPdf`-sequence and `hw` arguments typecheck
   against the `smoothedPriorSeq`-forms by delta + proof irrelevance.
7. `AxiomCheck.lean` extended to 12 audits — all depend only on
   `[propext, Classical.choice, Quot.sound]`. Full build green (3227 jobs), zero `sorry`.

**Status (current session):** the mollifier infrastructure is implemented and verified in
`ApproximationByGMM.lean`:
* `mollifier n C hC σ _hσ` = `σ^{-n} · φ_C(·/σ)` (the density of `N(0, σ² C)`),
  `gaussSmoothed n f C hC σ _hσ` = `x ↦ ∫ ψ_σ(u) f (x − u) du` (the continuum mixture);
* `integral_mollifier`: `∫ ψ_σ = 1` (change of variables via `integral_subst`);
* `integral_mollifier_mul`: **the DCT representation** `∫ ψ_σ(u) H u du =
  ∫ φ_C(v) H (σ v) dv` — the transport that powers the σ → 0 limit;
* `isPdf_multivariateGaussianPDF`, `multivariateGaussianPDF_pos`,
  `integral_gaussianPDF`, `multivariateGaussianPDF_sub_mean` (pdf(m)(x) = pdf(0)(x+(−m))),
  `multivariateGaussianPDF_neg`;
* translation infrastructure: `integral_toLp_trans_right`, `lintegral_toLp_trans_right`,
  `integrable_toLp_shift`, `integrable_toLp_sub` (integrability under `h ↦ toLp(c − h)`,
  via the reflection `map_linearMap_addHaar_eq_smul_addHaar` + translation composition).

**DONE in later rounds (all compiling, full build green, AxiomCheck clean):**
1. `setIntegral_tail_tendsto`: for nonnegative integrable `g`,
   `Tendsto (fun k => ∫ x in {y | (k:ℝ) < ‖y‖}, g x ∂volume) atTop (𝓝 0)` — sequential DCT on
   the exhaustion by complements of closed balls (via
   `tendsto_integral_of_dominated_convergence`, bound `= g`, pointwise limit via
   `exists_nat_gt ‖x‖` + `Filter.eventually_ge_atTop`).
2. `measurableSet_norm_gt`: the outside of a closed ball is measurable
   (`Metric.isClosed_closedBall.measurableSet.compl` after an `ext`+`simp` set-equality).
3. `weighted_modulus_tendsto_seq` (the `(T)`-lemma, ~250 lines): for continuous pdf `f` with
   `hfmom : Integrable (‖·‖ * f)` and `u k → 0`, the weighted translation modulus
   `∫ (1+‖x‖) * |f (x − u k) − f x| ∂volume → 0`. Proof structure:
   - fix `k₀` with `‖u (k + k₀)‖ < 1` for all `k`, and prove the claim for the shifted
     sequence `v k = u (k + k₀)` (uniform smallness makes the DCT bound uniform in `k`);
     convert back with `Filter.tendsto_add_atTop_iff_nat`;
   - `htri`: `‖x‖ ≤ ‖toLp 2 (x − v k)‖ + ‖v k‖` (via `WithLp.ofLp_injective` + `norm_add_le`);
   - `hbnd`: `(1+‖x‖) * |f (x − u)| ≤ (1+‖u‖) * (1+‖x−u‖) * f (x−u)` (nlinarith, no
     smallness needed — used for all integrability transports);
   - `hshiftint`: integrability of the shifted weighted `f`,
     `(1+‖u‖) * ((1+‖x−u‖) * f (x−u))`, via `integrable_toLp_shift` +
     `hwfint.const_mul` + `Integrable.congr'` (the `show`-with-norms form for the a.e.
     equality; note `Integrable.add`, `Integrable.mono`, `abs_sub`, and that
     `simp only [Real.norm_eq_abs]` must be paired with `Pi.add_apply` when the goal has
     function-sums);
   - `hintg`: integrability of the full modulus integrand (mono against
     `hshiftint k + hwfint`);
   - the bound `B` for `|f|` on the ball of radius `(K₁:ℝ)+2` via
     `IsCompact.exists_bound_of_continuousOn` (NOT `exists_isMaxOn`: the `IsMaxOn`
     ascription triggered a `whnf`/`isDefEq` timeout — the bounded-form
     `∀ z, ‖z‖ ≤ r → |f z| ≤ B` avoids the expensive `closedBall`-membership defeq);
   - `hmeasCore` via an `ext`+`simp` set-equality `{y | ‖y‖ ≤ r} = Metric.closedBall 0 r`
     (direct `Metric.isClosed_closedBall.measurableSet` ascription is a defeq bomb for the
     same reason);
   - the core DCT with the indicator-constant bound
     `{y | ‖y‖ ≤ R'}.indicator (fun _ => (1+R')*(2*B))` — a CONSTANT function is NOT
     integrable on the infinite measure `volume`; `integrable_const` needs
     `[IsFiniteMeasure]`. Integrability of the indicator-constant via
     `hasFiniteIntegral_iff_enorm` + `lintegral_indicator_const` +
     `measure_closedBall_lt_top`;
   - the pointwise limit via the single-continuous-map composition
     `(hG.tendsto 0).comp hu'` + typed `Filter.Tendsto.congr` + `simpa`;
   - `T1 ≤ 2δ`: the tail of `w|f(·−u)|` transported by the pure translation
     `integral_toLp_trans_right` with `c = −u` (the threshold-shift trick: the indicator
     moves INTO the transported function, so no set-transport is needed);
     `ψ₂` = the tail indicator of `w*f` at threshold `K₁`;
   - `T2 < δ`: monotone in the threshold (`R' = K₁+1 > K₁`);
   - assembly: pointwise `g_k ≤ Aint + T1int + T2int`, `integral_mono`, `integral_add`,
     budgets `δ + 2δ + δ = 4δ = ε`.
   
**Gotchas catalogued this round:** `rw [sub_eq_add_neg]` FAILS under `∫`-binders (the bound
variable coercion); use `simp only [sub_eq_add_neg]` or state transport lemmas in closed
form and apply them (alpha-conversion is handled). `rw [Set.indicator_of_mem hmem]` fails
when the membership hypothesis is in ≤/¬-form; use `simp only [Set.indicator_of_mem hmem]`
or construct the membership with `simpa only [Set.mem_setOf_eq] using hmem`. `calc` proofs
with the `:=`-witness on its own line can swallow the following tactics (parse drift) —
prefer `refine le_trans (steps) ?_` chains or `have`-ladders. Rewriting `∫`-terms that
differ by beta/instance-forms fails: state `have`-equations with the EXACT syntactic shape
of the goal (obtained by `have h := lemma...` then rewriting `at h`), or use
`integral_add'` (the `(f+g) a`-form) rather than `integral_add` when the goal came from
`integral_mono` over an `.add`-chain. `show T from e` may fail where `have h : T := e`
works. `(0 ≤ f)`-hypotheses are function-≤; `integral_nonneg hwnonneg` works directly but
`fun x => mul_nonneg ...` inline may need a separate typed `have`.

**DONE in the latest round (all compiling; `isPdf_gaussSmoothed` has ONE `sorry` for its
mass-component):**
1. `integral_shift_neg` / `lintegral_shift_neg`: translation invariance in the `y − c` form
   (the `rw [sub_eq_add_neg]`-under-binders trap avoided by the `funext`-rewrite of the
   whole function, applied to free variables only).
2. `lintegral_mollifier`: `∫⁻ ofReal (ψ_σ) = 1` — the ∫⁻ scaling transport:
   pointwise `ofReal`-split via a typed `have hpt` + `lintegral_congr_ae` (the ∫⁻ keeps the
   opaque mollifier), then `lintegral_const_mul` + `lintegral_map` (with the composed
   `hFmeas'` for the `(T a)`-form integrand — pass the UNcomposed map-form function, never
   the composition) + `map_linearMap_addHaar_eq_smul_addHaar` + `lintegral_smul_measure` +
   `ofReal_integral_eq_lintegral_ofReal` (note: its statement is
   `ofReal (∫ f) = ∫⁻ ofReal (f a)`, so the goal `∫⁻ ofReal (f) = 1` needs the ← direction)
   + `inv_pow`/`mul_inv_cancel₀`/`abs_of_pos` endgame. Beware: after `hφlint` rewrites the
   ∫⁻ into the bare `1`, the `1` is at ℝ≥0∞, so `mul_one` must come before
   `mul_comm`/`ofReal_mul`, and there is no `ofReal 1` in the goal at that point (the
   `ofReal_one` must only appear at the very end).
3. `isPdf_gaussSmoothed` nonnegativity: stated as a typed `have hgnonneg : ∀ x, 0 ≤ ∫ ...`
   (an inline `fun x => integral_nonneg ...` under a `refine ⟨?_, ?_⟩` gets stuck
   instance synthesis); `exact hgnonneg` closes the function-≤ goal directly.

**Latest round's progress (one `sorry` remains, in the `isPdf_gaussSmoothed` mass):**
1. `isPdf_gaussSmoothed` nonnegativity: DONE (the typed `have hgnonneg` pattern).
2. The Fubini mass-chain for `isPdf_gaussSmoothed`: the hflint (`∫⁻ ‖f‖ₑ = 1` via
   `Real.enorm_eq_ofReal` + `ofReal_integral_eq_lintegral_ofReal` + `hpdf.2`), hshift
   (∫⁻ shift-invariance of ‖f‖ₑ via `lintegral_shift_neg`), hΦmeas, and the joint
   integrability hΦint are DONE up to the last two rewrites: the `hinner` transport
   (`lintegral_const_mul` with the `hmeas'` Measurable supplied through a `heq := rfl`
   function-composition rewrite — the `hfm.enorm.comp` form produces `∘`-terms that do
   NOT syntactically match `∫⁻`-integrands) is in place; what remains is (a) rewriting
   the inner ∫⁻ integrand from the ‖f‖ₑ-form to the `ofReal (f …)`-form (the hinner's
   stated form has `‖f (… )‖ₑ` while the goal after the hpt-congr has
   `ENNReal.ofReal (f …)` — restate hinner in the ofReal form via a second hpt) and
   (b) closing the outer ∫⁻ with `lintegral_mollifier` (the goal after the hinner-simp
   is `∫⁻ a, ofReal (mollifier … a)`, which already matches `lintegral_mollifier`'s
   statement — no congr needed). Note the goal's ∫⁻ after `lintegral_prod_le` is the
   CURRIED two-binder form `∫⁻ a, ∫⁻ b, …`, so the hpt congr must be stated for the
   inner integrand of that curried form.
3. The remaining mass-chain `∫ gaussSmoothed = 1` via `integral_prod` is untouched.

**Latest round: `hΦint` (joint integrability) is now FULLY PROVEN** — the correct
Tonelli orientation (pair's FIRST coordinate carries ψ, so `lintegral_prod_le`'s outer ∫⁻
pairs with ψ's variable and the inner ∫⁻ transports through `hshift`) plus the final
steps: the hinner transport (with the `‖f‖ₑ`-form `hmeas'` supplied via the `heq := rfl`
composition trick and the hfpt congr flipping the `ofReal (f …)` to the `‖f‖ₑ` form),
then the outer ∫⁻ congr straight to `lintegral_mollifier` and `ENNReal.one_lt_top`.
The only `sorry` left in Phase 1 is the mass chain `∫ gaussSmoothed = 1`
(`integral_prod` with hΦint + the iterated-∫ inner transport `∫_x f(x−u) = 1` via
`integral_shift_neg` + `integral_mollifier`), and then the smoothing theorem itself
(`weighted_smoothing_tendsto_seq`: same Tonelli+DCT architecture as the `(T)`-lemma with
the `hΦint`-style joint integrability for the ψ-weighted integrand and the outer DCT
with dominator `φ_C(v)·2(1+M_f)`, closed via `weighted_modulus_tendsto_seq`), the
hw-existence theorem (`σ_K = 1/(K+1)`), and the corollary via `cme_uniform_balls_R`.

**Latest round: the Fubini mass-chain for `isPdf_gaussSmoothed` is nearly complete.**
New proven steps: `hAint'` (the gA-form joint integrability via
`measurePreserving_swap.integrable_comp .mpr hΦint` — note the full name
`MeasureTheory.Measure.measurePreserving_swap`), `hshiftmass` (∫-level shift invariance
via `integral_shift_neg`), and the three-step ∫-rw chain through
`integral_prod` (← form, `hAint'`) + `integral_prod_swap` (the ← form: the
`rw [integral_prod_swap (f := …)]` FORWARD direction fails to match when the goal's
integrand has already been beta-reduced — the `←` direction matches the unreduced
`z.swap` pattern) landing on `∫ z, gA z.swap ∂(vol.prod vol)`.

**Remaining for the mass (next round):**
1. The swapped-pair congr `gA z.swap = Φ z` (a `Prod.swap`-projection simp; the
   `integral_congr_ae` attempt with an inner `sorry` closed the goal vacuously — state
   the congr as a typed `have` with both sides explicit).
2. `integral_prod` with `f := Φ` (hΦint), giving `∫_u ∫_x ψ(u) f(x−u) dx du`.
3. The inner ∫_x transport: `integral_const_mul` + `hshiftmass` + `mul_one`, then
   `integral_mollifier`.

**Latest round: the Fubini mass-chain orientation fully diagnosed.** The three-step
∫-rw chain now lands on the single-∫-over-product form
`∫ z, gA z.swap ∂(vol.prod vol)` (after `integral_prod` ← with hAint', then
`integral_prod_swap` ← — the ← direction is REQUIRED: the forward direction fails to
match beta-reduced integrands). Key finding: after the `integral_prod_swap`, the
iterated form via `integral_prod` re-iterates with the ψ-coordinate as the INNER
variable (wrong orientation), so the transport must be stated directly on the
single-∫-over-product form with a typed `hinner` in the exact `z.swap`-shapes
(the `integral_const_mul` with a `_` metavariable for the ψ-term also fails to
elaborate/match under the goal's binder structure). The remaining steps for the mass:
(a) a typed `hinner : ∀ z, mollifier … z.swap.2 * f (toLp(z.swap.1 − z.swap.2))
= mollifier … z.1 * 1` in the exact goal shapes (using `hshiftmass` for the
`f (toLp(z.swap.1 − z.swap.2)) = 1` part), (b) `simp only [hinner]`, (c)
`integral_mollifier`. Then the smoothing theorem `weighted_smoothing_tendsto_seq` and
the hw-existence theorem + corollary.

**Remaining (next round):**
1. `weighted_modulus_tendsto` (the `(T)`-lemma): for continuous `f` with finite first
   moment, `G(u) = ∫ (1+‖x‖) |f (x−u) − f x| dx → 0` as `u → 0`. Proof: core/tail split —
   the tail by the moment tails of `f` (translation-invariance of the weighted mass), the
   core by uniform continuity of `f` on the compact ball
   (`IsCompact.uniformContinuousOn_of_continuous`) — plain DCT on the integrand
   `w(x)·|f (x−u_k) − f x|` with the translation-invariant domination
   `∫ w |f(·−u)| = ∫ w |f| = 1 + M_f`.
2. The tail lemma: `∀ ε > 0, ∃ R₀, ∀ R ≥ R₀, ∫_{‖y‖ > R−1} (2+‖y‖)·|f y| ≤ ε`
   (sequential DCT on the exhaustion + contradiction wrapper).
3. `weighted_smoothing_tendsto`: the chain
   `∫ w |f − f⋆ψ_σ| ≤ ∫ ψ_σ(u) G(u) du = ∫ φ_C(v) G(σ v) dv → 0`
   — the first inequality by the pointwise identity
   `f⋆ψ_σ(x) − f(x) = ∫ ψ_σ(u)(f (x−u) − f x) du` (from `∫ ψ_σ = 1`) + Tonelli swap
   (joint integrability via the `∫⁻`-route, following the
   `lintegral_enorm_noiseDens_mul` pattern), the limit by sequential DCT with the
   σ-uniform domination `φ_C(v) · 2(1+M_f)`.
4. `isPdf_gaussSmoothed` (mass via Tonelli swap + translation), then the Phase-1
   hw-existence theorem (with `σ_K = 1/(K+1)`) and the composed corollary
   (via `cme_uniform_balls_R`).

**Mathematical note:** Phase 1 requires `f` **continuous** (this is what makes `(T)` a
plain dominated convergence); the class matches the paper's `C₀` setting. The general
(integrable-only) case needs L¹-translation-continuity for arbitrary integrable `f` —
Mathlib's `Lp.instContinuousSMulDomMulAct` (in
`Mathlib/MeasureTheory/Function/LpSpace/DomAct/Continuous.lean`, for Haar-measured
finite-dimensional spaces) is the identified route — deferred. 

For general `f` (pdf + finite first moment), the sequence `f^(K) = f ⋆ φ_{1/K}`
("continuum mixtures": each `f^(K)` is a convolution of `f` with a single Gaussian, not
a finite mixture) satisfies `hw`.

Deliverables:
* `weighted_translation_cont`: continuity of translation in weighted L¹ for a fixed
  integrable kernel with finite first moment.
* `weighted_smoothing`: `∫ w |f − f ⋆ φ_σ| → 0` for `f` with finite first moment.
* The Phase 1 statement `hw` for `f^(K) = f ⋆ φ_{1/K}`.
* These lemmas are reused verbatim by Phase 2.

Limitation: `f ⋆ φ_σ` is an integral against a continuum of components — a valid prior
for the theory (the CME integrals still make sense) but not an implementable finite
mixture.

### Phase 2 — finite GMMs (the target; ~500–800 lines) — **Step 0 DONE; Steps 1–7 PLANNED (execution-level breakdown below)**

The smoothing–quantization construction above, decomposed into ordered steps. Everything
listed as reused is public, compiling, and axiom-clean (Phase 1 state). Mathematical
strategy = the "Proof strategy" section above; this is the formalization-level plan.

**Design decisions (settled):**

* **Normalization for `IsPdf` — residual atom at the origin.** `∑_j w_j = ∫_{B_R} f =: c`
  is `< 1` in general, so the literal finite sum is not a pdf. Define
  `gmmApprox f R σ δ x := ∑_{j ∈ S(R,δ)} W_j · φ_σ(x − j) + (1 − ∑_{j∈S} W_j) · φ_σ(x)`
  (two terms; do NOT try to fold the residual into the `Finset` — the insertion
  bookkeeping when `0 ∈ S` is worse than a separate summand). Chosen over normalized
  weights `w_j/c` because: (i) no division anywhere (option (a) needs the side lemma
  `c > 0`, i.e. a separate tail argument, plus `1/c`-bookkeeping in every identity);
  (ii) the mass is a plain `Finset`-sum + one term (Phase 0's `integral_finsetSum`
  pattern); (iii) nonnegativity needs only `c ≤ 1` (trivial: `f ≥ 0`, total mass 1,
  `set_integral` mono); (iv) the residual's weighted error `(1−c)·∫ w φ_σ =
  (1−c)(1 + σ·M)` is controlled by the SAME `R`-tail budget as the outside-the-box
  term, since `1 − c = ∫_{B_R^c} f ≤ ∫_{B_R^c} w f` — no extra ε-slot in the budget
  assembly; (v) the result is still an honest GMM (finitely many Gaussians, common
  covariance `σ²·I`, bounded locations).
* **Diagonal choice:** `σ K = 1/(K+1)`, `δ K = σ K² = 1/(K+1)²`, `R K = K+1`. What must
  tend to 0 is `δ K / σ K = σ K` (scaled-modulus argument, Step 3) — per-σ modulus
  continuity would NOT be uniform along the diagonal.
* **Moments of the approximants are NOT needed:** `cme_uniform_balls_R` requires
  `hfmom` only for the true prior `fh`, and `IsPdf` per approximant
  (`Main.lean` signature). So `Integrable (‖·‖·f_K)` is optional — skip unless a lemma
  needs it. (Per-K integrability of `w·|f − f_K|`, needed for the `hw` ∫⁻-bridge, IS
  needed — via domination `|f − f_K| ≤ f + f_K` and the weighted mass of `f_K`:
  `∫ w f_K = c·(1+R+σM)·-bound + (1−c)(1+σM) < ∞`, a `set_integral` + `Finset`-sum
  computation.)

**Step 0 — weighted translation continuity for INTEGRABLE `f`
(`weighted_modulus_tendsto_integrable`) — DONE (public, axiom-audited).**
As implemented: for `f ≥ 0` integrable with finite first moment,
`Filter.Tendsto (fun u => ∫ x, (1 + ‖x‖) * |f x − f (x + u)| ∂volume) (nhds 0) (nhds 0)`
— the `f(x+u)` sign; the `f(x−u)` form of the earlier draft (and of the (T)-lemma
`weighted_modulus_tendsto_seq`) is equivalent by `u ↦ −u`, and the code uses `+`
throughout, matching the `WithLp.toLp 2 (x + u)` transport helpers. The (T)-lemma
WITHOUT continuity; the one genuinely new analytic input. Core/tail architecture as
implemented (the unweighted route of the risk register, not the raw `DomAddAct`
statement sketch):
* unweighted primitive first: `modulus_tendsto_integrable` —
  `∫ |f x − f (x+u)| ∂volume → 0` for integrable `f` (no continuity), via Mathlib's
  continuous `DomAddAct` action on `Lp ℝ 1 volume` (the `Lp.instContinuousSMulDomMulAct`
  route: `DomAddAct.mk u +ᵥ MemLp.toLp f hmem` has coerced function a.e.
  `fun x => f (u +ᵥ x)`; the `L¹` distance computes back to the unweighted modulus via
  `L1.dist_def` + `edist_dist` + the a.e. chain);
* core: scale to the ball — `∫_{‖x‖ ≤ K} (1+‖x‖)|diff| ≤ (1+K) · ∫ |diff|`
  (`hcoreB`), so the core budget `ε/2` comes from the unweighted modulus at the
  `u`-dependent threshold `ε/(2(1+K))` (`hcoreu`);
* tail: `setIntegral_tail_tendsto` for `g = (1+‖x‖)·f` at **natural** thresholds `k`
  (`htail : Tendsto (fun k => ∫ x in {y | ↑k < ‖y‖}, (1+‖x‖)*f x) atTop (𝓝 0)`), plus
  the threshold-shift transport `hI2'le`: move the indicator INTO the transported
  function (`integral_toLp_trans_right` with `c = −u`), giving
  `∫_{‖y‖ > K} (1+‖y‖) f(y+u) ≤ (1+‖u‖) · ∫_{‖z‖ > K−1} (1+‖z‖) f(z)` — the real
  threshold `K − ‖u‖` of the sketch is rounded down to the integer `K − 1` because the
  tail lemma is stated at natural `k` (valid since `‖u‖ < 1`), and the `htri`-style
  `‖z‖ ≤ ‖z−u‖ + ‖u‖` bound supplies the `(1+‖u‖)` factor; the thresholds actually used
  are `K` and `K − 1` (`htK`, `htK1`) — never `↑K − 1` directly (gotcha 7);
* assembly: the `Tendsto` form of the statement (the ε-δ form is recovered by
  `Metric.tendsto_nhds`); budgets: core `ε/2`, tail `ε/8 + ε/4` (the `ε/8` threshold
  comes from `htail`), final `ε/2 + ε/8 + ε/4 < ε`.
  The unweighted lemma is not a corollary of the weighted one here — it is the
  *primitive* the core is built on; the weighted form is what Step 1 consumes
  (Step 3's `L₁` at `φ_1` follows from the (T)-lemma by domination `1 ≤ w`).

**Step 1 — smoothing for general `f` (`weighted_smoothing_integrable`).**
`∫ w·|f − f⋆φ_σ| → 0` as `σ → 0` (`f` integrable + finite first moment, NO continuity).
* **Reuse existing Phase 1 infrastructure instead of writing a new `G_f`:**
  In `ApproximationByGMM.lean`, `weightedModulus n f u` (`= ∫ (1+‖x‖)*|f(x−u) − f x| dx`)
  is ALREADY defined! Moreover, inspecting the proof of `weightedModulus_le`,
  `stepA_gaussSmoothed`, `integrable_joint_first`, `integrable_joint_second`, and
  `integrable_joint_smooth_prior`, they only use `hf : Continuous f` in one line:
  `have hfm : Measurable f := hf.measurable`!
  - **Action item 1a:** Generalize (or provide `_of_measurable` variants of)
    `isPdf_gaussSmoothed`, `weightedModulus_le`, `stepA_gaussSmoothed`,
    `integrable_joint_first`, `integrable_joint_second`, `integrable_joint_smooth_prior`,
    `measurable_gaussSmoothed`, and `integrable_weighted_abs_diff_gaussSmoothed` by
    replacing `(hf : Continuous f)` with `(hfm : Measurable f)` (note: for any
    `Integrable f volume`, if `f` is not assumed `Measurable` upfront, either assume
    `(hfm : Measurable f)` on `f` — every pdf of interest is measurable, or replace `f`
    by `hfi.1.mk f` a.e.; simplest and cleanest: add `(hfm : Measurable f)` to the
    target theorem or weaken `Continuous f` to `Measurable f` in those Phase 1 lemmas,
    since `(hf : Continuous f)` immediately implies `hf.measurable`).
  - **Action item 1b:** Bridge `weightedModulus n f u` (`f(x−u) − f x`) to Step 0's
    `weighted_modulus_tendsto_integrable` (`f x − f(x+u)`) via `u ↦ −u` and `abs_sub_comm`:
    `weightedModulus n f u = ∫ x, (1+‖x‖) * |f x − f (WithLp.toLp 2 (x + (−u)))|`, so
    `Tendsto (weightedModulus n f) (nhds 0) (nhds 0)` follows in 10 lines from
    `weighted_modulus_tendsto_integrable.comp tendsto_neg_nhds_zero`!
  - **Action item 1c:** Then `weighted_smoothing_integrable` is literally a 50-line copy
    of `weighted_smoothing_tendsto_seq` (or directly replaces it by weakening
    `Continuous f` to `Measurable f`), using the Step 1b limit in place of
    `weighted_modulus_tendsto_seq`. This saves ~500 lines of duplicated Fubini/Tonelli code!

**Step 2 — half-open lattice cell construction (no boundary edge cases).**
* **Integer index grid & half-open cells (simplification):**
  Instead of intersecting preimages of `latticeQ` with a closed box `[-R, R]^n` (which
  causes off-by-one boundary headaches at `t_i = R` where `⌊R/δ⌋` jumps to the next cell),
  parameterize the finite grid directly by an integer half-width `N : ℕ`:
  - `gridFinset (n : ℕ) (N : ℕ) : Finset (Fin n → ℤ) :=
      Fintype.piFinset (fun _ : Fin n => Finset.Ico (-(N : ℤ)) (N : ℤ))`
  - `latticeIdx (δ : ℝ) (t : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ :=
      fun i => ⌊(t : Fin n → ℝ) i / δ⌋`
  - `latticeQ (δ : ℝ) (t : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ))`
  - `gridPoint (δ : ℝ) (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => δ * (k i : ℝ))`
  - `cell (δ : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
      {t | ∀ i : Fin n, (k i : ℝ) * δ ≤ (t : Fin n → ℝ) i ∧ (t : Fin n → ℝ) i < ((k i : ℝ) + 1) * δ}`
    (equivalently `{t | latticeIdx δ t = k}` for `δ > 0` via `Int.floor_eq_iff`).
* **Why this representation is smooth in Lean:**
  1. `MeasurableSet (cell δ k)` is immediate (`Finset.measurableSet_biInter` of half-open
     coordinate intervals `(continuous_apply i).measurable Keep preimage of Ico`).
  2. On `t ∈ cell δ k`, `latticeQ δ t = gridPoint δ k` is immediate from `Int.floor_eq_iff`
     (after dividing by `δ > 0`).
  3. **Pairwise disjointness** of `cell δ k` for `k ∈ gridFinset n N` is 3 lines: if
     `t ∈ cell δ k₁ ∩ cell δ k₂`, then `k₁ = latticeIdx δ t = k₂`.
  4. **Covered box:** define `coveredBox (δ : ℝ) (N : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
     ⋃ k ∈ gridFinset n N, cell δ k`. By `Int.floor_eq_iff`, for `N * δ ≥ R`,
     `{t | ‖t‖ ≤ R} ⊆ {t | ∀ i, |(t : Fin n → ℝ) i| < N * δ} ⊆ coveredBox δ N`, so its
     complement `(coveredBox δ N)ᶜ` is contained in `{t | R < ‖t‖}`!
  5. **Partition identity (`sum_setIntegral_cell`):** for any integrable `g`,
     `∑ k ∈ gridFinset n N, ∫ t in cell δ k, g t ∂volume = ∫ t in coveredBox δ N, g t ∂volume`
     is a single call to `MeasureTheory.integral_biUnion_finset`!
  6. **Displacement bound (`norm_latticeQ_sub_le`):** for all `t` and `δ > 0`,
     `‖latticeQ δ t − t‖ ≤ δ * Real.sqrt n` (from per-coordinate
     `0 ≤ t_i - δ⌊t_i/δ⌋ < δ` via `Int.floor_le` and `Int.lt_floor_add_one`, plus
     `EuclideanSpace.norm_eq`).
  7. **Weights:** `cellWeight f δ k := ∫ t in cell δ k, f t ∂volume`. By the partition
     identity, `∑ k ∈ gridFinset n N, cellWeight f δ k = ∫ t in coveredBox δ N, f t ∂volume ≤ 1`.

**Step 3 — quantization estimate (`gmmApprox_quantization`) without `sSup` or `Q_δ` joint-integrability.**
Define `gmmApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
(hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (N : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ`:
`fun x => (∑ k ∈ gridFinset n N, cellWeight f δ k *
    mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))))
  + (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x`
(note: using `mollifier n C hC σ hσ (x − μ)` directly matches `gaussSmoothed n f C hC σ hσ`
and works for *any* positive definite covariance `C`, including `C = 1` where
`mollifier n 1 _ σ hσ (x − μ) = multivariateGaussianPDF n μ (σ² • 1) _ x`).
* **Crucial formalization insight — cell-by-cell Tonelli (`Integrable.prod_mul`) eliminates `latticeQ` from joint integrability (and makes Step 4 optional!):**
  In Bochner-integral Fubini (`MeasureTheory.integral_prod`), swapping `∫_x` and `∫_t`
  requires proving joint `Integrable` on `volume.prod volume`. If we merged the finite
  sum over `k ∈ gridFinset n N` into `∫_{coveredBox} f(t) ψ_σ(x − Q_δ(t)) dt` *before*
  integrating over `x`, we would have to prove joint integrability of a two-variable
  function involving the floor-quantizer `Q_δ(t)` (~150+ lines of `lintegral` Tonelli
  boilerplate) and separately prove the `integral_subst` scaling for a difference of two
  mollifiers.
  Instead, **keep the finite sum over `k ∈ gridFinset n N` on the outside**:
  1. For each cell `k`, write
     `cellWeight f δ k * ψ_σ(x − x_k) − ∫ t in cell δ k, f t * ψ_σ(x − t) ∂volume
      = ∫ t in cell δ k, f t * (ψ_σ(x − x_k) − ψ_σ(x − t)) ∂volume`
     (since `ψ_σ(x − x_k)` is constant in `t`, via `integral_mul_const` and `integral_sub`).
  2. Split `gaussSmoothed … x = (∑ k ∈ gridFinset n N, ∫ t in cell δ k, f t * ψ_σ(x − t))
     + ∫ t in (coveredBox δ N)ᶜ, f t * ψ_σ(x − t)` (via `integral_add_compl` and Step 2's
     `integral_biUnion_finset`, using the symmetric convolution rewrite
     `gaussSmoothed … x = ∫ t, f t * ψ_σ(x − t)` from `integrable_toLp_sub`).
  3. By the triangle inequality (`abs_add`, `Finset.abs_sum_le_sum_abs`,
     `abs_integral_le_integral_abs`) and `integral_finsetSum`, the `x`-integral of the
     difference splits into a finite sum over `k ∈ gridFinset n N` of cell errors plus
     the two tail pieces (`(1 − c) * ∫ w(x) ψ_σ(x) dx` and the `(coveredBox δ N)ᶜ` tail).
  4. **Why joint integrability on each cell `k` is now trivial:** on `cell δ k`, the
     integrand `(t, x) ↦ (cell δ k).indicator f t * ((1 + ‖x‖) * |ψ_σ(x − x_k) − ψ_σ(x − t)|)`
     is dominated by the sum of:
     - `(cell δ k).indicator f t * ((1 + ‖x‖) * ψ_σ(x − x_k))`: a **separable product**
       `g(t) * h(x)` where `x_k` is constant in `t`! Its joint integrability on
       `volume.prod volume` is a 1-line call to `MeasureTheory.Integrable.prod_mul`!
     - `f t * ((1 + ‖x‖) * ψ_σ(x − t))`: its joint integrability is ALREADY proven in
       Phase 1 (`integrable_joint_smooth_prior` + coordinate change)!
     Thus `Q_δ(t)` (`latticeQ`) NEVER appears inside any product-measure integrability
     proof; all we need on `t ∈ cell δ k` is the coordinatewise distance bound
     `‖t − gridPoint δ k‖ ≤ δ * Real.sqrt n`!
* **Scaled-modulus lemma (`weightedModulus_mollifier_le`):**
  By linear change of variables `x = σ y` (`integral_subst n 0 (σ • 1)`), for any
  shift `s : EuclideanSpace ℝ (Fin n)`:
  `∫ x, (1 + ‖x‖) * |mollifier n C hC σ hσ (x + s) − mollifier n C hC σ hσ x| ∂volume
   = ∫ y, (1 + σ * ‖y‖) * |φ_C (y + σ⁻¹ • s) − φ_C y| ∂volume`
  `≤ weightedModulus n φ_C (WithLp.toLp 2 (-(σ⁻¹ • s)))` (when `σ ≤ 1`),
  and similarly the unweighted $L^1$ shift satisfies
  `∫ x, |mollifier n C hC σ hσ (x + s) − mollifier n C hC σ hσ x| ∂volume
   = ∫ y, |φ_C (y + σ⁻¹ • s) − φ_C y| ∂volume
   ≤ weightedModulus n φ_C (WithLp.toLp 2 (-(σ⁻¹ • s)))` (since `1 ≤ 1 + ‖y‖`).
  Notice the huge simplification: **for `σ ≤ 1`, BOTH the weighted modulus of `ψ_σ` and
  the unweighted $L^1$ modulus of `ψ_σ` at shift `s` are bounded by the SINGLE quantity
  `weightedModulus n φ_C (-(σ⁻¹ • s))`!** We do not even need a separate `L₁` definition
  or `σ(2M₁ + ‖s/σ‖)` splitting!
* **Pointwise `η`-bound instead of `sSup` (`gmmApprox_quantization_of_modulus_bound`):**
  Since `φ_C` is a continuous pdf with finite first moment, `weighted_modulus_tendsto_seq`
  (or Step 1b) gives `Tendsto (weightedModulus n φ_C) (nhds 0) (nhds 0)`.
  Instead of taking `sSup` over `‖s‖ ≤ δ√n` (which requires `BddAbove` in Lean), prove
  `gmmApprox_quantization_of_modulus_bound`:
  > Given `η > 0`, if `∀ u, ‖u‖ ≤ δ * Real.sqrt n / σ → weightedModulus n φ_C u ≤ η`,
  > and `σ ≤ 1`, `0 < δ`, `(K : ℝ) ≤ N * δ`, then
  > `∫ x, (1 + ‖x‖) * |gmmApprox … x − gaussSmoothed … x| ∂volume
  >  ≤ η * (1 + ∫ t, ‖t‖ * f t ∂volume) + 2 * (1 + M_φ) * ∫ t in {y | (K : ℝ) < ‖y‖}, (1 + ‖t‖) * f t ∂volume`.
  Proof via the cell-by-cell decomposition above:
  1. For each cell `k ∈ gridFinset n N`, Tonelli (`integral_prod`) swaps `∫_x` and
     `∫_{t ∈ cell δ k}`. For each `t ∈ cell δ k`, shifting `y = x − t`
     (`integral_toLp_trans_right`), bounding `1 + ‖y + t‖ ≤ (1 + ‖y‖) + ‖t‖`, and
     applying `weightedModulus_mollifier_le` with `s = t − gridPoint δ k`
     (`‖s‖ ≤ δ * Real.sqrt n`, so `‖-(σ⁻¹ • s)‖ ≤ δ * Real.sqrt n / σ`) bounds the inner
     `x`-integral by `(1 + ‖t‖) * weightedModulus n φ_C (-(σ⁻¹ • s)) ≤ η * (1 + ‖t‖)`.
     Integrating over `t ∈ cell δ k` and summing over `k ∈ gridFinset n N` via Step 2's
     `sum_setIntegral_cell` gives
     `≤ η * ∫ t in coveredBox δ N, (1 + ‖t‖) * f t ≤ η * (1 + M_f)` (R-free!).
  2. On `(coveredBox δ N)ᶜ ⊆ {t | (K : ℝ) < ‖t‖}`, both `(1 − c) ∫ w ψ_σ` and
     `∫_{(coveredBox)ᶜ} f(t) ∫ w(x) ψ_σ(x − t) dx dt` are bounded by
     `(1 + σ M_φ) * ∫_{(coveredBox)ᶜ} (1 + ‖t‖) f(t) dt ≤ (1 + M_φ) * ∫_{‖t‖ > K} (1 + ‖t‖) f(t) dt`.

**Step 5 — `IsPdf (gmmApprox …)` and bridge to `gmmPDF` (`isPdf_gmmApprox`, `gmmApprox_eq_gmmPDF`).**
* `isPdf_gmmApprox`: Nonnegativity from `0 ≤ cellWeight f δ k`, `1 − c ≥ 0` (since
  `c = ∫_{coveredBox} f ≤ ∫ f = 1`), and `0 ≤ mollifier`. Mass `= 1` from
  `integral_add`, `integral_finsetSum`, `integral_const_mul`, `integral_mollifier` (`= 1`),
  and `c + (1 − c) = 1`.
* **Syntactic bridge to `gmmPDF` (Goal 2):**
  To satisfy Goal (2) literally (`g K = gmmPDF n m (σ_K² • C) _ w μ`), note that
  `mollifier n C hC σ hσ (x − μ) = multivariateGaussianPDF n μ (σ² • C) _ x`
  (by `multivariateGaussianPDF_eq` and `det`/`inv` scaling of `σ² • C`), and any
  `Finset`-sum `∑ k ∈ S, W_k * φ(x − μ_k) + (1 − ∑ W_k) * φ(x − 0)` can be re-indexed
  via `S.equivFin` onto `Fin (S.card + 1)` (`Fin.sum_univ_castSucc`), putting the
  residual weight `1 − c` at `Fin.last S.card` with location `0`. This 25-line bridge
  gives an exact `gmmPDF` witness without complicating Steps 3–6!

**Step 6 — the explicit diagonal sequence (`gmmPriorSeq`) and `hw`.**
* Choose the explicit parameters at index `K : ℕ`:
  - `σ_K := 1 / ((K : ℝ) + 1)` (`0 < σ_K ≤ 1`, `σ_K → 0`)
  - `δ_K := 1 / ((K : ℝ) + 1) ^ 2` (`δ_K / σ_K = σ_K → 0`)
  - `N_K := (K + 1) ^ 3` (so `N_K * δ_K = K + 1 ≥ K`, ensuring
    `(coveredBox δ_K N_K)ᶜ ⊆ {t | (K : ℝ) < ‖t‖}` without needing `Nat.ceil`!).
  *(Choosing `N_K = (K + 1)^3` so that `N_K * δ_K = K + 1` is an exact algebraic identity
  completely eliminates `Nat.ceil` from the formalization!)*
* Triangle inequality:
  `∫ w |f − gmmPriorSeq K| ≤ ∫ w |f − gaussSmoothed K| + ∫ w |gaussSmoothed K − gmmPriorSeq K|`.
  - First term `→ 0` by Step 1 (`weighted_smoothing_integrable`).
  - Second term `→ 0` by Step 3 (`gmmApprox_quantization_of_modulus_bound`): given `ε > 0`,
    pick `η = ε / (4 * (1 + M_f))` to get radius `r > 0` from continuity of
    `weightedModulus n φ_C` at `0`; for large `K`, `δ_K * √n / σ_K = √n / (K + 1) < r`
    and the tail `2 * (1 + M_φ) * ∫_{‖t‖ > K} (1 + ‖t‖) f(t) < ε / 2` by
    `setIntegral_tail_tendsto`.
* Convert real `∫` convergence to the `∫⁻ ENNReal.ofReal` form `hw` using
  `ofReal_integral_eq_lintegral_ofReal` (exact Phase 1 `hw_smoothedPriorSeq` pattern).

**Step 7 — the final corollaries (`gmm_density_weighted_L1`, `cme_uniform_balls_gmm_prior_general`).**
Compose `isPdf_gmmApprox` + `hw_gmmPriorSeq` with `cme_uniform_balls_R` (exact Phase 1
`cme_uniform_balls_smoothed_prior` pattern).

**Deliverables checklist:**
* `weighted_modulus_tendsto_integrable` (Step 0) — **DONE** (together with its
  unweighted primitive `modulus_tendsto_integrable`; both public, axiom-audited);
  `weightedModulus_tendsto_integrable` + `weighted_smoothing_integrable` (Step 1) —
  obtained by weakening `(hf : Continuous f)` to `(hfm : Measurable f)` in the Phase 1
  smoothing helpers and plugging in Step 0.
* `gridFinset`, `latticeIdx`, `latticeQ`, `gridPoint`, `cell`, `coveredBox`,
  `cellWeight`, `sum_setIntegral_cell` (`integral_biUnion_finset`),
  `norm_latticeQ_sub_le` (Step 2), and `gmmApprox_sum_eq_setIntegral` (Step 4).
* `gmmApprox` def + `isPdf_gmmApprox` + `gmmApprox_eq_gmmPDF` (Step 5),
  `weightedModulus_mollifier_le` + `gmmApprox_quantization_of_modulus_bound` (Step 3).
* `gmmPriorSeq` (with `σ_K = 1/(K+1)`, `δ_K = 1/(K+1)²`, `N_K = (K+1)³`) +
  `hw_gmmPriorSeq` (Step 6), `gmm_density_weighted_L1` +
  `cme_uniform_balls_gmm_prior_general` (Step 7).
* `AxiomCheck.lean` audits for every new public theorem (Phase 1 convention).
* Follow the Phase 1 file layout: public defs/lemmas in `ApproximationByGMM.lean`,
  appended in dependency order.

**Risk register (updated):**
(a) the L^p-translation-continuity Mathlib route (Step 0 core) — **RESOLVED: Step 0 is
done via the unweighted L¹ `DomAddAct` route** (`modulus_tendsto_integrable`) plus the
Phase 1 tail architecture with integer thresholds.
(b) the measurable-partition `set_integral` bookkeeping (Steps 2/4) — **SIMPLIFIED**:
using half-open cells `cell δ k` indexed by `gridFinset n N = Fintype.piFinset (fun _ =>
Ico (-N) N)` and defining `coveredBox δ N` as their `biUnion` eliminates boundary
off-by-one issues at `t_i = R` and reduces the partition identity to a direct call to
`MeasureTheory.integral_biUnion_finset`; choosing `N_K = (K+1)³` with `δ_K = 1/(K+1)²`
gives `N_K * δ_K = K + 1` algebraically and eliminates `Nat.ceil`.
(c) the diagonal & quantization assembly (Steps 3/6) — **SIMPLIFIED**:
  1. **Cell-by-cell Tonelli (`Integrable.prod_mul`)**: keeping the finite sum over
     `k ∈ gridFinset n N` on the outside and applying Fubini cell-by-cell means the
     quantized center `x_k = gridPoint δ k` is constant on `cell δ k`, so the
     `(t, x)`-dominator is a separable product `g(t) * h(x)` whose joint integrability on
     `volume.prod volume` is a 1-line `MeasureTheory.Integrable.prod_mul` call (plus
     Phase 1's `integrable_joint_smooth_prior`). Thus `latticeQ` (`Q_δ(t)`) is completely
     eliminated from all product-measure integrability proofs!
  2. **Single `weightedModulus` bound**: for `σ ≤ 1`, both the weighted modulus and the
     unweighted $L^1$ shift of `mollifier … σ` at shift `s` are bounded by the single
     quantity `weightedModulus n φ_C (-(σ⁻¹ • s))`, eliminating a separate `L₁`
     definition.
  3. **`sSup`-free quantization lemma**: stating `gmmApprox_quantization_of_modulus_bound`
     with an explicit `η`-hypothesis (`∀ u, ‖u‖ ≤ δ√n/σ → weightedModulus n φ_C u ≤ η`)
     completely avoids `sSup` and `BddAbove` over uncountable balls.
(d) `Int.floor` manipulation under `WithLp` coercions (Step 2) — do all floor arithmetic
on the plain `Fin n → ℝ` coordinates (`(t : Fin n → ℝ) i`) via `Int.floor_eq_iff`,
`Int.floor_le`, and `Int.lt_floor_add_one` before wrapping in `WithLp.toLp 2`.
(e) the weight-shift correction in §2/Step 3 — keep the `(1 + ‖t‖)` factor inside the
`coveredBox` integral against `f(t)` so it integrates to `η * (1 + M_f)` (R-free).

### Non-goals / explicit caveats

* **No rates.** The theorem is pure convergence. Quantitative rates (Bacharoglau-type
  `O(K^{-2/d})` for bounded `f`, or the L^p/multivariate refinements) are a further
  project.
* **No global uniform convergence.** `cme_uniform_balls_R` is locally uniform; the
  global statement is false under these hypotheses (bump counterexample, documented
  above and in the `main_theorem` discussions).
* **No bridge from Nguyen et al. Theorem 5(a).** Their result (L¹ mode, `C₀` class,
  no control of the approximants' moments) does not imply `hw`; see the counterexample
  above. Our construction is self-contained.
* **Continuity of the GMM priors is not needed** by `cme_uniform_balls_R` (it is
  available anyway — Gaussian mixtures are continuous — but the theorem does not use
  it).


**CRITICAL RECOVERY NOTE (latest round).** The working file `ApproximationByGMM.lean` was
accidentally truncated by an editing script and had to be recovered from the git HEAD copy
(read-only `git show`, user-approved). Recovered state (compiling, zero `sorry`, axioms
clean):

* everything up to and including the `(T)`-lemma `weighted_modulus_tendsto_seq` and the
  Fubini mass chain of `isPdf_gaussSmoothed` — now FULLY PROVEN (the final steps:
  the `hcongr` swapped-pair congr via `simp [Prod.swap]`, then `integral_prod` with
  `hΦint`, the inner `integral_congr_ae` with `integral_const_mul + hshiftmass + mul_one`,
  and `integral_mollifier`); `isPdf_gaussSmoothed` is done.

**RE-APPLIED (latest round) — all blocks restored and verified:** the file is back to its
full pre-truncation state (2369 lines, zero `sorry`, full build green, axioms clean):
1. `mollifier_le_zero` — DONE.
2. `mollifier_integrable` — DONE.
3. `lintegral_mollifier_mul_norm` — DONE.
4. `weightedModulus` def + `weightedModulus_le` + `aemeasurable_weightedModulus` — DONE.
5. `weighted_smoothing_tendsto_seq` — DONE (public, ~700 lines; Step A per-x identity,
   Step B ∫⁻-Tonelli joint integrability + Fubini calc + `integral_mollifier_mul`
   transport, Step C shifted-sequence DCT + final sandwich).
6. `Main.lean`: `multivariateGaussianPDF_le_const` is `public`.
7. `AxiomCheck.lean` audits `isPdf_gaussSmoothed`, `weighted_modulus_tendsto_seq`,
   `weighted_smoothing_tendsto_seq` (all `public` in ApproximationByGMM.lean).

**Latest round (continued after recovery):** the per-σ smoothing machinery has been
EXTRACTED into standalone public lemmas (copy-based, the smoothing theorem untouched and
still compiling):
* `measurable_mollifier` (new top-level lemma; fun_prop needs a `Measurable (mollifier …)`
  hypothesis in context — this was the blocker for the extracted blocks),
* `measurable_joint_first` (the ψ-first joint difference integrand's measurability),
* `stepA_gaussSmoothed` (the per-x pointwise identity; note `WithLp.ofLp_neg` for the
  reflection congruence),
* `integrable_joint_first` (the ∫⁻-Tonelli joint integrability, ψ-first),
* `integrable_joint_second` (the x-first orientation via the measure-preserving swap;
  note the ∏-∘ vs flat-lambda syntactic-mismatch trap: provide the meas-arg as a
  previously-`have`-bound FLAT-lambda lemma, never an inline `.mul`/`.comp` term).
All compiling, zero `sorry`, AxiomCheck green.

Phase 1 remaining work (design not affected by the incident):
* the hw-existence theorem: `σ K = 1/(K+1)`, `IsPdf (gaussSmoothed n f C hC (1/(K+1)))` per
  `K` (via `isPdf_gaussSmoothed`), and the `hw` of `cme_uniform_balls_R` via the smoothing
  theorem + the `ofReal_integral_eq_lintegral_ofReal` conversion
  (`∫⁻ ofReal ((1+‖h‖)·|f h − fhK h|) = ofReal (∫ …) < ofReal ε` from a real-∫ bound);
* the composed corollary through `cme_uniform_balls_R` (Phase 1 deliverable);
* `plan.md` status updates.

**LOST in the truncation and still to be REWRITTEN (all tactics were verified once this
session, so this is re-application, not design):**
1. `mollifier_le_zero` (mollifier ≤ peak at 0, via `multivariateGaussianPDF_le_const`,
   which was made `public` in Main.lean).
2. `mollifier_integrable` (via `hasFiniteIntegral_iff_ofReal` + `lintegral_mollifier`).
3. `lintegral_mollifier_mul_norm`: `∫⁻ ψ_σ·‖u‖ₑ = ofReal (σ * M_φ)` (same
   `map_linearMap_addHaar` transport as `lintegral_mollifier`; `ENNReal.ofReal_mul` takes
   only ONE nonneg hypothesis; endgame `ring` on ENNReal works).
4. `weightedModulus` def + `weightedModulus_le` (bound `(1+M)(2+‖u‖)`; x-shift via
   `integral_shift_neg` + triangle inequality; split via `abs_sub`; watch the
   `(1 + ‖x‖)`-parenthesisation in `‖...‖` — the `‖`-bar must close AFTER the
   `WithLp.toLp 2 (...)` arg) + `aemeasurable_weightedModulus` (via
   `StronglyMeasurable.integral_prod_right'`).
5. `weighted_smoothing_tendsto_seq` (the smoothing theorem, ~700 lines):
   per-σ `hchain` = Step A (per-x identity via `∫ ψ = 1`, `integral_sub`,
   `abs_integral_le_integral_abs`, the reflection `Measure.measurePreserving_neg` +
   `integrable_toLp_shift` + ψ(0)-domination for per-x integrability) + Step B
   (joint integrability `hΦint` via ∫⁻-Tonelli with the ψ-moment, the Fubini calc with
   `integral_prod`/`integral_prod_swap`/swap-congrs, `integral_mollifier_mul` transport)
   + Step C (DCT `tendsto_integral_of_dominated_convergence` with bound
   `φ_C·(1+M)(2+‖v‖)` from `weightedModulus_le` + `σ_k ≤ 1`, shifted sequence
   `σ(k+k₀)` + `Filter.tendsto_add_atTop_iff_nat`, final sandwich through `hchain`).
   KEY GOTCHAS recorded this session: `calc` with `=`-steps does NOT auto-bridge to a
   `≤` goal — the FIRST step's operator must be `≤`; `AEMeasurable`/`StronglyMeasurable`
   are ∃-structures with no `.comp` (use `.comp_measurable`, `.comp_aemeasurable`);
   `ENNReal.ofReal_mul` has ONE explicit hypothesis; `Real.enorm_eq_ofReal_abs` converts
   `‖r‖ₑ = ofReal |r|`; `mul_le_mul_of_nonneg_left/right` (not `*_left` only); the
   ∫⁻ Fubini equality is `lintegral_prod` (forward direction turns pair-form into
   iterated); `Filter.Eventually.of_forall`, `norm_pos_iff.2`, `tendsto_const_nhds
   (x := ...)`.
6. Then the hw-existence theorem (`σ_K = 1/(K+1)`, per-K `IsPdf (gaussSmoothed …)`,
   hw via `ofReal_integral_eq_lintegral_ofReal` conversion) and the composed corollary
   through `cme_uniform_balls_R`.
7. `Main.lean`: `multivariateGaussianPDF_le_const` was made `public` (needed by the
   mollifier-peak lemma).


**Phase 2 Step 0 status (final):**

DONE and verified: `modulus_tendsto_integrable` (unweighted L¹ translation continuity for
integrable `f`, no continuity needed) — via Mathlib's continuous `DomAddAct` action on
`Lp ℝ 1 volume`: `DomAddAct.mk u +ᵥ MemLp.toLp f hmem` has coerced function a.e.
`fun x => f (u +ᵥ x)`, and the `L¹` distance of the action translate computes to the
unweighted translation modulus via `L1.dist_def` + `edist_dist` + the a.e. chain
(`MemLp.coeFn_toLp`, `DomAddAct.vadd_Lp_ae_eq`,
`hmp.quasiMeasurePreserving.ae_eq_comp`). Full build was green with it.

DONE and verified (this session): `weighted_modulus_tendsto_integrable` (the weighted
Step 0 lemma) — full build green, zero `sorry`, public and axiom-audited
(`AxiomCheck.lean`, 13 audits total). Architecture as implemented: core = the unweighted
lemma scaled by `(1+K)` on the ball (`hcoreB`/`hcoreu`); tails =
`setIntegral_tail_tendsto` at the natural thresholds `K` and `K−1` with the
threshold-shift transport `hI2'le` via `integral_toLp_trans_right` (indicator moved INTO
the transported function; `(1+‖u‖)` factor from the `htri` bound and `‖u‖ < 1`);
budgets ε/2 + ε/8 + ε/4. The `+ᵥ`/`toLp`/beta/defeq form-alignment issues catalogued
below were all resolved in place; the pass also fixed two real defects (a free-`x`
typo inside the `{y | …}` set literals of `hptx`/`htr`, which made them constant sets,
and a wrong-shape `le_trans (le_refl _)` step in `hWint`, replaced by
`add_le_add` + `← mul_assoc`), and bumped the theorem's `maxHeartbeats` to 2000000.

**New gotchas catalogued (Phase 2 Step 0):**
1. `have h := e` locals do NOT unfold for `rfl`/term-level defeq checks against their own
   definition (the `fL := MemLp.toLp f hmem` saga) — avoid `have`-bound Lp elements in
   statement positions; write `MemLp.toLp f hmem` inline (its coercion DOES reduce
   pointwise via `AEEqFun.coeFn_mk`-rfl-chain... empirically the +ᵥ-annotated forms
   typecheck but the toLp-substituted ones don't when mixed).
2. `⇑X` and `↑↑X` for Lp elements are the SAME term (`AEEqFun.cast`) — but `rw` pattern
   matching still failed across the `.sub`-lemma's ↑↑-form vs a ⇑-goal once (cause:
   the argument shape, not the notation).
3. The REAL failure driver everywhere: `+ᵥ`-forms and `WithLp.toLp 2 ((x : Fin n → ℝ) +
   (u : Fin n → ℝ))`-forms are NOT defeq (they differ by `add_comm` and `Real.instAdd` is
   NOT exposed for unfolding in this module-Mathlib). Bridge them ONLY propositionally,
   via `vadd_toLp_add x u` (proven: ofLp-injective + ofLp_add + add_comm + add_sub_cancel).
   ⇒ RULE: keep each proof internally in ONE form; the `DomAddAct` action proofs in the
   `+ᵥ`-form (they match `vadd_Lp_ae_eq`, `mk_vadd_toLp`); the ∫-statement forms in the
   `toLp`-idiom form; connect by `Tendsto.congr'`/`integral_congr_ae` pointwise bridges.
4. `memLp_one_iff_integrable.mp hSR` gives `Integrable` of hSR's PLAIN function
   (`f ∘ (u +ᵥ ·)`, the ∘-form, beta-equal to the flat `fun x => f (u +ᵥ x)`) — NO
   `MemLp.coeFn_toLp` is needed for `Integrable.congr`; the coe is needed only for the
   pointwise a.e. identification of the coerced values.
5. `add_sub_cancel` in this Mathlib is `a + (b - a) = b` (pattern `?a + (?b - ?a)`);
   for `(a + b) - b = a` use `add_sub_cancel_right`.
6. `Continuous.isClosed_preimage` does not exist; get MeasurableSet of `{y | ‖y‖ ≤ K}` via
   `A = Bᶜ` (ext + `not_lt`) + `hBmeas.compl`.
7. `(K - 1 : ℕ) : ℝ` vs `↑K - 1` cast mismatch. The earlier advice ("use `K₁` directly,
   never `K - 1`") was **superseded by the implementation**: the statements that must
   match `hK₁K (K - 1)`/`htK1` (`hI2'le`'s RHS, `hg2int`, `hconv`, `hconst`) all use the
   `((K - 1 : ℕ) : ℝ)`-set form, and `↑K − 1` is reached only inside `linarith` through
   `hKm1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1` (proved by
   `rw [Nat.cast_sub (by omega : (1:ℕ) ≤ K), Nat.cast_one]`, with `hKdef : K = K₁ + 1`
   in context for `omega`). `K₁` survives only in the `hK₁` hypothesis. Rule: pick ONE
   cast form per statement and bridge between forms with a typed `have`, never mix them.
8. In this module-Mathlib, `Real.instAdd` etc. are NOT exposed for `whnf` defeq unfolding:
   any defeq check that must look inside a real sum FAILS. All Real-arithmetic identities
   must be propositional (`ring`/`linarith` with `hexp`-style rewrites).
9. abs-indicator integrand statements: count parens by generating the line from the
   verified `hWint` statement template (y-substituted), never by hand.

**Phase 2 Step 0 — final-round gotchas (the green-build pass):**
10. `rw` closes a refl-trivial goal (`0 = 0`, `0 ≤ 0`, `t ≤ t`) only at the END of its
    rule sequence. An extra rule after the goal is already trivial reports "did not find
    an occurrence of the pattern", and a trailing `exact le_refl _` after a closing `rw`
    reports "No goals to be solved". End such branches with the `rw`-sequence alone —
    verified in `hpt`-inr, `hWf'2int`-inr, `hg2int`-inl, and the `hI2'le` tail
    (`rw [hconst, hconv]`).
11. `mul_assoc` rewrites `(a*b)*c → a*(b*c)` (left-to-right): goals with a
    right-nested `a * (b * c)` — e.g. `((1:ℝ)+‖u‖) * ((1+‖z‖) * f z)` — need
    `rw [← mul_assoc]`. Used in `hpt`, `hWf'2int`, `hWint`. (An earlier draft had
    forward `rw [mul_assoc]` in all three; it fails with "did not find an occurrence".)
12. `LT.lt.not_le` does not exist for `Real.lt` — `hm.not_le` fails with "Invalid field
    notation". Use `not_le.mpr hm` / `not_lt.mpr hm`, and ANNOTATE the binder:
    `fun hc : x ∈ {…} => not_le.mpr hm (show ‖x‖ ≤ (K:ℝ) from hc)`. An unannotated
    `fun hc =>` lets the `?s`/`?a` metavariables unify backwards (the membership
    predicate is captured as the set — the pattern comes out as
    `Set.indicator (fun b => ↑K < ‖b‖) ?f ‖x‖` and never matches).
13. Multi-line `calc` step proofs break parsing: a `:= term` continued on the next line,
    or `:= by` + newline tactics in a step whose left-hand side spans lines, gets
    re-read as a NEW calc step ("invalid 'calc' step", "unexpected token"). Put the step
    proof on one line, or restructure with a `have`-ladder + `le_trans` (as in `h2` of
    `htailB`).
14. `by linarith [Nat.cast_nonneg K]` can leave the cast's type metavariable unsolved
    (goal `0 ≤ 1 + ↑K` stays open with an "unsolved goals" error). Use `by positivity`
    for `0 ≤ (1:ℝ) + K`-style goals.
15. `mul_le_mul_of_nonneg_left (h : b ≤ c) : a*b ≤ a*c` vs
    `mul_le_mul_of_nonneg_right (h : a ≤ b) : a*c ≤ b*c` — pick the variant whose
    COMMON factor matches the goal: `((1+‖u‖) * ε/8 ≤ 2 * ε/8)` needs `_right`
    (common `ε/8` on the right), `(1+‖u‖) * I ≤ (1+‖u‖) * J` needs `_left`.
16. `linarith` atoms must be syntactically identical: a hypothesis proved in one form
    (`htri : ‖x‖ ≤ ‖u +ᵥ x‖ + ‖u‖`) is a DIFFERENT atom from the goal's
    `‖WithLp.toLp 2 (x + u)‖`. Convert first with `rw [← vadd_toLp_add x u]`
    (as in `hWint`'s `htri`); defeq is not enough.
17. State the `integral_add` split as a typed
    `have hadd : (∫ …, A x + B x) = (∫ …, A x) + (∫ …, B x) := integral_add hf hg`
    (defeq-checked, beta/zeta absorbed) and `rw [hadd, hI1']`; a bare
    `rw [integral_add hf hg]` must match the goal's integrand through the beta/zeta
    redexes left by `.add`/`.indicator` chains and can fail.
18. The `hI2'le` tail needs `set_option maxHeartbeats 2000000` (the kernel timed out at
    the default and at 800000): the `show`-defeq canonicalization plus
    `rw [hconst, hconv]` produces expensive proof terms.
