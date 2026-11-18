# Plan: Gaussian mixture priors satisfy the weighted-L¹ convergence hypothesis

Status: Phase 0 implemented and verified (see below); Phases 1–2 are planning documents.

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

2. **Quantization (lattice cells).** For lattice spacing `δ ≪ σ`, define the rounding
   map `Q_δ(t) = δ ⌊t/δ⌋` (componentwise; a measurable, piecewise-constant map with
   `‖Q_δ(t) − t‖ ≤ δ√n`). Let the cells be the finitely many fibers of `Q_δ` inside a
   large box, with centers `x_j = Q_δ(x_j)` and weights `w_j = ∫_{cell j} f`. Define
   `f_K(x) = ∑_j w_j φ_σ(x − x_j)` — a **finite** mixture (sum over lattice points in
   the box), and an integral identity
   `f_K(x) = ∫ f(t) φ_σ(x − Q_δ(t)) dt` holds (finite sum ↔ integral interchange).
   Then
   `‖f_K − f ⋆ φ_σ‖_{L¹(w)}
      ≤ ∫ f(t) · ∫ w(x) |φ_σ(x − Q_δ(t)) − φ_σ(x − t)| dx dt
      ≤ sup_{‖s‖ ≤ δ√n} ∫ w(x) |φ_σ(x + s) − φ_σ(x)| dx`,
   which → 0 as `δ → 0` by **continuity of translation in weighted L¹ for the fixed
   kernel** (legitimate: `∫ w φ_σ < ∞` since Gaussians have finite moments of all
   orders). Note the kernel bandwidth `σ` and the cell size `δ` play *independent*
   roles: only `δ/σ → 0` is needed; no bandwidth–cell-size matching (that is only
   needed for sup-norm approximation, which we do not attempt).

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
   triples `(R, σ, δ)`. Every error term is `< ε/3`; assembly gives (3).

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

### Phase 2 — finite GMMs (the target; ~500–800 lines) — **PLANNED (execution-level breakdown below)**

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
(`weighted_modulus_tendsto_integrable`).** `G_f(u) := ∫ (1+‖x‖)·|f x − f (x−u)| dx → 0`
as `u → 0` for `f ≥ 0` integrable with finite first moment — the (T)-lemma WITHOUT
continuity; the one genuinely new analytic input. Core/tail architecture (Phase 1's
(T)-lemma with the core replaced by Mathlib's L¹ translation continuity):
* core: `∫_{‖x‖ ≤ R} |f x − f(x−u)| dx → 0` via the route identified in the Mathlib
  note (`Lp.instContinuousSMulDomMulAct`, Haar-measured finite-dim spaces — verify the
  exact lemma name/statement for `EuclideanSpace ℝ (Fin n)` + `volume` before
  committing; watch the `(−u) • f` sign convention vs. `f (x−u)`);
* tail: `setIntegral_tail_tendsto` for `(1+‖x‖)·f` + the translate-tail transport
  (Phase 1's threshold-shift trick: move the indicator INTO the transported function;
  `∫_{‖x‖>R}(1+‖x‖)|f(x−u)| ≤ (1+‖u‖)·tail(R−‖u‖)` via the `htri`-style
  `‖x‖ ≤ ‖x−u‖+‖u‖` bound);
* assembly: both `Filter.Tendsto G_f (𝓝 0) (𝓝 0)` (pointwise-in-`u` input for the DCTs)
  and the ε-δ form. The unweighted corollary `∫|f x − f(x−u)| → 0` follows by
  domination (`1 ≤ w`); the weighted form is needed for Step 1, the unweighted for
  nothing (Step 3 uses the (T)-lemma at `φ_1`, see below).

**Step 1 — smoothing for general `f` (`weighted_smoothing_integrable`).**
`∫ w·|f − f⋆φ_σ| → 0` as `σ → 0` (`f` integrable + finite first moment, NO continuity):
* Tonelli block: `(x,y) ↦ φ_σ(y)·(1+‖x‖)·|f x − f(x−y)|` integrable on the product
  (`∫∫ ≤ (2+‖y‖)·∫wf`-bound + `integrable_toLp_shift` — Phase 1 patterns), giving
  `∫ w|f − f⋆φ_σ| ≤ ∫ φ_σ(y)·G_f(y) dy`;
* σ→0 limit = the smoothing theorem's Step C pattern verbatim: transport
  `∫ φ_σ(y)·G_f(y) dy = ∫ φ_1(z)·G_f(σz) dz` via `integral_subst` (the
  `integral_mollifier_mul` transport), DCT against the fixed integrable dominator
  `(2+‖z‖)·∫wf` (for `σ ≤ 1`), pointwise limit `G_f(σz) → 0` from Step 0 + `σz → 0`
  (`tendsto_const_nhds.mul`-style composition + typed `Filter.Tendsto.congr`).

**Step 2 — lattice construction.**
* `latticeQ δ := fun t => δ • ⌊t/δ⌋` componentwise (`Real.floor` per coordinate on the
  `Fin n → ℝ` projection; watch the `WithLp` coercion care from Phase 1's shifts);
  `Measurable (latticeQ δ)` (measurability of `floor`-composed maps);
* displacement bound `‖latticeQ δ t − t‖ ≤ δ·√n`: per-coordinate
  `|δ·⌊tᵢ/δ⌋ − tᵢ| ≤ δ` (floor inequality manipulation), then the `n`-coordinate
  Euclidean norm bound (`EuclideanSpace.norm_eq` + squaring);
* the box: use the SUP-NORM box `B_R = {t | ∀ i, |t i| ≤ R}` (NOT the Euclidean ball —
  the `Finset` enumeration is then a `Finset.product` of finite `ℤ`-ranges via
  `Finset.range`/`Ico`, much cleaner); `B_R ⊆ {‖t‖ ≤ R·√n}`;
* the `Finset` `S(R,δ)` of lattice points in the box (only finiteness needed, not the
  count); cells `cell_j = latticeQ δ ⁻¹' {j} ∩ B_R` measurable;
* weights `W_j := ∫_{cell_j} f ∂volume` (`MeasureTheory.setIntegral`); the partition
  identity `∑_{j∈S} ∫_{cell_j} g = ∫_{B_R} g` for `g ≥ 0` (measurable finite partition
  `set_integral` lemmas — the voluminous bookkeeping the risk register flags).

**Step 3 — quantization estimate (`gmmApprox_quantization`).**
Split `f⋆φ_σ = ∫_{B_R} + ∫_{B_R^c}` at the box; with Step 4's identity:
`∫ w|f_K − f⋆φ_σ| ≤ ∫_{B_R} f(t)·weightedModulus n φ_σ (t − Q_δ t) dt
  + (1+σM)·[(1−c) + ∫_{B_R^c} w f]` — the first term via the Tonelli joint block
  (Phase 1 `ofReal` patterns) and the uniform displacement bound
  `‖t − Q_δ t‖ ≤ δ√n`; the tail term via `1 − c ≤ ∫_{B_R^c} w f`.
* **Scaled-modulus lemma** `weightedModulus_gaussian_scale`: with `x = σy`
  (`integral_subst` transport), `∫ w(x)|φ_σ(x+s) − φ_σ(x)| dx
  = ∫ (1+σ‖y‖)|φ_1(y+s/σ) − φ_1(y)| dy ≤ L₁(s/σ) + σ·(2M_1 + ‖s/σ‖)`, where
  `L₁(v) := ∫|φ_1(y+v) − φ_1(y)| dy ≤ weightedModulus n φ_1 v` — so `L₁(s/σ) → 0`
  by the ALREADY-PROVEN `weighted_modulus_tendsto_seq` at `f := φ_1`
  (`φ_1` is a continuous pdf with finite first moment: `isPdf_multivariateGaussianPDF`,
  `integrable_norm_mul_gaussianPDF_center`), and `σ·(2M_1 + ‖s/σ‖) → 0` along
  `s = δ_K√n`, `σ = σ_K` since `δ_K/σ_K = σ_K → 0`. NOTE: this corrects the old
  deliverable "`weighted_translation_cont` (from Phase 1) reused" — Phase 1 never
  formalized that lemma; the kernel's modulus is covered by the existing (T)-lemma,
  and the general-`f` modulus is Step 0.

**Step 4 — the integral identity (`gmmApprox_integral_identity`).**
`∑_{j∈S} W_j·φ_σ(x−j) = ∫_{B_R} f(t)·φ_σ(x − Q_δ t) dt`: the integrand
`φ_σ(x − Q_δ t)` is constant = `φ_σ(x−j)` on each cell, so the identity is the same
measurable-partition `set_integral` machinery as Step 2 (per-cell pull-out + `Finset`
sum). This is what makes the quantization term a single Tonelli block rather than a
sum of cell estimates.

**Step 5 — `IsPdf (gmmApprox f R σ δ)` (`isPdf_gmmApprox`).**
Nonnegativity (both terms; `1 − c ≥ 0` from `c ≤ 1`); mass
`∑_{j∈S} W_j + (1 − ∑_{j∈S} W_j) = 1` via `integral_finsetSum` +
`integral_gaussianPDF` (`∫ φ_σ = 1`) + `mul_one`, with the partition identity at
`g = f` for `∑ W_j = c`. Measurability: finite sum of measurable (Gaussian-shift)
terms — Phase 0's `gmmPDF` measurability pattern.

**Step 6 — the sequence + diagonal (`gmmPriorSeq`) and `hw`.**
`fhK K := gmmApprox f (K+1) (1/(K+1)) (1/(K+1)²)`. Triangle:
`∫ w|f − fhK K| ≤ [smoothing @ σ_K] + [quantization @ (σ_K, δ_K)] + [no third term —
the tails were folded into the quantization estimate's budget]`. Each term is
eventually `< ε` (or `< ε/2` each): smoothing by Step 1 (`σ_K → 0`), quantization by
Step 3 (`σ_K → 0`, `δ_K/σ_K = σ_K → 0`). Then the `hw` conversion — the Phase 1
`hw_smoothedPriorSeq` pattern VERBATIM: per-K `Integrable w·|f − fhK K|` by
domination (`|f − f_K| ≤ f + f_K`, both weighted-integrable: `f` via
`hfi.add hfmom`-style, `f_K` via the weighted-mass computation in the design-decisions
block), `ofReal_integral_eq_lintegral_ofReal` bridge,
`(ENNReal.ofReal_lt_ofReal_iff hε).mpr`.

**Step 7 — the corollary (`cme_uniform_balls_gmm_prior_general`).**
`cme_uniform_balls_R m n S hS A f hpdf hfmom gmmPriorSeq (fun K => isPdf_gmmApprox …)
(hw_gmmPriorSeq …) r hr` — the Phase 1 corollary pattern
(`cme_uniform_balls_smoothed_prior`), with the defeq/proof-irrelevance care for the
sequence arguments.

**Deliverables checklist:**
* `weighted_modulus_tendsto_integrable` (Step 0), `weighted_smoothing_integrable` (Step 1)
  — the two new analytic lemmas.
* `latticeQ` + geometry, `S`/`W`/cells + partition identity (Step 2),
  `gmmApprox_integral_identity` (Step 4).
* `gmmApprox` def + `isPdf_gmmApprox` (Steps 3/5), `gmmApprox_quantization` (Step 3).
* `gmmPriorSeq` + `hw_gmmPriorSeq` (Step 6), `cme_uniform_balls_gmm_prior_general`
  (Step 7).
* The **GMM density theorem** (statement at the top of this file) is exactly the
  ∫-form of Step 6's convergence; state it as a corollary of the same assembly.
* `AxiomCheck.lean` audits for every new public theorem (Phase 1 convention).
* Follow the Phase 1 file layout: public defs/lemmas in `ApproximationByGMM.lean`,
  appended in dependency order.

**Risk register (updated):** (a) the L^p-translation-continuity Mathlib route (Step 0
core) — verify the exact lemma name/statement for `EuclideanSpace` + `volume` FIRST;
if the weighted form resists, fall back to the unweighted L¹ route + the Phase 1 tail
architecture (the original `weighted_translation_cont` shape). (b) the
measurable-partition `set_integral` bookkeeping (Steps 2/4) — voluminous but standard;
no new math. (c) the diagonal assembly (Step 6) — keep the ε-budgets as explicit named
`have`s; the ordering σ → R → δ within each `K` mirrors the Proof-strategy section.
(d) `Real.floor` manipulation under `WithLp` coercions (Step 2) — expect the usual
coercion gotchas; do the geometry on the `Fin n → ℝ` projection first.

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


**Phase 2 Step 0 status (this session):**

DONE and verified: `modulus_tendsto_integrable` (unweighted L¹ translation continuity for
integrable `f`, no continuity needed) — via Mathlib's continuous `DomAddAct` action on
`Lp ℝ 1 volume`: `DomAddAct.mk u +ᵥ MemLp.toLp f hmem` has coerced function a.e.
`fun x => f (u +ᵥ x)`, and the `L¹` distance of the action translate computes to the
unweighted translation modulus via `L1.dist_def` + `edist_dist` + the a.e. chain
(`MemLp.coeFn_toLp`, `DomAddAct.vadd_Lp_ae_eq`,
`hmp.quasiMeasurePreserving.ae_eq_comp`). Full build was green with it.

IN PROGRESS: `weighted_modulus_tendsto_integrable` (the weighted Step 0 lemma) — the
architecture is fully drafted in the file (core = the unweighted lemma scaled by (1+K) on
the ball; tails = `setIntegral_tail_tendsto` at K with the threshold-shift transport via
`integral_toLp_trans_right`; budgets ε/2 + ε/8 + ε/4). ~15 mechanical form-alignment
errors remain, all of the `+ᵥ`/`toLp`/beta/defeq kind catalogued below, no mathematical
obstacles.

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
7. `(K - 1 : ℕ) : ℝ` vs `↑K - 1` cast mismatch: use `K₁` directly (K := K₁ + 1) instead
   of `K - 1`.
8. In this module-Mathlib, `Real.instAdd` etc. are NOT exposed for `whnf` defeq unfolding:
   any defeq check that must look inside a real sum FAILS. All Real-arithmetic identities
   must be propositional (`ring`/`linarith` with `hexp`-style rewrites).
9. abs-indicator integrand statements: count parens by generating the line from the
   verified `hWint` statement template (y-substituted), never by hand.
