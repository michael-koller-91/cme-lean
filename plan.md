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

3. **Mixtures are pdfs.** `∫ f_K = ∑_j w_j = ∫_{box} f`, plus the tail argument below,
   give `IsPdf (f_K)`. The nonnegativity is immediate; the mass computation is a finite
   sum of `∫ φ_σ = 1` terms (via `integral_multivariateGaussianPDF_one`).

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

### Phase 1 — continuum-mixture sequence (~150–250 lines) — **IN PROGRESS**

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

### Phase 2 — finite GMMs (the target; ~500–800 lines)

The smoothing–quantization construction above: lattice cells, cell weights, finite-sum
bookkeeping, tail control, diagonalization.

Deliverables:
* `weighted_translation_cont` (from Phase 1) reused.
* The lattice construction: `Q_δ`, measurable cells, `Finset` of lattice points in a
  box, weights as integrals over cells; measurability and `IsPdf` of the mixture.
* The quantization estimate and the moment/tail bounds.
* The full **GMM density theorem** (statement at the top of this file).
* Final corollary: for every pdf prior with finite first moment, the GMM sequence
  satisfies `hw`, hence (by `cme_uniform_balls_R`) the GMM-based CMEs converge to the
  true CME locally uniformly.

Risk register: the fiddliest parts are (a) defining the lattice partition measurably
and doing the finite-sum/integral interchanges, and (b) the tail estimates outside the
covered box. Both are routine but voluminous; neither involves new mathematical ideas.

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
