# Plan for proving the uniform convergence of `f_y^{(K)}` to `f_y`

## Goal

Formalize in Lean the statement from `appendix_1.tex` (lines 52–84, first part of the proof of
`thm:main_result`): let

* `h` be a random variable with a continuous pdf `f_h` that vanishes at infinity
  (`f_h ∈ C₀`),
* `h^{(K)}` be random variables with pdfs `f_h^{(K)}`,
* `f_h^{(K)}` converge uniformly to `f_h` — **assumed**, not constructed. (Gaussian mixture
  models are the motivating example: by Theorem 5(a) of *Approximation by finite mixtures of
  continuous density functions that vanish at infinity* (Nguyen–Nguyen–Chamroukhi–McLachlan,
  2020) such a uniformly convergent sequence of GMMs exists for any `f ∈ C₀` pdf — but GMMs
  play no role in the formalization and are not used anywhere),
* `n ~ N(0, S)` be independent Gaussian noise,
* `y = A h + n` and `y^{(K)} = A h^{(K)}`, with pdfs `f_y` and `f_y^{(K)}`.

Conclude: `f_y^{(K)}` converges uniformly to `f_y`, where
`f_y(y) = ∫ f_n(y − A h) f_h(h) dh` (appendix Eq. (convolution) after the change of variables
`s = y − A h`), and analogously for `f_y^{(K)}`.

## What already exists in `Main.lean` (and gets reused)

The end of `Main.lean` already contains the mathematical core of the appendix argument:

* `noiseDens` — the noise density `f_n(y − A h)` evaluated along `h ↦ y − A h`.
* `fyPDF n S hS A f y := ∫ noiseDens n S hS A y h * f h ∂volume` — the observation density
  `f_y` induced by any measurable `f` playing the role of `f_h` (this is exactly the appendix's
  convolution formula after the change of variables `s = y − A h`).
* `integral_subst_unit` / `integral_noise_pullback` — `∫ f_n(y − A h) dh = |det A|⁻¹`.
* `multivariateGaussianPDF_le_const` — the Gaussian density is bounded by its normalizing
  constant (used for domination).
* **`uniform_convergence_fy`** (the last theorem in the file) — the uniform convergence transfer
  itself, already fully proved: given
  `hfh : Integrable fh volume`, `hfhK : ∀ K, Integrable (fhK K) volume`, and
  `hconv : ∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∀ x, |fh x − fhK K x| < ε`,
  it concludes `∃ K₀, ∀ K ≥ K₀, ∀ y, |fyPDF … fh y − fyPDF … (fhK K) y| < ε`.
  This is the appendix's chain (appendix lines 71–84), in ε-form instead of the closed-form
  bound `≤ ‖f_h − f_h^{(K)}‖_∞ / |det A|`.

So the uniform convergence statement is *already proved at the right level of generality*
("only integrability of the densities is assumed"). The remaining work is entirely about
**setting up the setting** described above:

1. define the predicates "is a pdf" and "vanishes at infinity";
2. discharge the integrability side conditions of `uniform_convergence_fy` from these predicates;
3. (requested, separable) connect `fyPDF` to the actual random variables `h`, `h^{(K)}`, `n`,
   `y = A h + n`, `y^{(K)} = A h^{(K)}` — i.e. prove that `f_y` and `f_y^{(K)}` really are the
   pdfs of `y` and `y^{(K)}`.

## Formalization design

### Predicates (new definitions, `Main.lean` after `uniform_convergence_fy`)

```lean
/-- `f` is a probability density function w.r.t. `volume` on `EuclideanSpace ℝ (Fin n)`. -/
def IsPdf (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  0 ≤ f ∧ ∫ x, f x ∂volume = 1

/-- `f` vanishes at infinity: `f x → 0` as `‖x‖ → ∞`. On the proper space
`EuclideanSpace ℝ (Fin n)`, `Tendsto f atTop (nhds 0)` is exactly this. -/
def VanishesAtInfinity (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Tendsto f atTop (nhds 0)
```

Notes:

* `IsPdf` is deliberately minimal (nonneg + integral 1). Continuity and vanishing at infinity
  are *separate* hypotheses on `f_h` (matching the appendix setting: `f_h ∈ C₀` pdf), because
  the pdf property alone is what provides integrability — for both `f_h` and every
  `f_h^{(K)}` — and `uniform_convergence_fy` needs neither continuity nor vanishing.
* No GMM predicate is defined; the approximating sequence is axiomatized purely through the
  uniform convergence assumption `hconv` plus the requirement that each `f_h^{(K)}` is itself a
  pdf.
* Keep the predicates over plain `ℝ`-valued functions on `EuclideanSpace ℝ (Fin n)`, consistent
  with `fyPDF`, `noiseDens`, and `uniform_convergence_fy`. Handle `WithLp`/plain-function
  friction at the *instantiation sites* (see the existing `hcast` trick in
  `integral_normalized_gaussian_bounded`), not inside the predicates.

### Final theorem statement

```lean
theorem uniform_convergence_fy_pdf
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh)                    -- f_h is a pdf
    (hfhcont : Continuous fh)              -- … continuous …
    (hfh0 : VanishesAtInfinity fh)         -- … and vanishes at infinity (f_h ∈ C₀)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K))         -- every f_h^{(K)} is a pdf
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
      -- the uniform convergence assumption; motivated by Theorem 5(a) (GMM sequences),
      -- but assumed abstractly, with no reference to GMMs
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ y : EuclideanSpace ℝ (Fin n),
      |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| < ε
```

The proof is `uniform_convergence_fy n S hS A hA fh hIntegrable fhK hIntegrableK hconv ε hε`
where the two integrability arguments are discharged by Step 1 below.

## Step 1 — Integrability from the pdf property (both sides)

`hfh : Integrable fh volume` and `hfhK K : Integrable (fhK K) volume` follow *directly* from
`IsPdf`:
`∫ |f| = ∫ f = 1` since `f ≥ 0`.

**Lean:** `integrable_of_integral_eq_one`-style lemma, or inline:
`hfint : ∫ x, f x ∂volume = 1`, then
`Integrable.of_integral_ne_zero` + `integral_abs_of_nonneg` (or
`MeasureTheory.Integrable` via `∫|f| = ∫f` when `0 ≤ f`: `integral_abs_of_nonneg`).
No continuity/vanishing needed here — and the same argument covers *every* member of the
sequence `f_h^{(K)}` uniformly, since each is assumed to be a pdf.

## Step 2 — Assemble the final theorem

`uniform_convergence_fy_pdf` is now pure glue (~5 lines): apply Step 1 to `fh` and to each
`fhK K`, and apply the existing `uniform_convergence_fy`. The uniform convergence statement of
`appendix_1.tex` (lines 52–84) is thereby fully formalized.

## Step 3 (requested, separable) — `f_y` and `f_y^{(K)}` are the pdfs of `y` and `y^{(K)}`

**STATUS: COMPLETE (all proved in `Main.lean`, compiles clean, no `sorry`).** Delivered
theorems, in file order:

1. `integral_toLp_trans` — left-translation invariance of `volume` integrals on
   `EuclideanSpace ℝ (Fin n)`, for any complete-normed codomain `F` (used for both the ℂ
   characteristic-function computation and the ℝ-valued mass computation).
2. `lintegral_toLp_trans` — the ℝ≥0∞ version.
3. `lintegral_noiseDens_mass` — for fixed `h`, `y ↦ f_n(y − A h)` has mass `1`
   (translation by `−A h`).
4. `lintegral_enorm_noiseDens_mul` — Tonelli on the coupled integrand
   `(y, h) ↦ f_n(y − A h) f(h)`: the `ℝ≥0∞`-norm integral over `volume.prod volume`
   equals `1` (both factors have infinite mass, so this is the nontrivial step).
5. `charFun_fyPDF_density` — density-side factorization:
   `charFun (volume.withDensity (fun y => ENNReal.ofReal (fyPDF …))) t
      = (∫ h, e^{i⟨A h, t⟩} * f h) * charFun μn t`.
   Key steps: `f' := hfint.aemeasurable.mk f` (measurable representative, needed for
   `StronglyMeasurable.integral_prod_left`), per-`y` `integral_const_mul`, Fubini swap
   dominated by item 4 via `Integrable.mono'`, per-`h` translation of
   `∫ y, φ y * ↑f_n (y − A h)` with `φ y = φ (y − A h) * e h`, and
   `integral_ofReal` (`∫ ↑g = ↑∫ g`) to move the ℝ→ℂ coercion across the inner integral.
6. `isPdf_fyPDF` — `f_y` is a pdf: nonnegative pointwise; mass `1` by Fubini on the
   ℝ-valued integrand (`integral_integral_swap`) plus the per-`h` translation
   `∫ y, f_n(y − A h) dy = 1`.
7. `fyPDF_eq_map` — assembly: both sides are finite measures
   (`isFiniteMeasure_withDensity` on the right, using mass `1` from item 6; map/prod
   finiteness instances on the left) with equal characteristic functions
   (`charFun_map_fy` and item 5), so `Measure.ext_of_charFun` applies.

Lean pitfalls learned along this step (keep for future work): `calc` continuation items
must be indented strictly *less* than the first item's `=` when a middle item carries a
`:= by`-newline proof (inline `:= by rw […]` or the law-side indentation works); a `by`
proof on its own line in a *middle* calc item otherwise derails the parser; `rw` cannot
rewrite inside a variable-shadowing beta-redex (`(fun h => …) h`) — insert a `show` that
beta-reduces first; `Measurable.comp` against a metavariable `?f` loops at `whnf` on
`EuclideanSpace` when the expected type is a curried lambda — instead give the concrete
`∘`-form as the `have`'s type annotation and convert with `funext … ; simp [Function.comp]`;
`RCLike.norm_ofReal` matches only via term-mode (concrete `have`s) in `rw` chains;
`integral_const_mul`/`integral_mul_const`/`lintegral_mul_const` need explicit
`(μ := volume)` in bare `have :=` terms; `set_option … in` cannot follow a docstring —
the docstring goes between `set_option … in` and the declaration.

Original plan text follows.

Goal: identify `volume.withDensity (fun y => ENNReal.ofReal (fyPDF … fh y))` with the law of
`y = A h + n`, where the law of `h` is `μ_h = volume.withDensity (fun x => ENNReal.ofReal (fh x))`
and the law of `n` is `μ_n = multivariateGaussian (WithLp.toLp 2 (0 : Fin n → ℝ)) S`:

```
(law of y) = map (fun p : Ω_h × Ω_n => A • p.1 + p.2) (μ_h.prod μ_n)
           = volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A fh y))
```

Prove it **generically** for any measurable `f` with `IsPdf f` (one lemma, instantiated twice:
`f := fh` and `f := fhK K`).

Recommended route: **characteristic functions**, mirroring the existing pattern
(`stdGaussian_eq_withDensity`, `multivariateGaussian_eq_withDensity` use
`Measure.ext_of_charFun`).

1. `charFun` of the density side:
   `∫ y, e^{i⟨t, y⟩} • fyPDF y ∂volume`
   `= ∫ y ∫ h, e^{i⟨t, y⟩} * f_n(y − A h) * f(h) dh dy` (unfold `fyPDF`).
   Substitute `s = y − A h` **for fixed `h`**: `y ↦ s = y − A h` is a *translation*, so
   `dy = ds` and `e^{i⟨t, y⟩} = e^{i⟨t, s⟩} · e^{i⟨t, A h⟩}`. This avoids any determinant
   bookkeeping (unlike the appendix's general linear-change-of-variables, translation invariance
   is trivial in Mathlib: `MeasureTheory.map_add_left_eq_self`, already used in
   `integral_subst`/`integral_subst_unit`). Result:
   `∫ h, e^{i⟨t, A h⟩} * f(h) dh • ∫ s, e^{i⟨t, s⟩} * f_n(s) ds`
   `= charFun (map (A ·) μ_h) t * charFun μ_n t`.
2. `charFun` of the law side: on the product measure `μ_h.prod μ_n` the coordinates are
   independent; `charFun` of the pushforward along `p ↦ A • p.1 + p.2` factorizes into
   `charFun (map (A ·) μ_h) * charFun μ_n`.
   Search Mathlib for: `charFun_map`, `IndepFun`, `charFun_indepFun_add`,
   `ProbabilityTheory.charFun_indepFun`, `Measure.prod` pushforward lemmas
   (`Measure.map_prod`, `integral_prod`/Fubini via `MeasureTheory.integral_prod`).
   If no ready-made factorization lemma exists, prove it directly:
   `charFun (map (fun p => A • p.1 + p.2) (μ.prod ν)) t`
   `= ∫ p, e^{i⟨t, A p.1 + p.2⟩} ∂(μ.prod ν)` (definition, needs `charFun_apply` +
   `integral_map`), then Fubini + `exp` addition + `integral_prod`
   (`= ∫∫ … dμ dν`), then split the integrand and pull out the integrals — same shape as the
   density-side computation, so both halves of the identification are essentially the same
   Fubini computation and can share the pointwise `exp`-splitting lemmas.
3. Conclude with `Measure.ext_of_charFun` (already used twice in `Main.lean`).

Side conditions to keep in mind (all have working precedents in `Main.lean`):

* `μ_h` is a probability measure: `∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1` — copy the `hlint`
  pattern from `stdGaussian_eq_withDensity` /
  `isFiniteMeasure_gaussianPDF_withDensity` (`ofReal_integral_eq_lintegral_ofReal`).
* The `WithLp` friction: `multivariateGaussian` takes `EuclideanSpace ℝ (Fin n)` arguments;
  expect the same `WithLp.toLp` bridging as in `integral_normalized_gaussian_bounded`
  (`hcast`, `hEqL` tricks).
* Nonnegativity of `fyPDF … f` (needed so that `ofReal` is well-behaved): both `noiseDens ≥ 0`
  (`hposa` pattern in `uniform_convergence_fy`) and `f ≥ 0` (`IsPdf f`) give it pointwise.

Deliverables of Step 3:

```lean
theorem fyPDF_is_pdf_of_map
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) (hfm : Measurable f) :
    volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A f y))
      = map (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) + p.2)
            (…withDensity f…).prod (multivariateGaussian …)
```

(where `A • p.1` means the linear map `h ↦ A h` through `Matrix.toEuclideanLin`, matching how
`multivariateGaussian` handles linear maps; adjust to whatever shape makes the `Measure.map`
composition work smoothly — the *content* is the charFun factorization, the plumbing around
it is flexible.)

Optionally, if Mathlib's `MeasureTheory.HasPDF`/`Measure.pdf` API (`Measure.pdf`,
`HasPDFAt`) turns out to fit better, state the result as
`(map … …).HasPDF (fun y => fyPDF … f y) volume` — but the raw `withDensity` equality is the
more robust target given the codebase's style.

## Suggested lemma ordering in `Main.lean`

Per repo convention (standalone content-bearing lemmas with their own `sorry` while debugging,
verified in isolation with `lake env lean Main.lean`, inline glue in the final theorem):

1. `IsPdf`, `VanishesAtInfinity` (definitions; no proofs).
2. `integrable_of_isPdf` (Step 1 — three lines; may stay inline in the final theorem).
3. `uniform_convergence_fy_pdf` (Step 2 — glue).
4. `charFun_withDensity_fyPDF` (Step 3, part 1: the Fubini + translation computation on the
   density side).
5. `fyPDF_is_pdf_of_map` (Step 3, part 2: charFun factorization for the law side + assembly).

Ordering rationale: Steps 1–2 are independent of Step 3 and complete the goal as literally
stated in `appendix_1.tex`; Step 3 upgrades the statement to genuine random variables and can
proceed (or fail Mathlib-hunting) without blocking the rest.

## Risks and known Mathlib gaps

* **Step 3 is the only part with real Mathlib risk.** The density-side Fubini/translation
  computation should be fine (all ingredients have working precedents in `Main.lean`). The
  law-side charFun factorization over a product measure needs checking against current
  Mathlib (`charFun_indepFun_add` / `IndepFun` API); worst case, prove it by hand from
  `charFun_apply` + `integral_map` + `integral_prod` — no new mathematics, just Fubini.
* `Continuous fh` + `VanishesAtInfinity fh` ⇒ `Bounded` is **not needed** for the uniform
  convergence statement (it is needed later for `M_2` in the CMME part of the appendix,
  lines 145–149). If wanted anyway: obtain `R` with `|f x| ≤ 1` for `‖x‖ ≥ R` from the
  `Tendsto`, take the max of `|f|` on the compact ball `{‖x‖ ≤ R}` (`Continuous.max` on
  compact / `IsCompact.exists_forall_le` — note continuity on the *closed* ball suffices,
  consider `ContinuousOn` + `IsCompact.exists_forall_le_of_continuousOn`).
* Do **not** try to derive `Integrable fh` from continuity + vanishing at infinity — that is
  false in general (e.g. `f(x) = (1+‖x‖²)^{-p}` with `p ≤ n/2`); the pdf property
  (`∫ f = 1`, `f ≥ 0`) is what carries integrability — for `f_h` and for every `f_h^{(K)}`
  alike.

## Out of scope (for later)

* The construction of any concrete uniformly convergent sequence `f_h^{(K)}` — in particular
  GMM sequences and the proof of Theorem 5(a). GMMs serve only as motivation for the
  assumption `hconv`; nothing in the formalization mentions them.
* The second half of the appendix (lines 86–182: the CMME convergence
  `ħ(y) − ħ^{(K)}(y) → 0` via `Lemma bound_norm`, the fraction bound (common denominator),
  and the constants `N₁,…,N₅`, `M₁,M₂,M₃`). Note in passing: `Lemma bound_norm`'s content
  (the expectation bound `∫ ‖h‖ f_n(y − A h) dh ≤ …`) is precisely what
  `integral_gaussian_bounded` / `integral_normalized_gaussian_bounded` at the *end of the
  integrability section* of `Main.lean` already provide in `Integrable` form — a good
  starting point for that follow-up.
* Positivity of `f_y`, `f_y^{(K)}` (appendix line 69): easy once Step 3 exists (product of
  nonnegative factors, integral of a nonnegative function is ≥ 0); not needed for the
  uniform convergence statement itself.
