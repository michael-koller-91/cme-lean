# Plan for proving `integral_norm_gaussian_bounded`

Goal (as stated in `Main.lean`): `Integrable` of `h ↦ ‖h‖ * multivariateGaussianPDF n 0 S hS (y - A h) * c`
w.r.t. `volume` on `EuclideanSpace ℝ (Fin n)`, where `c = 1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)`.

Strategy: recognize the weighted density as the Gaussian PDF with mean `μ̃ = A⁻¹ y` and
covariance `Σ̃ = A⁻¹ S A⁻ᵀ` (the computation in `appendix_1.tex`), identify the measure with this
density as the multivariate Gaussian measure `multivariateGaussian μ̃ Σ̃`, and finish with Fernique's
theorem. Keep the statement in `Integrable` form — for ℝ-valued integrands `∫ … ∂μ` is defined to be
`0` when the integrand is not integrable, so `∃ C, ∫ … ≤ C` would be trivially true.

## Lemma structure

Do **not** make all five steps into lemmas. Make the three content-bearing ones standalone lemmas
(each with its own `sorry`, stated in `Main.lean` above the theorem, so each can be verified and
debugged in isolation), and keep Steps 4–5 as inline glue in the theorem's proof:

* `density_id` (Step 1): `c * multivariateGaussianPDF n 0 S hS (y - A·h) = multivariateGaussianPDF n (A⁻¹·y) Σ̃ hΣ̃ h`.
  Pure matrix algebra; no measure theory.
* `stdGaussian_eq_withDensity` (Step 2): `stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity (fun x => (2π)^(-card ι / 2) * Real.exp (-‖x‖^2 / 2))`
  for any finite `ι` — the "pdf of the standard Gaussian" lemma Mathlib is missing; state it
  generally (arbitrary finite `ι`) so it is reusable and upstreamable.
* `multivariateGaussian_eq_withDensity` (Step 3, **generalized**): `multivariateGaussian μ S = volume.withDensity (fun x => multivariateGaussianPDF n μ S hS x)`
  for positive (semi)definite `S` — the general missing density lemma, not the special case
  `μ̃, Σ̃`. The theorem then instantiates it at `μ̃, Σ̃`.
* Steps 4–5 (withDensity bridge + Fernique) stay inline in the final proof: they are 2-line
  applications of `integrable_withDensity_iff_integrable_smul₀'` + `integrable_congr` and
  `IsGaussian.integrable_id` + `Integrable.norm`; wrapping them in lemmas would only duplicate the
  bookkeeping.

With the three lemmas in place, the proof of `integral_norm_gaussian_bounded` should be a short
corollary-style argument (~10 lines).

## Step 1 — Density identification

Prove the pointwise equality of functions (pure matrix algebra, no measure theory):
`fun h => c * multivariateGaussianPDF n 0 S hS (WithLp.toLp 2 (y - A h))`
`  = fun h => multivariateGaussianPDF n (A⁻¹ y) (A⁻¹ S A⁻ᵀ) hΣ̃ (WithLp.toLp 2 h)`,
i.e. the appendix computation: expand the exponent
`(y - A h)ᵀ S⁻¹ (y - A h) = (h - A⁻¹ y)ᵀ (Aᵀ S⁻¹ A) (h - A⁻¹ y)` and use `Σ̃⁻¹ = Aᵀ S⁻¹ A`
and `det(A⁻¹ A⁻ᵀ) = (det A)⁻²` to match the normalizing constant.

**Lean:** first construct `hΣ̃ : (A⁻¹ S A⁻ᵀ).PosDef` from `hS` and `hA` (`Matrix.PosDef.mul`,
noting `(A⁻¹)ᵀ = (Aᵀ)⁻¹`); then prove the equality as a standalone lemma (e.g.
`density_id : ∀ h, c * multivariateGaussianPDF n 0 S hS (y - A·h)
  = multivariateGaussianPDF n (A⁻¹·y) Σ̃ hΣ̃ h`) by `simp`/`ring`-style manipulation of
`Matrix.mulVec`, `det_mul`, `det_transpose`, `det_inv` and `Matrix.PosDef.det_pos`.

## Step 2 — Integral equals expectation

Build the bridge from Lebesgue integrals over `volume` to integrals against a Gaussian measure
whose density w.r.t. `volume` is the Step-1 function. Note: the pinned Mathlib has **no**
ready-made lemma `pdf (multivariateGaussian μ S) = …`, so this bridge must be built here, starting
from the standard Gaussian.

**Lean:** prove `stdGaussian (EuclideanSpace ℝ (Fin n)) = volume.withDensity (fun x => (2π)^(-n/2) * Real.exp (-‖x‖^2 / 2))`
via `Measure.ext_of_charFun` (or `gaussian_charFun_congr`): the charFun of the density measure is
`∫ exp (I * ⟪t, x⟫) * (2π)^(-n/2) * exp (-‖x‖^2 / 2) ∂volume`, which is exactly Mathlib's Gaussian
Fourier integral `integral_cexp_neg_mul_sq_norm_add` (file
`Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean` — add the import) with `b = 1/2`
and `c = I`; compare with `charFun_stdGaussian`. The Pi/`WithLp` conversions are handled by
`PiLp.volume_preserving_toLp`-style equivs; dot products via `PiLp.inner_apply`.

## Step 3 — Pushforward measure

Identify the target measure as the affine image of the standard Gaussian:
by the *definition* of `multivariateGaussian`, `multivariateGaussian μ̃ Σ̃ = (stdGaussian …).map (fun x => μ̃ + toEuclideanCLM (CFC.sqrt Σ̃) x)`;
correspondingly transport the Step-1 density under the same affine map to conclude
`volume.withDensity (fun h => multivariateGaussianPDF n μ̃ Σ̃ hΣ̃ h) = multivariateGaussian μ̃ Σ̃`.

**Lean:** use the change of variables for affine maps on Haar measure: `map_linearMap_addHaar_eq_smul_addHaar`
(linear part rescales `volume` by `|det|`, here `|det (CFC.sqrt Σ̃)| = √det Σ̃`), translation
invariance of `volume`, and `Measure.map_map`; the square root satisfies
`(CFC.sqrt Σ̃) * (CFC.sqrt Σ̃)ᵀ = Σ̃` by `CFC.sqrt_mul_sqrt_self` (Σ̃ is symmetric positive
definite), which makes the transported density exactly the Step-1 function. Matrices ↔ continuous
linear maps go through `toEuclideanCLM` (that is what `multivariateGaussian` uses internally).

## Step 4 — Integral equals first moment

With Steps 1–3, the goal `Integrable (fun h => ‖h‖ * …density…) volume` becomes precisely the
statement that the first moment of the Gaussian measure `ν₂ := multivariateGaussian μ̃ Σ̃` is finite.

**Lean:** use the `withDensity` bridge
`integrable_withDensity_iff_integrable_smul₀'` (`L1Space/Integrable.lean`, ℝ≥0∞-valued density,
needs `AEMeasurable` and density < ∞ a.e.): `Integrable g (volume.withDensity f̃) ↔ Integrable (fun x => f̃ x • g x) volume`;
take `g = ‖·‖` and match `fun h => multivariateGaussianPDF … * ‖h‖` with the original integrand via
Step 1 and `integrable_congr` (the density is strictly positive, hence finite a.e.).

## Step 5 — Finite first moment (Fernique)

`ν₂` is a Gaussian measure (`isGaussian_multivariateGaussian` instance), so Fernique's theorem
applies directly to it and the first moment is finite.

**Lean:** `IsGaussian.integrable_id (μ := ν₂) : Integrable id ν₂` (from
`Mathlib.Probability.Distributions.Gaussian.Fernique`), then `Integrable.norm` gives
`Integrable (fun z => ‖z‖) ν₂`; chain with Steps 3–4 to close the goal.

## Verification

Work one lemma at a time, keeping the others as `sorry`s; `lake env lean Main.lean` tells you which
declarations still have `sorry` warnings, and `#print axioms <lemma>` confirms a lemma is complete
(no `sorryAx`). After filling everything, run `lake env lean Main.lean` to confirm the proof
compiles; success means no errors (warnings such as unused variables are fine). If a step fails,
isolate it as a private lemma first and debug it separately.

## Status (updated 2026-11-10)

**Step 1 is DONE (proved in `Main.lean`, verified with `lake env lean Main.lean`).**

Lemmas proved in `Main.lean`:

* `transpose_nonsing_inv (hA : IsUnit A.det) : (Aᵀ)⁻¹ = (A⁻¹)ᵀ` — helper, by
  `Matrix.inv_eq_right_inv` of `Aᵀ * (A⁻¹)ᵀ = 1`.
* `sigmaTilde_posDef` — via `Matrix.posDef_iff_posSemidef_and_mulVec_injective`:
  PosSemidef part from `Matrix.IsUnit.posSemidef_star_left_conjugate_iff hTU`
  (with `star ((A⁻¹)ᵀ) = A⁻¹` by `ext; simp`); mulVec-injectivity chains
  `(A⁻¹)ᵀ`, `S`, `A⁻¹` injectivity via `congrArg` + `Matrix.mulVec_mulVec`.
* `quadForm_eq (hSdet) (hA) u w : ((Σ̃)⁻¹ *ᵥ (u - A⁻¹·w)) ⬝ᵥ (u - A⁻¹·w)
  = (S⁻¹ *ᵥ (w - A·u)) ⬝ᵥ (w - A·u)` — via the sandwich product `h1` (calc with
  `mul_assoc`/`nonsing_inv_mul`), `Matrix.inv_eq_left_inv h1`, then
  `mulVec_mulVec`/`dotProduct_comm`/`dotProduct_transpose_mulVec`/`mulVec_sub`/
  `mulVec_neg`/`neg_dotProduct_neg`.
* `density_id` — helper scalar facts `hSigdet : (A⁻¹ S A⁻ᵀ).det = S.det / (A.det)²`,
  `hAdet2`, `hAdetc : 1 / √((A⁻¹ A⁻ᵀ).det) = |A.det|`, and
  `hKey : c * ((2π)^((n:ℝ)/2) * √S.det)⁻¹ = ((2π)^((n:ℝ)/2) * √(A⁻¹ S A⁻ᵀ).det)⁻¹`
  (proved by `rw [hAdetc, hSigdet, Real.sqrt_div, Real.sqrt_sq_eq_abs]; field_simp [hZne, hSdne, hAbsne]`),
  then tail: `simp only [multivariateGaussianPDF, sub_zero]; rw [quadForm_eq …];
  rw [← mul_assoc c ((2π)^((n:ℝ)/2) * √S.det)⁻¹, hKey]`.

Key gotchas discovered (important for future steps):

1. `(2 * Real.pi) ^ (↑n / 2)` in a typed-ℝ context elaborates the exponent as
   `n / 2 : ℕ` (instance `HPow Real Nat Real` via `Monoid.toNPow`), i.e. an **integer** power,
   NOT `Real.rpow`. The PDF's `((n : ℝ) / 2)` exponent is `rpow`. Writing `↑n / 2` caused
   silent rewrite mismatches. Always write the exponent as `((n : ℝ) / 2)`.
2. `norm_num` LOOPS (deterministic timeout / heartbeat exhaustion) when asked to prove
   `0 < 2 * Real.pi` (it tries to compute `Real.pi`). Use `positivity` instead — it has a
   dedicated hook for `Real.pi` (`Real.rpow_pos_of_pos` extension). Unknown identifiers +
   `autoImplicit` also masquerade as massive elaboration timeouts.
3. `mul_assoc : a * b * c = a * (b * c)`; goal `c * (X * E)` reproduces with `← mul_assoc`
   with **explicit** first two args; bare `mul_assoc` as rewrite matches unrelated matrix
   products.
4. In `density_id`, no sign juggling needed: `simp only [multivariateGaussianPDF, sub_zero]`
   produces LHS quad `(S⁻¹ *ᵥ (y - A·h)) ⬝ᵥ (y - A·h)` and RHS quad
   `((Σ̃)⁻¹ *ᵥ (h - A⁻¹·y)) ⬝ᵥ (h - A⁻¹·y)` — exactly `quadForm_eq u w` with `u := h, w := y`.
5. `WithLp.ofLp_toLp` is not needed in the tail simp (the coercion resolves before).

**Remaining:** Step 2 (`stdGaussian_eq_withDensity`, generalized over finite `ι`),
Step 3 (`multivariateGaussian_eq_withDensity`, generalized), Steps 4–5 inline glue;
the theorem `integral_norm_gaussian_bounded` still has `sorry`.

### Sub-step 2a — DONE (proved in `Main.lean`)

`stdGaussianDensity_integral_one {ι} [Fintype ι] :
  ∫ x : EuclideanSpace ℝ ι, (2π)^(-(card ι : ℝ)/2) * Real.exp (-‖x‖²/2) = 1`

Needed so that `volume.withDensity (fun x => …)` is a probability measure — the
`IsFiniteMeasure` ingredient for `Measure.ext_of_charFun` in sub-step 2c (and reusable
in Step 4's withDensity bridge). It is the `c = 0`, `b = 1/2` case of
`GaussianFourier.integral_rexp_neg_mul_sq_norm`
(import `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`;
the lemmas live in namespace `GaussianFourier`, ambient `V` needs
`NormedAddCommGroup/InnerProductSpace ℝ/FiniteDimensional/MeasurableSpace/BorelSpace`).

Proof recipe (works verbatim):
```
have hb : 0 < (1/2 : ℝ) := by norm_num
have hf : ∀ x, Real.exp (-‖x‖^2/2) = Real.exp (-(1/2) * ‖x‖^2) := fun x => by congr 1; ring
have h0 : ∫ x, Real.exp (-‖x‖^2/2) ∂volume = (2π)^((card ι : ℝ)/2) := by
  simp only [hf]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ ι) hb,
      finrank_euclideanSpace,
      show (Real.pi / (1/2 : ℝ)) = 2 * Real.pi from by ring]
have hne : (2π)^((card ι : ℝ)/2) ≠ 0 := by positivity
rw [integral_const_mul, h0, neg_div, Real.rpow_neg, inv_mul_cancel₀ hne]; positivity
```
Gotchas: `Real.rpow_neg` leaves side goal `0 ≤ 2 * π` (close with `positivity` after the
main goal closes); `finrank_euclideanSpace` is a simp lemma equal to `Fintype.card ι`;
`ring` proves `(π : ℝ)/(1/2) = 2 * π` and the exponent reshuffle (`congr 1; ring`);
`inv_mul_cancel₀` (not `mul_inv_cancel₀`) since the inverse is on the LEFT.

**Remaining in Step 2:** 2b — `charFun (volume.withDensity (fun x => (2π)^(-(card ι : ℝ)/2) *
Real.exp (-‖x‖²/2))) t = exp(-‖t‖²/2)`; reduce via `charFun_apply` (`charFun μ t =
∫ x, exp (⟪x, t⟫ * I) ∂μ`) to `GaussianFourier.integral_cexp_neg_mul_sq_norm_add` with
`b = 1/2` and `c = ±I`; then 2c — `Measure.ext_of_charFun` + `charFun_stdGaussian`
(needs `IsFiniteMeasure` instances on both sides: use 2a for the density measure).
