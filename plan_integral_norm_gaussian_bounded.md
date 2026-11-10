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
