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

## Status (updated 2026-11-12)

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

(Superseded — all steps are done; see the sub-step sections below and the final
**Remaining** at the end of this Status section.)

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

(Superseded — 2b and 2c are done; see below.)

### Sub-step 2b — DONE (proved in `Main.lean`)

`charFun_stdGaussianDensity {ι} [Fintype ι] (t : EuclideanSpace ℝ ι) :
  charFun (volume.withDensity (fun x => ENNReal.ofReal ((2π)^(-(card ι : ℝ)/2) *
    Real.exp (-(1/2) * ‖x‖^2)))) t = Complex.exp (-‖t‖^2 / 2)`

Proof recipe (compiles verbatim; in `Main.lean` write `Complex.I`/`Complex.exp` explicitly
since `Complex` is not opened there):
1. Setup: `hb : 0 < ((1/2 : ℝ) : ℂ).re := by norm_num`; `h2pi : 0 < 2 * Real.pi := by positivity`;
   `hne : (2π)^((card ι : ℝ)/2) ≠ 0 := by positivity`; `hpos : ∀ x, 0 ≤ (2π)^(-(card ι : ℝ)/2) *
   Real.exp (-(1/2) * ‖x‖^2) := fun x => by positivity`.
2. `hpoint` (ℝ≥0∞→ℂ scalar bridge):
   `(ENNReal.ofReal f).toReal • cexp (↑⟪x,t⟫ * I) = ↑((2π)^(-(card ι:ℝ)/2)) * (↑(rexp (-1/2*‖x‖^2)) * cexp (↑⟪x,t⟫ * I))`
   by `rw [ENNReal.toReal_ofReal (hpos x), Complex.real_smul, Complex.ofReal_mul, mul_assoc]`.
   Gotchas: `smul_eq_mul` FAILS for ℝ • ℂ (different smul instance) — `Complex.real_smul :
   x • z = x * z` is the right lemma (ℝ-scalar mul on ℂ is defeq to `↑x * z`); state the RHS so
   the real `rexp` factor is wrapped in `Complex.ofReal` explicitly (else the elaborator inserts
   `↑(rexp …)` which the next step's `simp only` won't line up with).
3. `hint` (pointwise exp-of-sum):
   `↑(rexp (-(1/2)*‖x‖^2)) * cexp (↑⟪x,t⟫ * I) = cexp (-↑(1/2) * (↑‖x‖)^2 + I * ↑⟪t,x⟫)`
   by `rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_pow,
   Complex.ofReal_neg, real_inner_comm t x, mul_comm (Complex.ofReal (inner ℝ t x)) Complex.I]`.
   Gotchas: the STATEMENT must write `Complex.ofReal ‖x‖ ^ 2` (coerce norm, then square) — NOT
   `Complex.ofReal (‖x‖ ^ 2)` — because the rewrite only proves the goal up to defeq, but
   `simp only [hint]` uses the STATED RHS; the resulting integrand then matches
   `integral_cexp_neg_mul_sq_norm_add`'s `-b * ↑‖v‖ ^ 2 + c * ⟪w, v⟫` shape. After
   `real_inner_comm t x` the inner is `inner ℝ t x`, so the final `mul_comm` must target
   `inner ℝ t x`.
4. Main chain: `rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop)
   (by simp)]` (ℝ≥0∞ density; the a.e.-finiteness side goal closes `by simp` via
   `ENNReal.ofReal_lt_top`), then `simp only [hpoint, hint]`, then
   `rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I t, …]`
   with `b = ((1/2 : ℝ) : ℂ)`, `c = Complex.I`, `w = t`.
5. Scalar endgame after the Fourier rewrite:
   ```
   finrank_euclideanSpace,
   ← Complex.ofReal_div,
   show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring,
   show (((Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)) = Complex.ofReal ((Fintype.card ι : ℝ) / 2) from by push_cast; rfl,
   ← Complex.ofReal_cpow h2pi.le ((Fintype.card ι : ℝ) / 2),
   neg_div,
   Real.rpow_neg h2pi.le ((Fintype.card ι : ℝ) / 2),
   ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hne,
   Complex.ofReal_one, one_mul,
   Complex.I_sq, neg_one_mul,
   show ((4 : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 2 from by norm_num
   ```
   Gotchas: the Fourier lemma's cpow exponent elaborates as `(↑(Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)`
   (ℕ-cast division IN ℂ, not ofReal of the division) — bridge with the `push_cast; rfl` `show`
   before `← Complex.ofReal_cpow`; `neg_div` is needed before `Real.rpow_neg` because
   `-(card : ℝ) / 2` elaborates as `(-card)/2` while `rpow_neg` needs `x ^ (-(y))`; pass explicit
   args to `Real.rpow_neg`/`Complex.ofReal_cpow` (else `0 ≤ x` surfaces as an rw side goal).

(Superseded — 2c is done; see below.)

### Sub-step 2c — DONE (proved in `Main.lean`)

`stdGaussian_eq_withDensity {ι} [Fintype ι] :
  stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity (fun x => ENNReal.ofReal
    ((2π)^(-(card ι : ℝ)/2) * Real.exp (-(1/2) * ‖x‖^2)))`

**Step 2 is now complete.** Proof recipe:
1. `IsFiniteMeasure` for the density measure (the only new ingredient — `stdGaussian`'s side
   comes from Mathlib's instance `isProbabilityMeasure_stdGaussian`, which extends it):
   - reshape 2a: `hexp : ∀ x, Real.exp (-(1/2)*‖x‖^2) = Real.exp (-‖x‖^2/2) := fun x => by
     congr 1; ring`, then `hint : ∫ x, (2π)^(-(card ι : ℝ)/2) * Real.exp (-(1/2)*‖x‖^2) = 1`
     by `simp only [hexp]; exact stdGaussianDensity_integral_one`;
   - `hfin : Integrable (fun x => …) volume := Integrable.of_integral_ne_zero (by rw [hint]; norm_num)`
     — the trick: `Integrable.of_integral_ne_zero` needs only `∫ f ≠ 0`, which 2a gives for free
     (no separate integrability argument needed);
   - `hlint : ∫⁻ x, ENNReal.ofReal f ∂volume = 1` by
     `rw [← ofReal_integral_eq_lintegral_ofReal hfin (Eventually.of_forall fun x => by positivity),
     hint, ENNReal.ofReal_one]` (`ofReal_integral_eq_lintegral_ofReal` lives in
     `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`);
   - `have : IsFiniteMeasure (volume.withDensity f) := isFiniteMeasure_withDensity
     (by rw [hlint]; simp)` (`isFiniteMeasure_withDensity (hf : ∫⁻ a, f a ∂μ ≠ ∞)`).
2. Conclusion: `refine Measure.ext_of_charFun (funext fun t => ?_)`, then
   `rw [charFun_stdGaussian, charFun_stdGaussianDensity]` — both sides become
   `Complex.exp (-‖t‖^2/2)`. Instances needed by `Measure.ext_of_charFun`
   (`CompleteSpace`, `BorelSpace`, `SecondCountableTopology`, `IsFiniteMeasure` on both
   sides) are all available for `EuclideanSpace ℝ ι` automatically.

### Sub-step 3 — DONE (proved in `Main.lean`)

Theorems proved in `Main.lean` (kept at `Fin n`; `multivariateGaussianPDF` stays at `Fin n`):

* `integral_subst {F} (n) (μ) (B) (hBdet : 0 < B.det) (f) (hf : AEMeasurable f volume) :
  ∫ x, f x ∂volume = (B.det : ℝ) • ∫ x, f (μ + toEuclideanLin B x) ∂volume` — via
  `Measure.map_linearMap_addHaar_eq_smul_addHaar` + `Matrix.toEuclideanLin_eq_toLin_orthonormal`
  + `LinearMap.det_toLin`; translation by `(μ + ·) ∘ L` then `← Measure.map_map`,
  `Measure.map_smul`, `MeasureTheory.map_add_left_eq_self volume μ`; transport of
  measurability via `Measure.smul_absolutelyContinuous` + `hf.mono_ac hac |>.aestronglyMeasurable`;
  tail `integral_map` (FIRST arg = measurability of the map!), `integral_smul_measure`,
  `ENNReal.toReal_ofReal`.
* `quadForm_sqrt_eq_norm_sq (n) (S) (hS : S.PosDef) : ∀ h : EuclideanSpace ℝ (Fin n),
  (S⁻¹ *ᵥ (CFC.sqrt S *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (CFC.sqrt S *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2` —
  via `Matrix.inv_eq_left_inv` of `(S⁻¹ * B) * B = 1` (so `B⁻¹ = S⁻¹ * B`),
  `Matrix.dotProduct_transpose_mulVec`, `hBT : Bᵀ = B` (from
  `Matrix.conjTranspose_eq_transpose_of_trivial` + `B.IsHermitian`),
  `Matrix.mul_nonsing_inv`, `Matrix.one_mulVec`, `EuclideanSpace.inner_toLp_toLp`,
  `real_inner_self_eq_norm_sq`.
* `stdGaussianDensity_ft {ι} [Fintype ι] (w : EuclideanSpace ℝ ι) : ∫ x : EuclideanSpace ℝ ι,
  Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) * Complex.exp (Complex.ofReal (inner ℝ x w) * Complex.I)
  = ((2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) * Complex.exp (-‖w‖ ^ 2 / 2)` —
  general-frequency version of 2b's core, via `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`
  (pointwise `hint` rewrites the integrand into its normal form: `Complex.exp (-(ofReal (1/2)) * ofReal ‖x‖^2 + I * ofReal (inner ℝ w x))`,
  using `real_inner_comm w x`), then coercion surgery
  (`← Complex.ofReal_div`, `show (π / (1/2 : ℝ)) = 2 * Real.pi`,
  `← Complex.ofReal_cpow`, `Complex.I_sq`, `neg_one_mul`).
* `multivariateGaussian_eq_withDensity (n) (μ) (S) (hS : S.PosDef) (t) :
  charFun (volume.withDensity (fun x => ENNReal.ofReal
  (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x))) t
  = Complex.exp (Complex.ofReal (inner ℝ t μ) * Complex.I
    - Complex.ofReal ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)) / 2)` — exactly the RHS of
  Mathlib's `charFun_multivariateGaussian (hS : S.PosSemidef)`, so Steps 4–5 glue via
  `Measure.ext_of_charFun` (finiteness on the Mathlib side is free from
  `IsGaussian.toIsProbabilityMeasure`).

**Step 3 proof recipe:**
1. CFC bundle: `set B := CFC.sqrt S with hBdef`; `hBB : B * B = S` (`CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef)`); `hBnn`, `hBher`, `hBdetEq : B.det = √S.det` (`Real.sqrt_eq_iff_eq_sq`), `hBdet`/`hSdet : IsUnit …`, `hBT : Bᵀ = B`.
2. Bridges: `hcoep : (μ + L x).ofLp - μ.ofLp = B *ᵥ x.ofLp` (`WithLp.ofLp_add`, `add_sub_cancel_left`, rfl); `hinner` (`Matrix.inner_toEuclideanCLM`); `hcoLt` (rfl); `hbridge : inner (L x) t = inner x (L t)` (`real_inner_comm`, `hinner`, `← Matrix.dotProduct_transpose_mulVec`, `hBT`).
3. PDF facts: `hpdf : ∀ x, multivariateGaussianPDF n μ.ofLp S hS x = RHS x := fun _ => rfl`;
   `hpos` (positivity); `hpoint : (ofReal (pdf x)).toReal • cexp (…) = ofReal (const⁻¹) * (ofReal (rexp (…)) * cexp (…))`
   (`ENNReal.toReal_ofReal`, `Complex.real_smul`, `Complex.ofReal_mul`, `mul_assoc`);
   `hmeasP` (see gotcha below); `htop : ∀ᵐ x, ofReal (pdf x) < ∞ := by simp`.
4. `hnorm2 : ‖toEuclideanLin B t‖ ^ 2 = (t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)` —
   `rw [← real_inner_self_eq_norm_sq, hinner …, hcoLt, ← Matrix.dotProduct_transpose_mulVec, hBT, Matrix.mulVec_mulVec, hBB]`.
5. `hstep2` (the key trick): ONE `have` stating `∫ x, (unsubstituted integrand) ∂volume
   = (B.det : ℝ) • ((const * cexp (inner μ t * I)) * ∫ x, (standard-Gaussian integrand with w = L t) ∂volume)`,
   proved by `refine Eq.trans hsub (congrArg ((B.det : ℝ) • ·) (Eq.trans (integral_congr_ae
   (Filter.Eventually.of_forall (fun y => hsplit y))) (integral_const_mul _ (fun x => …))))`
   where `hsub := integral_subst n μ B hBdetpos (fun x => …) (by fun_prop)` —
   `Eq.trans`/`congrArg` use elaborator defeq, avoiding brittle `rw` matching of the
   beta-redexed substituted integrand (see gotchas).
6. Endgame: `rw [charFun_apply]`,
   `rw [integral_withDensity_eq_integral_toReal_smul₀ hmeasP htop]`,
   `simp only [hpoint]`,
   `rw [hstep2, Complex.real_smul, stdGaussianDensity_ft (toEuclideanLin B t)]`,
   `simp only [Fintype.card_fin]`,
   `rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, hnorm2, hrearr, hscalC, one_mul, real_inner_comm t μ, hfin]`
   (`hrearr`/`hscalC`/`hfin` are `ring`/identity side conditions stated as `have`s).

Step-3 gotchas (verified by compile):
* `Matrix.mulVec_mulVec (v) (M) (N) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v` — vector argument is
  FIRST in the signature but the statement is `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`; use
  unexplicit `rw [Matrix.mulVec_mulVec]` (matches `B *ᵥ (B *ᵥ t)` uniquely).
* `real_inner_comm t μ` — argument order matters: this rewrites `inner ℝ μ t → inner ℝ t μ`
  (matching the goal-LHS form); with `(μ t)` it instead rewrote the theorem-RHS side and broke `hfin`.
* AEMeasurable of the PDF: `fun_prop` cannot unfold `multivariateGaussianPDF` ("No theorems
  found for multivariateGaussianPDF"). Instead: prove `Measurable` of the explicit RHS lambda
  by `fun_prop` (`hinner_meas`), compose `(ENNReal.measurable_ofReal.comp hinner_meas).aemeasurable`
  (annotate the `AEMeasurable … volume` type so the implicit measure is fixed), then transport
  to the PDF form with `AEMeasurable.congr (Filter.Eventually.of_forall (fun x => by simp only [hpdf]))`
  — plain `rw [hpdf x]` FAILS inside the congr goal because it is not beta-reduced; `simp only` is.
* `integral_congr` for Bochner integrals is `integral_congr_ae` (needs `=ᵐ[μ]`; obtain from
  pointwise via `Filter.Eventually.of_forall`).
* The substituted integral in `integral_subst`'s RHS is a beta-redex
  `f (μ + L x)` (`f` a lambda) — `rw [hsplit]` (or any rewrite whose pattern spells the
  substituted body) FAILS against it even though everything displays identically;
  chain with `Eq.trans`/`congrArg` instead.
* `Fintype.card (Fin n) = n` is NOT rfl: `simp only [Fintype.card_fin]` after
  `rw [stdGaussianDensity_ft …]`.
* `Main.lean` needs `open scoped Matrix MatrixOrder` (`0 ≤ S`, `PosSemidef` order on matrices)
  and `open scoped ENNReal` (`∞` notation) for the Step-3 block.
* `set B := CFC.sqrt S with hBdef` then state helpers against `B`; `exact hquad n S hS h`
  closes the `B`-form goal by defeq (the `rw [← hBdef] at *` in the prototype is a no-op).

**Remaining:** none — all five steps are proved; `integral_norm_gaussian_bounded` is complete
(see "Steps 4–5" below).

### Steps 4–5 — DONE (proved in `Main.lean`)

New theorems in `Main.lean` (all verified with `lake env lean Main.lean`; `#print axioms` on the
main theorem and all helpers shows only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):

* `integral_multivariateGaussianPDF_one (n) (μ : EuclideanSpace ℝ (Fin n)) (S) (hS : S.PosDef) :
  ∫ x, multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x ∂volume = 1` — Step 4. CFC bundle as in
  Step 3, `hshift` (PDF at `μ + B y` collapses to the standard density:
  `rw [hpdf, hcoep y, hquad' y, ← neg_div]` — the `← neg_div` is REQUIRED because the rewritten
  exponent is `-(‖y‖²/2)` (Neg(Div)) while the stated RHS is `-‖y‖²/2` (Div(Neg)) and they are
  NOT defeq), then `hstep` (defeq-chained `Eq.trans hsub (congrArg _ (Eq.trans
  (integral_congr_ae …) (integral_const_mul …)))`, same pattern as Step 3's `hstep2`), extraction
  of `∫ exp(-‖x‖²/2) = (2π)^(n/2)` from `stdGaussianDensity_integral_one`, tail `rw [hstep,
  smul_eq_mul, h1]; rw [hscal]` with Step-3's `hscal` scalar identity.
* `isFiniteMeasure_gaussianPDF_withDensity (n) (mean : Fin n → ℝ) (S) (hS : S.PosDef) :
  IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (multivariateGaussianPDF n mean
  S hS x)))` — Step 5 support. Takes the mean as a PLAIN `Fin n → ℝ` function (not
  `EuclideanSpace`) so the main theorem can call it with `(A⁻¹).mulVec y` verbatim; internally
  calls `integral_multivariateGaussianPDF_one` at `(WithLp.toLp 2 mean)` and bridges via a
  pointwise `rfl` (`WithLp.ofLp (WithLp.toLp 2 m) ≡ m`). Mirrors the 2c recipe
  (`Integrable.of_integral_ne_zero`, `ofReal_integral_eq_lintegral_ofReal`,
  `isFiniteMeasure_withDensity`).
* `multivariateGaussianPDF_eq (n) (m) (Cov) (hC : Cov.PosDef) (x)` — generic pointwise PDF
  unfolding (rfl); parenthesisation: the exponent is `-(((Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ
  ((x : Fin n → ℝ) - m)) / 2)`, i.e. Neg(Div(dotProduct, 2)) — the dotProduct AND the mulVec each
  carry their own parens, and the `/ 2` sits inside the negation parens.
* `measurable_multivariateGaussianPDF (n) (m) (Cov) (hC) : Measurable (fun x => …)` —
  `simp only [multivariateGaussianPDF_eq n m Cov hC]` under the binder, then `fun_prop`
  (fun_prop cannot unfold `multivariateGaussianPDF` itself).
* Main theorem `integral_norm_gaussian_bounded` — glue:
  `hSig := sigmaTilde_posDef n S hS A hA`; `hposT` (PDF ≥ 0) via
  `rw [multivariateGaussianPDF_eq …]` + `mul_nonneg`; `hmeasPT := (ENNReal.measurable_ofReal.comp
  (measurable_multivariateGaussianPDF …)).aemeasurable`; `htopT : ∀ᵐ x, ENNReal.ofReal (pdf x) < ∞`
  by `simp`; finiteness `hfin` from `isFiniteMeasure_gaussianPDF_withDensity`; measure identity
  `hEq : volume.withDensity (ofReal ∘ pdf) = multivariateGaussian (A⁻¹·y) (A⁻¹ S A⁻ᵀ)` via
  `Measure.ext_of_charFun` + `rw [multivariateGaussian_eq_withDensity n (WithLp.toLp 2 ((A⁻¹).mulVec
  y)) (A⁻¹ * S * A⁻¹ᵀ) hSig t, charFun_multivariateGaussian hSig.posSemidef t]` (note: Step 3's
  theorem takes `PosDef`, Mathlib's `charFun_multivariateGaussian` takes `PosSemidef`);
  `hwithD : Integrable id (withDensity …) := by rw [hEq]; exact IsGaussian.integrable_id`
  (`IsGaussian.toIsProbabilityMeasure` supplies the `IsFiniteMeasure` instance on the
  `multivariateGaussian` side for `ext_of_charFun`); then
  `(integrable_withDensity_iff_integrable_smul₀' hmeasPT htopT).mp hwithD` (the `.mp` with
  `g := id` avoids the higher-order `rw` into the iff), `.norm`,
  `hpt : ‖(ofReal pdf x).toReal • id x‖ = ‖x‖ * pdf x` via `rw [norm_smul,
  ENNReal.toReal_ofReal (hposT x), Real.norm_eq_abs, abs_of_nonneg (hposT x), show ‖id x‖ = ‖x‖
  from rfl, mul_comm]` (order matters: `toReal_ofReal` FIRST, since
  `ENNReal.toReal_nonneg` is a Prop-application, not a function; `abs_of_nonneg (hposT x)`
  then works on the real value directly), `hkey := hnormed.congr …`, and the final
  `Integrable.congr` to the goal integrand via `hcongr1`, proved by `rw [mul_assoc, mul_comm
  (pdf₀ …) (1 / Real.sqrt …), ← density_id n S hS A hA y hSig h]` (mul_assoc FORWARD — the goal
  LHS is `(‖h‖ * pdf₀) * c`, left-associated, and `← mul_assoc` looks for `a * (b * c)`).

Gotchas (Steps 4–5):

* **Combining tilde is not a Lean identifier character**: `hpos̃`/`hmeasP̃` fail with
  `error: expected token` at the identifier; use ASCII names (`hposT`, `hmeasPT`, `htopT`).
* The `(x : EuclideanSpace ℝ (Fin n)) → Fin n → ℝ` cast is `WithLp.ofLp`, and
  `WithLp.ofLp (WithLp.toLp 2 v) ≡ v` is rfl — so cast-mean and plain-mean PDF values agree
  pointwise by `rfl` (`hcast`), and `withDensity` of them are defeq (`exact` suffices for
  `IsFiniteMeasure`); for `rw`-matching use an explicit `congrArg volume.withDensity (funext …)`
  bridge (`hEqL`) rather than relying on `kabstract` seeing through the cast.
* Everything in the main theorem is stated with the PLAIN mean `((A⁻¹).mulVec (y : Fin n → ℝ))`
  so `density_id` matches verbatim in the last `rw`.
* `simp only [neg_div] at h0` in the `stdGaussianDensity_integral_one` extraction also rewrites
  the exponent `-‖x‖²/2` → `-(‖x‖²/2)`, breaking later `rw [h1]`; instead target ONLY the rpow
  exponent: `rw [show (-(↑n : ℝ)) / 2 = -((↑n : ℝ) / 2) from by ring] at h0`, then
  `rw [Real.rpow_neg h2pi.le ((n : ℝ) / 2)] at h0`.
* `charFun_multivariateGaussian`'s RHS `exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2)` elaborates (under
  `open Matrix` scoped notation, `⟪·,·⟫ = inner 𝕜 · ·`, and ℝ→ℂ coercion = `Complex.ofReal`)
  to exactly the RHS form of `multivariateGaussian_eq_withDensity`, so the two-step `rw` closes
  the `ext_of_charFun` goal outright — no bridge needed.
