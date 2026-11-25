module

public import Main
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Phases 0–2 of `plan.md`: Gaussian mixture priors satisfy the weighted-L¹ hypothesis of `cme_uniform_balls_R`

A finite Gaussian mixture with weights `w` (nonnegative, summing to one), locations `μ`,
and common positive definite covariance `Cov` is `gmmPDF n k Cov hC w μ`. This file
implements all three phases of `plan.md`:

* **Phase 0**: `isPdf_gmmPDF`, `integrable_norm_mul_gmmPDF`, and
  `cme_convergence_of_gmm_prior` — when the true prior is itself a GMM, its pdf and
  first-moment hypotheses are automatic.
* **Phase 1**: `gaussSmoothed`, `isPdf_gaussSmoothed`, `weighted_smoothing_tendsto_seq`,
  `hw_smoothedPriorSeq`, and `cme_uniform_balls_smoothed_prior` — Gaussian-smoothed
  (continuum-mixture) priors converge in weighted L¹ and yield locally uniform CME
  convergence.
* **Phase 2**: `modulus_tendsto_integrable`, `weighted_modulus_tendsto_integrable`,
  `weighted_smoothing_integrable`, the half-open lattice cell partition (`gridFinset`,
  `cell`, `coveredBox`, `cellWeight`), `gmmApprox`, `gmmApprox_quantization_of_modulus_bound`,
  `isPdf_gmmApprox`, `gmmApprox_eq_gmmPDF`, the diagonal sequence `gmmPriorSeq`,
  `hw_gmmPriorSeq`, and the main theorems **`gmm_density_weighted_L1`** and
  **`cme_uniform_balls_gmm_prior_general`** — every measurable pdf prior `f` with finite
  first moment is approximated in weighted L¹ by a sequence of finite Gaussian mixture
  pdfs (`gmmPDF`), and the resulting conditional mean estimates converge locally uniformly
  on every closed ball in `ℝ^m` for arbitrary dimensions `m, n` and observation matrix `A`.
-/

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped ENNReal

/-- Weights of a finite mixture: nonnegative and summing to one. -/
public def IsMixtureWeights {k : ℕ} (w : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- A finite Gaussian mixture: the weighted sum of multivariate Gaussian pdfs with a
common positive definite covariance `Cov`, mixture weights `w`, and locations `μ`. -/
public noncomputable def gmmPDF (n k : ℕ) (Cov : Matrix (Fin n) (Fin n) ℝ) (hC : Cov.PosDef)
    (w : Fin k → ℝ) (μ : Fin k → Fin n → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
  ∑ i, w i * multivariateGaussianPDF n (μ i) Cov hC x

/-- The multivariate Gaussian pdf is everywhere strictly positive. -/
theorem multivariateGaussianPDF_pos (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    0 < multivariateGaussianPDF n m Cov hC x := by
  rw [multivariateGaussianPDF_eq n m Cov hC x]
  refine mul_pos (inv_pos.mpr ?_) (Real.exp_pos _)
  exact
    mul_pos (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi) _)
      (Real.sqrt_pos.mpr hC.det_pos)

/-- Integral of the Gaussian pdf with a plain-vector mean (the `EuclideanSpace`-mean
version is `integral_multivariateGaussianPDF_one`). -/
theorem integral_gaussianPDF (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n m Cov hC x ∂volume = 1 := by
  have hcast :
    ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (WithLp.toLp 2 m) Cov hC x = multivariateGaussianPDF n m Cov hC x :=
    fun _ => rfl
  exact
    (integral_congr_ae (Filter.Eventually.of_forall fun x => (hcast x).symm)).trans
      (integral_multivariateGaussianPDF_one n (WithLp.toLp 2 m) Cov hC)

/-- A single Gaussian pdf is a pdf. -/
theorem isPdf_multivariateGaussianPDF (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) : IsPdf (multivariateGaussianPDF n m Cov hC) := by
  refine ⟨fun x => le_of_lt (multivariateGaussianPDF_pos n m Cov hC x), ?_⟩
  exact integral_gaussianPDF n m Cov hC

/-- Evaluating a Gaussian pdf with mean `m` at `x` is the same as evaluating the centered
Gaussian pdf at the point `x + (-m)` (plain-vector shift). -/
theorem multivariateGaussianPDF_sub_mean (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    multivariateGaussianPDF n m Cov hC x =
      multivariateGaussianPDF n 0 Cov hC (WithLp.toLp 2 ((x : Fin n → ℝ) + (-m : Fin n → ℝ))) := by
  rw [multivariateGaussianPDF_eq n m Cov hC x,
    multivariateGaussianPDF_eq n 0 Cov hC (WithLp.toLp 2 ((x : Fin n → ℝ) + (-m : Fin n → ℝ)))]
  rw [WithLp.ofLp_toLp, sub_zero, sub_eq_add_neg]

/-- The centered Gaussian pdf is even: `pdf(-x) = pdf(x)`. -/
theorem multivariateGaussianPDF_neg (n : ℕ) (Cov : Matrix (Fin n) (Fin n) ℝ) (hC : Cov.PosDef)
    (x : Fin n → ℝ) :
    multivariateGaussianPDF n 0 Cov hC (WithLp.toLp 2 (-x)) =
      multivariateGaussianPDF n 0 Cov hC (WithLp.toLp 2 x) := by
  rw [multivariateGaussianPDF_eq n 0 Cov hC (WithLp.toLp 2 (-x)),
    multivariateGaussianPDF_eq n 0 Cov hC (WithLp.toLp 2 x)]
  rw [WithLp.ofLp_toLp, WithLp.ofLp_toLp, sub_zero, sub_zero, Matrix.mulVec_neg, neg_dotProduct_neg]

/-- Right-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`
(Bochner version, `y + c` form; cf. `integral_toLp_trans`). -/
theorem integral_toLp_trans_right {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [SecondCountableTopology F] (n : ℕ) (c : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) + c)) ∂volume =
      ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show
      (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + c))) =
        (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 (c + (y : Fin n → ℝ))))
      from by
      funext y; rw [add_comm (y : Fin n → ℝ) c]]
  exact integral_toLp_trans n c g hg

/-- Right-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`
(ℝ≥0∞ version, `y + c` form; cf. `lintegral_toLp_trans`). -/
theorem lintegral_toLp_trans_right (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) + c)) ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show
      (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + c))) =
        (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 (c + (y : Fin n → ℝ))))
      from by
      funext y; rw [add_comm (y : Fin n → ℝ) c]]
  exact lintegral_toLp_trans n c g hg

/-- Bochner integrability is invariant under the map `h ↦ toLp 2 (h + c)`. -/
theorem integrable_toLp_shift {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [SecondCountableTopology F] (n : ℕ) (c : Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → F) (hg : MeasureTheory.Integrable g volume)
    (hgmeas : Measurable g) :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((h : Fin n → ℝ) + c))) volume := by
  classical
  have hTmeas :
    Measurable (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((h : Fin n → ℝ) + c)) := by
    fun_prop
  refine ⟨(hgmeas.comp hTmeas).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  rw [lintegral_toLp_trans_right n c (fun u => ‖g u‖ₑ) hgmeas.enorm]
  rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact hg.2

/-- The centered first moment: the integrand `fun u => ‖u‖ * pdf(u)` of a centered
Gaussian pdf is integrable (from `integral_gaussian_bounded` with `A = 1`, `y = 0`, plus
the evenness of the centered Gaussian). -/
theorem integrable_norm_mul_gaussianPDF_center (n : ℕ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u) volume := by
  have hunit : IsUnit ((1 : Matrix (Fin n) (Fin n) ℝ).det) := by
    rw [Matrix.det_one]; exact isUnit_one
  have h0 := integral_gaussian_bounded n Cov hC 1 hunit (WithLp.toLp 2 (0 : Fin n → ℝ))
  have key :
    (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u) =
      fun h : EuclideanSpace ℝ (Fin n) =>
      ‖h‖ *
        multivariateGaussianPDF n 0 Cov hC
          (WithLp.toLp 2
            ((0 : Fin n → ℝ) - (1 : Matrix (Fin n) (Fin n) ℝ).mulVec (h : Fin n → ℝ))) := by
    funext h
    rw [Matrix.one_mulVec, zero_sub, multivariateGaussianPDF_neg, WithLp.toLp_ofLp]
  rw [key]
  exact h0

/-- The first moment of a Gaussian pdf is finite: the integrand
`fun h => ‖h‖ * pdf(h)` is integrable for a Gaussian pdf with **arbitrary** mean `m`
(translate the centered first moment, then dominate `‖h‖ ≤ ‖h - m‖ + ‖m‖`). -/
theorem integrable_norm_mul_gaussianPDF (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * multivariateGaussianPDF n m Cov hC h) volume := by
  classical
  have hcenter :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u) volume :=
    integrable_norm_mul_gaussianPDF_center n Cov hC
  have hGmeas :
    Measurable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u) :=
    (continuous_norm.measurable).mul (measurable_multivariateGaussianPDF n 0 Cov hC)
  -- the translated first moment
  have hshift :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u)
          (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))))
      volume :=
    integrable_toLp_shift n (-m : Fin n → ℝ)
      (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u) hcenter
      hGmeas
  -- the constant part
  have hintm :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n m Cov hC h) volume :=
    integrable_of_isPdf (isPdf_multivariateGaussianPDF n m Cov hC)
  have hint3 :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ *
          multivariateGaussianPDF n 0 Cov hC (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))))
      volume := by
    have key :
      (fun h : EuclideanSpace ℝ (Fin n) =>
          ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ *
            multivariateGaussianPDF n 0 Cov hC
              (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)))) =
        fun h : EuclideanSpace ℝ (Fin n) =>
        ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ • multivariateGaussianPDF n m Cov hC h := by
      funext h
      rw [smul_eq_mul, ← multivariateGaussianPDF_sub_mean]
    rw [key]
    exact MeasureTheory.Integrable.smul ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ hintm
  -- domination: `‖h‖ ≤ ‖h - m‖ + ‖m‖`
  have hsum :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * multivariateGaussianPDF n 0 Cov hC u)
            (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))) +
          ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ *
            multivariateGaussianPDF n 0 Cov hC (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))))
      volume :=
    hshift.add hint3
  have hfmeas :
    MeasureTheory.AEStronglyMeasurable
      (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * multivariateGaussianPDF n m Cov hC h) volume :=
    ((continuous_norm.measurable).mul
        (measurable_multivariateGaussianPDF n m Cov hC)).aestronglyMeasurable
  refine hsum.mono' hfmeas (Filter.Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs,
    abs_eq_self.mpr
      (mul_nonneg (norm_nonneg _) (le_of_lt (multivariateGaussianPDF_pos n m Cov hC h)))]
  have hshift_eq :
    (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
      h - WithLp.toLp 2 m := by
    rw [← WithLp.toLp_sub, sub_eq_add_neg]
  have hsplit :
    (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) +
        WithLp.toLp 2 m =
      h := by
    rw [hshift_eq, sub_add_cancel]
  have htri :
    ‖h‖ ≤
      ‖(WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ +
        ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ := by
    conv_lhs => rw [← hsplit]
    exact norm_add_le _ _
  calc
    ‖h‖ * multivariateGaussianPDF n m Cov hC h ≤
        (‖(WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ +
            ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖) *
          multivariateGaussianPDF n m Cov hC h :=
      mul_le_mul_of_nonneg_right htri (le_of_lt (multivariateGaussianPDF_pos n m Cov hC h))
    _ =
        ‖(WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ *
            multivariateGaussianPDF n m Cov hC h +
          ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ * multivariateGaussianPDF n m Cov hC h :=
      by rw [add_mul]
    _ =
        ‖(WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ *
            multivariateGaussianPDF n 0 Cov hC
              (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))) +
          ‖(WithLp.toLp 2 m : EuclideanSpace ℝ (Fin n))‖ *
            multivariateGaussianPDF n 0 Cov hC
              (WithLp.toLp 2 ((h : Fin n → ℝ) + (-m : Fin n → ℝ))) :=
      by rw [multivariateGaussianPDF_sub_mean]

/-- A finite Gaussian mixture is a pdf: pointwise nonnegative (each Gaussian pdf is
positive and the weights are nonnegative) with total mass `∑ w i = 1` (finite-sum
interchange plus `integral_multivariateGaussianPDF_one`). -/
public theorem isPdf_gmmPDF (n k : ℕ) (Cov : Matrix (Fin n) (Fin n) ℝ) (hC : Cov.PosDef)
    (w : Fin k → ℝ) (μ : Fin k → Fin n → ℝ) (hw : IsMixtureWeights w) :
    IsPdf (gmmPDF n k Cov hC w μ) := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [gmmPDF]
    exact
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw.1 i) (le_of_lt (multivariateGaussianPDF_pos n (μ i) Cov hC x))
  · simp only [gmmPDF]
    have hint :
      ∀ i : Fin k,
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) => w i * multivariateGaussianPDF n (μ i) Cov hC x)
          volume := by
      intro i
      refine
        (MeasureTheory.Integrable.smul (w i)
              (integrable_of_isPdf (isPdf_multivariateGaussianPDF n (μ i) Cov hC))).congr
          ?_
      filter_upwards with x
      simp only [Pi.smul_apply, smul_eq_mul]
    calc
      ∫ x : EuclideanSpace ℝ (Fin n), gmmPDF n k Cov hC w μ x ∂volume =
          ∑ i,
            ∫ x : EuclideanSpace ℝ (Fin n),
              w i * multivariateGaussianPDF n (μ i) Cov hC x ∂volume :=
        MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hint i)
      _ = ∑ i, w i :=
        Finset.sum_congr rfl fun i _ => by
          rw [MeasureTheory.integral_const_mul, integral_gaussianPDF n (μ i) Cov hC, mul_one]
      _ = 1 := hw.2

/-- A finite Gaussian mixture has a finite first moment (each component does, and the
integrand is a finite sum): the `hfmom` hypothesis of `cme_uniform_balls_R` is automatic
for GMM priors, for any weights `w` and locations `μ`. -/
public theorem integrable_norm_mul_gmmPDF (n k : ℕ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (w : Fin k → ℝ) (μ : Fin k → Fin n → ℝ) :
    MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * gmmPDF n k Cov hC w μ h)
      volume := by
  classical
  have hint :
    ∀ i : Fin k,
      MeasureTheory.Integrable
        (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * (w i * multivariateGaussianPDF n (μ i) Cov hC h))
        volume :=
    fun i =>
    (MeasureTheory.Integrable.smul (w i) (integrable_norm_mul_gaussianPDF n (μ i) Cov hC)).congr
      (Filter.Eventually.of_forall fun h => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
  have hsum :
    (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * gmmPDF n k Cov hC w μ h) =
      fun h : EuclideanSpace ℝ (Fin n) =>
      ∑ i, ‖h‖ * (w i * multivariateGaussianPDF n (μ i) Cov hC h) := by
    funext h
    simp only [gmmPDF, ← Finset.mul_sum]
  rw [hsum]
  exact MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hint i)

/-- **Phase 0**: if the true prior is a finite Gaussian mixture, then *every* sequence of
priors `fhK` converging to it in the weighted-L¹ sense satisfies the hypotheses of
`cme_uniform_balls_R` with no analytic hypothesis on the prior: the GMM prior is a pdf
(`isPdf_gmmPDF`) and has finite first moment automatically
(`integrable_norm_mul_gmmPDF`). Consequently the conditional mean estimates computed
from `fhK` converge to the CME of the GMM prior locally uniformly — uniformly on every
closed ball of radius `r > 0` in `ℝ^m`, for arbitrary dimensions `m, n` and observation
matrix `A` (no invertibility or rank hypothesis). -/
public theorem cme_convergence_of_gmm_prior (m n k : ℕ) (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (A : Matrix (Fin m) (Fin n) ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (w : Fin k → ℝ) (μ : Fin k → Fin n → ℝ) (hw : IsMixtureWeights w)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfhKpdf : ∀ K, IsPdf (fhK K))
    (hconv :
      ∀ ε > 0,
        ∃ K₀ : ℕ,
          ∀ K ≥ K₀,
            ∫⁻ h : EuclideanSpace ℝ (Fin n),
                ENNReal.ofReal ((1 + ‖h‖) * |gmmPDF n k Cov hC w μ h - fhK K h|) ∂volume <
              ENNReal.ofReal ε)
    (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun K : ℕ =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A (gmmPDF n k Cov hC w μ) y - cmeR m n S hS A (fhK K) y‖)
      atTop (nhds 0) :=
  cme_uniform_balls_R m n S hS A (gmmPDF n k Cov hC w μ) (isPdf_gmmPDF n k Cov hC w μ hw)
    (integrable_norm_mul_gmmPDF n k Cov hC w μ) fhK hfhKpdf hconv r hr

/-! ## Phase 1 of `plan.md`: the Gaussian-smoothed (continuum-mixture) sequence satisfies
the weighted-L¹ hypothesis `hw`

For a **continuous** pdf `f` with finite first moment and a fixed positive definite
covariance `C`, the Gaussian-smoothed priors `gaussSmoothed n f C hC σ hσ` (with
`σ = 1/(K+1) → 0`) converge to `f` in weighted L¹:
`∫ (1 + ‖x‖) |f x - gaussSmoothed ... x| ∂volume → 0`. Each `gaussSmoothed` is a pdf, so
the hypothesis `hw` of `cme_uniform_balls_R` is satisfiable by (continuum) mixtures of
Gaussians. The restriction to continuous `f` matches the paper's class `C₀` setting
(continuity is what makes the translation-modulus argument a plain dominated
convergence); the general case is deferred (see `plan.md`). -/

/-- The scaled Gaussian mollifier `ψ_σ = σ^{-n} · φ_C(·/σ)` for a fixed positive definite
covariance `C` (the density of `N(0, σ² C)`). -/
public noncomputable def mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (_hσ : 0 < σ) : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
  (σ : ℝ)⁻¹ ^ n * multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ)))

/-- The Gaussian-smoothed prior: the (continuum) mixture
`x ↦ ∫ ψ_σ(u) · f (x − u) du`. -/
public noncomputable def gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (_hσ : 0 < σ) :
    EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
  ∫ u : EuclideanSpace ℝ (Fin n),
    mollifier n C hC σ _hσ u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume

/-- Transport for scalar-multiple identity matrices. -/
theorem toEuclideanLin_smul_one (n : ℕ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (r • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      WithLp.toLp 2 (r • (x : Fin n → ℝ)) := by
  apply WithLp.ofLp_injective
  show (r • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (x : Fin n → ℝ) = r • (x : Fin n → ℝ)
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem mollifier_nonneg (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ)
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ mollifier n C hC σ hσ x := by
  simp only [mollifier]
  exact
    mul_nonneg (le_of_lt (pow_pos (inv_pos.mpr hσ) n))
      (le_of_lt (multivariateGaussianPDF_pos n 0 C hC _))

/-- Mass of the mollifier: `∫ ψ_σ = 1` (change of variables `x ↦ σ⁻¹ • x` via
`integral_subst`). -/
theorem integral_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) : ∫ x : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ x ∂volume = 1 := by
  classical
  simp only [mollifier]
  have hBdet : 0 < ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_pos (inv_pos.mpr hσ) n
  have hsub :=
    integral_subst n 0 ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) hBdet
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n 0 C hC x)
      (measurable_multivariateGaussianPDF n 0 C hC).aemeasurable
  rw [integral_gaussianPDF n 0 C hC, smul_eq_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
    mul_one] at hsub
  simp only [zero_add] at hsub
  rw [integral_congr_ae
      (Filter.Eventually.of_forall fun x => by rw [toEuclideanLin_smul_one])] at hsub
  have hinner :
    ∫ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ))) ∂volume =
      (σ : ℝ) ^ n := by
    have h2 :
      (σ : ℝ) ^ n * 1 =
        (σ : ℝ) ^ n *
          ((σ : ℝ)⁻¹ ^ n *
            ∫ x : EuclideanSpace ℝ (Fin n),
              multivariateGaussianPDF n 0 C hC
                (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ))) ∂volume) := by
      rw [← hsub]
    rw [mul_one, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), one_mul] at h2
    exact h2.symm
  rw [integral_const_mul, hinner, inv_pow, inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hσ))]

/-- `∫ ψ_σ(u) · H u du = ∫ φ_C(v) · H (σ v) dv`: the transport used for the dominated
convergence in the smoothing theorem (change of variables `u ↦ σ v` via
`integral_subst`). -/
theorem integral_mollifier_mul (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (H : EuclideanSpace ℝ (Fin n) → ℝ) (hH : AEMeasurable H volume) :
    ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ u * H u ∂volume =
      ∫ v : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n 0 C hC v *
          H (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) ∂volume := by
  classical
  simp only [mollifier, mul_assoc, MeasureTheory.integral_const_mul]
  have hpdfS :
    AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
      volume :=
    ((measurable_multivariateGaussianPDF n 0 C hC).comp
        (by fun_prop :
          Measurable fun u : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).aemeasurable
  have hFmeas :
    AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        (σ : ℝ)⁻¹ ^ n *
          multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) *
          H u)
      volume :=
    (hpdfS.const_mul ((σ : ℝ)⁻¹ ^ n)).mul hH
  have hBdet : 0 < ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_pos hσ n
  have htr :
    ∀ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2
            ((σ : ℝ)⁻¹ •
              ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                    ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                  v :
                Fin n → ℝ))) =
        multivariateGaussianPDF n 0 C hC v := by
    intro v
    congr 1
    rw [toEuclideanLin_smul_one, WithLp.ofLp_toLp, ← mul_smul, inv_mul_cancel₀ (ne_of_gt hσ),
      one_smul]
  have hsub :=
    integral_subst n 0 ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) hBdet
      (fun u : EuclideanSpace ℝ (Fin n) =>
        (σ : ℝ)⁻¹ ^ n *
          multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) *
          H u)
      hFmeas
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hsub
  simp only [zero_add, htr, smul_eq_mul, mul_assoc] at hsub
  simp only [MeasureTheory.integral_const_mul] at hsub
  rw [hsub, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), one_mul]
  have hpt :
    ∀ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC v * H ((toEuclideanLin (σ • 1)) v) =
        multivariateGaussianPDF n 0 C hC v * H (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) := by
    intro v
    rw [toEuclideanLin_smul_one]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => hpt v)

/-- Bochner integrability is invariant under the map `h ↦ toLp 2 (c - h)` (the
composition of the reflection and a translation, both `volume`-preserving). -/
theorem integrable_toLp_sub {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [OpensMeasurableSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [SecondCountableTopology F] (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.Integrable g volume) (hgmeas : Measurable g) :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))))
      volume := by
  classical
  have hLdet :
    |(LinearMap.det
          (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
            ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))))| =
      1 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  have hLne :
    (LinearMap.det
        (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))) ≠
      0 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)
  have hLabs :
    |(LinearMap.det
          (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
            ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))))| =
      1 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  have hTneg :
    Measurable (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) := by
    have heq :
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) =
        fun h : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (0 : Fin n → ℝ) - WithLp.toLp 2 (h : Fin n → ℝ) := by
      funext h
      rw [← zero_sub, WithLp.toLp_sub]
    rw [heq]
    exact Measurable.sub measurable_const measurable_id
  have hTnegmap :
    MeasureTheory.Measure.map (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ)))
        volume =
      volume := by
    rw [show
        (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) =
          Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
        from by
        funext h
        apply WithLp.ofLp_injective
        show
          (-(h : Fin n → ℝ) : Fin n → ℝ) =
            ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (h : Fin n → ℝ)
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul],
      MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, abs_inv, hLabs,
      inv_one, ENNReal.ofReal_one, one_smul]
  have hTmeas :
    Measurable
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) := by
    have heq :
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) =
        fun h : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (c : Fin n → ℝ) - WithLp.toLp 2 (h : Fin n → ℝ) := by
      funext h
      rw [WithLp.toLp_sub]
    rw [heq]
    exact Measurable.sub measurable_const measurable_id
  have hTmeasOut :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) := by
    have heq :
      (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) =
        fun z : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (c : Fin n → ℝ) + WithLp.toLp 2 (z : Fin n → ℝ) := by
      funext z
      rw [WithLp.toLp_add]
    rw [heq]
    exact Measurable.add measurable_const measurable_id
  have hTmap :
    MeasureTheory.Measure.map
        (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ)))
        volume =
      volume := by
    have hcomp :
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) =
        (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) ∘
          (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) := by
      funext h
      congr 1
    have heqO :
      (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) =
        fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c : Fin n → ℝ) + x := by
      funext z
      rw [WithLp.toLp_add, WithLp.ofLp_toLp]
    rw [hcomp, ← MeasureTheory.Measure.map_map hTmeasOut hTneg, hTnegmap, heqO,
      MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  refine ⟨(hgmeas.comp hTmeas).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm, ← lintegral_map hgmeas.enorm hTmeas, hTmap]
  exact hg.2

/-- **Moment-tail lemma**: for a nonnegative integrable function `g`, the integrals over the
outside of growing closed balls tend to `0` (sequential dominated convergence on the
exhaustion by complements of balls). -/
theorem setIntegral_tail_tendsto (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : MeasureTheory.Integrable g volume) (hgnonneg : ∀ x, 0 ≤ g x) :
    Tendsto (fun k : ℕ => ∫ x in {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}, g x ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hmeas : ∀ k : ℕ, MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖} := by
    intro k
    exact
      (((by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin n) => ‖y‖)).isOpen_preimage _
          isOpen_Ioi).measurableSet
  have hind :
    ∀ k : ℕ,
      ∫ x in {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}, g x ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x ∂volume :=
    fun k =>
    (MeasureTheory.integral_indicator (s := {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖})
        (hmeas k)).symm
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k => (hind k).symm) ?_
  have hbound :
    ∀ k : ℕ,
      ∀ᵐ x ∂volume, ‖{y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x‖ ≤ g x := by
    intro k
    filter_upwards with x
    rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}) with hx | hx
    · simp only [Set.indicator_of_mem hx]
      simp [abs_of_nonneg (hgnonneg x)]
    · simp only [Set.indicator_of_notMem hx]
      simp
      exact hgnonneg x
  have hlim :
    ∀ᵐ x ∂volume,
      Tendsto (fun k : ℕ => {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x)
        Filter.atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
    filter_upwards with x
    have hev :
      (fun k : ℕ => {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x) =ᶠ[Filter.atTop]
        fun _ => (0 : ℝ) := by
      obtain ⟨k₀, h⟩ := exists_nat_gt ‖x‖
      filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
      have hmem : ¬((k : ℝ) < ‖x‖) := not_lt.mpr (le_trans (le_of_lt h) (Nat.cast_le.mpr hk))
      simp [hmem]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hdct :=
    MeasureTheory.tendsto_integral_of_dominated_convergence g (f := fun _ => (0 : ℝ))
      (fun k => hg.1.indicator (hmeas k)) hg hbound hlim
  rw [integral_zero] at hdct
  exact hdct

/-- Helper: the outside of a closed ball as a set-of-norm predicate is measurable. -/
theorem measurableSet_norm_gt (n : ℕ) (r : ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin n) | r < ‖y‖} := by
  have h :
    {y : EuclideanSpace ℝ (Fin n) | r < ‖y‖} =
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)ᶜ := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, not_le, Set.mem_ofPred_eq, Set.mem_compl_iff]
  rw [h]
  exact Metric.isClosed_closedBall.measurableSet.compl

set_option maxHeartbeats 2000000 in
/-- **Translation modulus lemma** (the `(T)`-lemma): for a continuous pdf `f` with finite first
moment, the weighted translation modulus
`G(u) = ∫ (1 + ‖x‖) * |f (x − u) − f x| ∂volume`
tends to `0` along every sequence `u k → 0`. Continuity of `f` makes the core contribution a
plain dominated convergence, and the tails are controlled by the first moment (using the
translation invariance of `volume`). -/
public theorem weighted_modulus_tendsto_seq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (u : ℕ → EuclideanSpace ℝ (Fin n)) (hu : Filter.Tendsto u Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u k : Fin n → ℝ))) - f x| ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwfint :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) volume := by
    have heq :
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) = fun x : EuclideanSpace ℝ (Fin n) =>
        f x + ‖x‖ * f x := by
      funext x; ring
    rw [heq]; exact hfi.add hfmom
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  -- the moment-tail lemma applied to `w * f`
  have htail :=
    setIntegral_tail_tendsto n (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) hwfint hwnonneg
  -- fix `k₀` with `‖u (k + k₀)‖ < 1` for all `k`
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hu 1 one_pos)
  have hu1 : ∀ k : ℕ, ‖u (k + k₀)‖ < 1 := by
    intro k
    have h := hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    rw [dist_zero_right] at h
    exact h
  -- the shifted sequence `u (· + k₀)` still tends to `0`
  have hu' : Filter.Tendsto (fun k : ℕ => u (k + k₀)) Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hu δ hδ)
    exact
      Filter.eventually_atTop.mpr
        ⟨N, fun k hk => hN (k + k₀) (Nat.le_trans hk (Nat.le_add_right k k₀))⟩
  -- main claim for the shifted sequence
  have hmain :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume)
      Filter.atTop (nhds 0) := by
    classical
    have hfm : Measurable f := hf.measurable
    -- the norm triangle for the shifted vector
    have htri :
      ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖ + ‖u (k + k₀)‖ := by
      intro k x
      have heq :
        x =
          WithLp.toLp 2
            (((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) + (u (k + k₀) : Fin n → ℝ)) := by
        apply WithLp.ofLp_injective
        show
          (x : Fin n → ℝ) = ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) + (u (k + k₀) : Fin n → ℝ)
        rw [sub_add_cancel]
      rw [show
          ‖x‖ =
            ‖WithLp.toLp 2
                (((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) + (u (k + k₀) : Fin n → ℝ))‖
          from congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) heq,
        WithLp.toLp_add]
      exact
        norm_add_le (a := WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) (b :=
          WithLp.toLp 2 ((u (k + k₀) : Fin n → ℝ)))
    -- the weighted bound `w(x) ≤ (1 + ‖u‖) * (1 + ‖x − u‖)`
    have hbnd :
      ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| ≤
          (1 + ‖u (k + k₀)‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) := by
      intro k x
      rw [abs_of_nonneg (hf0 _)]
      have hnorm :
        (1 + ‖x‖) ≤
          (1 + ‖u (k + k₀)‖) *
            (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) := by
        have hprod :
          0 ≤ ‖u (k + k₀)‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖ :=
          mul_nonneg (norm_nonneg (u (k + k₀)))
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))
        nlinarith [htri k x, hprod]
      exact mul_le_mul_of_nonneg_right hnorm (hf0 _)
    -- integrability of the shifted weighted `f` (transported from `hwfint`)
    have hshiftint :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖u (k + k₀)‖) *
              ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))))
          volume := by
      intro k
      have h1 :=
        integrable_toLp_shift n (-(u (k + k₀) : Fin n → ℝ))
          (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖u (k + k₀)‖) * ((1 + ‖z‖) * f z))
          (hwfint.const_mul (1 + ‖u (k + k₀)‖)) (by fun_prop)
      refine h1.congr' ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖u (k + k₀)‖) *
                  ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
                    f
                      (WithLp.toLp 2
                        ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))))).aestronglyMeasurable
      · filter_upwards with x
        show
          ‖(fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖u (k + k₀)‖) * ((1 + ‖z‖) * f z))
                (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ))))‖ =
            ‖(1 + ‖u (k + k₀)‖) *
                ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
                  f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))‖
        rw [sub_eq_add_neg]
    -- integrability of the full modulus integrand
    have hintg :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
          volume := by
      intro k
      refine MeasureTheory.Integrable.mono ((hshiftint k).add hwfint) ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) -
                      f x|)).aestronglyMeasurable
      · filter_upwards with x
        have habs :
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg
            (by positivity :
              0 ≤
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|),
          abs_of_nonneg
            (add_nonneg
              (mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
                (mul_nonneg
                  (by
                    linarith [norm_nonneg
                        (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))])
                  (hf0 _)))
              (hwnonneg x))]
        have hstep1 :
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
            (1 + ‖x‖) *
              (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x|) :=
          mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
        have hstep2 :
          (1 + ‖x‖) * (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x|) ≤
            (1 + ‖u (k + k₀)‖) *
                ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
                  f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) +
              (1 + ‖x‖) * f x := by
          rw [abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 x), mul_add, ← mul_assoc]
          have h2a := hbnd k x
          rw [abs_of_nonneg (hf0 _)] at h2a
          linarith [h2a]
        linarith [hstep1, hstep2]
    -- ε-proof
    refine Metric.tendsto_nhds.mpr ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδε⟩ : ∃ δ, 0 < δ ∧ ε = 4 * δ := ⟨ε / 4, by linarith, by field_simp⟩
    obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_nhds.mp htail δ hδpos).exists
    have hK₁' :
      ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume < δ := by
      have h0 :
        0 ≤ ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.setIntegral_nonneg (measurableSet_norm_gt n (K₁ : ℝ)) (fun x _ => hwnonneg x)
      have h := hK₁
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at h
    -- a bound for `|f|` on the ball of radius `(K₁ : ℝ) + 2`
    obtain ⟨B₀, hB₀⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n))
            ((K₁ : ℝ) + 2)).exists_bound_of_continuousOn
        (hf.abs.continuousOn)
    obtain ⟨B, hB0, hBmax⟩ :
      ∃ B, 0 ≤ B ∧ ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ≤ (K₁ : ℝ) + 2 → |f z| ≤ B := by
      refine ⟨max B₀ 0, le_max_right _ _, fun z hz => ?_⟩
      have hz' : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((K₁ : ℝ) + 2) :=
        Metric.mem_closedBall.mpr
          (by
            rw [dist_zero_right]; linarith)
      have hzn := hB₀ z hz'
      simp only [Real.norm_eq_abs, abs_abs] at hzn
      linarith [hzn, le_max_left B₀ 0]
    have hcoreBall :
      {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((K₁ : ℝ) + 1) := by
      ext y
      simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
    have hmeasCore : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := by
      rw [hcoreBall]
      exact Metric.isClosed_closedBall.measurableSet
    -- the core DCT
    have hdom :
      ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        |{y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
              x| ≤
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)) x := by
      intro k x
      rcases le_or_gt ‖x‖ ((K₁ : ℝ) + 1) with hcore | hcore
      · have hmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := hcore
        simp only [Set.indicator_of_mem hmem]
        have hz' : ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖ ≤ (K₁ : ℝ) + 2 := by
          show ‖(x - u (k + k₀) : EuclideanSpace ℝ (Fin n))‖ ≤ (K₁ : ℝ) + 2
          have hns : ‖(x - u (k + k₀) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x‖ + ‖u (k + k₀)‖ :=
            norm_sub_le _ _
          nlinarith [hns, hu1 k, hcore, norm_nonneg (u (k + k₀))]
        have habs :
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        rw [abs_of_nonneg
            (by positivity :
              0 ≤
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)]
        have h5 : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| ≤ B :=
          hBmax _ hz'
        have h6 : |f x| ≤ B := hBmax x (by linarith [hcore])
        have h7a :
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| ≤
            (1 + ((K₁ : ℝ) + 1)) * B := by
          refine le_trans (mul_le_mul_of_nonneg_left h5 (by linarith [norm_nonneg x])) ?_
          exact mul_le_mul_of_nonneg_right (by linarith [hcore]) (by linarith [hB0])
        have h7b : (1 + ‖x‖) * |f x| ≤ (1 + ((K₁ : ℝ) + 1)) * B := by
          refine le_trans (mul_le_mul_of_nonneg_left h6 (by linarith [norm_nonneg x])) ?_
          exact mul_le_mul_of_nonneg_right (by linarith [hcore]) (by linarith [hB0])
        refine le_trans (mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])) ?_
        rw [mul_add]
        have h7c :
          (1 + ((K₁ : ℝ) + 1)) * (2 * B) = (1 + ((K₁ : ℝ) + 1)) * B + (1 + ((K₁ : ℝ) + 1)) * B := by
          ring
        linarith [h7a, h7b, h7c]
      · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := not_le.mpr hcore
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    have hlim :
      ∀ᵐ x ∂volume,
        Filter.Tendsto
          (fun k : ℕ =>
            {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
              x)
          Filter.atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
      filter_upwards with x
      rcases le_or_gt ‖x‖ ((K₁ : ℝ) + 1) with hcore | hcore
      · have hmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := hcore
        simp only [Set.indicator_of_mem hmem]
        have hG :
          Continuous
            (fun v : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (v : Fin n → ℝ))) - f x|) := by
          fun_prop
        have h1 := Filter.Tendsto.comp (hG.tendsto (0 : EuclideanSpace ℝ (Fin n))) hu'
        have hcong :
          ∀ k : ℕ,
            ((fun v : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (v : Fin n → ℝ))) - f x|) ∘
                  (fun k : ℕ => u (k + k₀)))
                k =
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| :=
          fun k => rfl
        simpa using Filter.Tendsto.congr hcong h1
      · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := not_le.mpr hcore
        simp only [Set.indicator_of_notMem hmem]
        exact tendsto_const_nhds
    have hboundint :
      MeasureTheory.Integrable
        ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)))
        volume := by
      refine ⟨(measurable_const.indicator hmeasCore).aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have h2 :
        (fun x : EuclideanSpace ℝ (Fin n) =>
            ‖{y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
                (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)) x‖ₑ) =
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun _ => ENNReal.ofReal ((1 + ((K₁ : ℝ) + 1)) * (2 * B))) := by
        funext x
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) with hx | hx
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (by positivity)]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp
      rw [h2, MeasureTheory.lintegral_indicator_const hmeasCore]
      have hmeas : volume {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} < ⊤ := by
        rw [hcoreBall]
        exact measure_closedBall_lt_top
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmeas
    have hdct :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)))
        (f := fun _ => (0 : ℝ))
        (fun k =>
          (((by fun_prop :
                  Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖x‖) *
                      |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) -
                          f x|)).indicator
              hmeasCore).aestronglyMeasurable)
        hboundint (fun k => Filter.Eventually.of_forall fun x => hdom k x) hlim
    rw [integral_zero] at hdct
    have hdct' :
      Filter.Tendsto
        (fun k : ℕ =>
          ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
            (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume)
        Filter.atTop (𝓝 0) := by
      refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) hdct
      exact
        MeasureTheory.integral_indicator (s := {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1})
          hmeasCore
    -- the tail bound `T1 < 2δ` via the transport of the shifted indicator
    -- the tail bound `T1 < 2δ` via the transport of the shifted indicator
    have hψ₂meas :
      Measurable
        ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
          (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)) :=
      ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)).indicator
        (measurableSet_norm_gt n (K₁ : ℝ))
    have hψ₂int :
      MeasureTheory.Integrable
        ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
          (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z))
        volume := by
      refine MeasureTheory.Integrable.mono hwfint ?_ ?_
      · exact hψ₂meas.aestronglyMeasurable
      · filter_upwards with x
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}) with hmem | hmem
        · simp only [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (hwnonneg x)]
          exact le_refl _
        · simp only [Set.indicator_of_notMem hmem, Real.norm_eq_abs, abs_zero]
          exact abs_nonneg _
    have hT1intall :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x)
          volume := by
      intro k
      refine MeasureTheory.Integrable.mono (hshiftint k) ?_ ?_
      · exact
          (((by fun_prop :
                  Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖x‖) *
                      |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)).indicator
              (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
      · filter_upwards with x
        have hχpos :
          0 ≤
            (1 + ‖u (k + k₀)‖) *
              ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) :=
          mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
            (mul_nonneg
              (by
                linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))])
              (hf0 _))
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem,
            abs_of_nonneg
              (by positivity :
                0 ≤ (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|),
            abs_of_nonneg hχpos, ← mul_assoc]
          exact hbnd k x
        · rw [Set.indicator_of_notMem hmem, abs_zero, abs_of_nonneg hχpos]
          exact hχpos
    have hT1 :
      ∀ k : ℕ,
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x ∂volume <
          2 * δ := by
      intro k
      have hψ₂shift :
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
              (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))
          volume := by
        have h2 :=
          integrable_toLp_shift n (-(u (k + k₀) : Fin n → ℝ))
            ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z))
            hψ₂int hψ₂meas
        refine h2.congr' ?_ ?_
        · exact
            ((by fun_prop :
                Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                  {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                    (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                    (WithLp.toLp 2
                      ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))).aestronglyMeasurable
        · filter_upwards with x
          show
            ‖{y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                  (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ))))‖ =
              ‖{y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                  (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))‖
          rw [sub_eq_add_neg]
      have hT1int := hT1intall k
      have hpt :
        ∀ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x ≤
            (1 + ‖u (k + k₀)‖) *
              ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) := by
        intro x
        rcases le_or_gt ‖x‖ ((K₁ : ℝ) + 1) with hout | hin
        · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} := not_lt.mpr hout
          rw [Set.indicator_of_notMem hmem]
          have hpos :
            0 ≤
              (1 + ‖u (k + k₀)‖) *
                ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                  (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) := by
            rcases
              em
                ((WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) ∈
                  {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}) with
              hm | hm
            · rw [Set.indicator_of_mem hm]
              exact
                mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
                  (mul_nonneg
                    (by
                      linarith [norm_nonneg
                          (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))])
                    (hf0 _))
            · rw [Set.indicator_of_notMem hm]
              exact mul_nonneg (by linarith [norm_nonneg (u (k + k₀))]) (le_refl 0)
          exact hpos
        · have hmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} := hin
          have hzmem :
            (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) ∈
              {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖} := by
            show (K₁ : ℝ) < ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖
            linarith [htri k x, hu1 k, hin]
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzmem, ← mul_assoc]
          exact hbnd k x
      have hchain :
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x ∂volume ≤
          ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖u (k + k₀)‖) *
              ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) ∂volume :=
        MeasureTheory.integral_mono hT1int (hψ₂shift.const_mul (1 + ‖u (k + k₀)‖)) hpt
      rw [MeasureTheory.integral_const_mul (1 + ‖u (k + k₀)‖)] at hchain
      have htransport :
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
              (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ)))) ∂volume =
          ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume := by
        rw [integral_toLp_trans_right n (-(u (k + k₀) : Fin n → ℝ))
            ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z))
            hψ₂meas.aestronglyMeasurable,
          integral_indicator (measurableSet_norm_gt n (K₁ : ℝ))]
      simp only [sub_eq_add_neg] at hchain
      rw [htransport] at hchain
      refine lt_of_le_of_lt hchain ?_
      have hint :
        0 ≤ ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.setIntegral_nonneg (measurableSet_norm_gt n (K₁ : ℝ)) (fun x _ => hwnonneg x)
      exact
        lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right
            (show (1 + ‖u (k + k₀)‖ : ℝ) ≤ 2 by linarith [norm_nonneg (u (k + k₀)), hu1 k]) hint)
          (mul_lt_mul_of_pos_left hK₁' (show (0 : ℝ) < 2 by norm_num))
    -- the `f`-tail bound `T2 < δ`
    have hT2 :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume <
        δ := by
      have hT2int :
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x)
          volume := by
        refine MeasureTheory.Integrable.mono hwfint ?_ ?_
        · exact
            (((by fun_prop :
                    Measurable fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)).indicator
                (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
        · filter_upwards with x
          simp only [Real.norm_eq_abs]
          rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
          · rw [Set.indicator_of_mem hmem, abs_of_nonneg (hwnonneg x)]
          · rw [Set.indicator_of_notMem hmem, abs_zero]
            exact abs_nonneg _
      have hpt :
        ∀ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ≤
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x := by
        intro x
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
        · have hmem' : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖} := by
            show (K₁ : ℝ) < ‖x‖
            linarith [show ((K₁ : ℝ) + 1 : ℝ) < ‖x‖ from hmem]
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
        · rw [Set.indicator_of_notMem hmem]
          rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}) with hmem2 | hmem2
          · rw [Set.indicator_of_mem hmem2]
            exact mul_nonneg (by linarith [norm_nonneg x]) (hf0 x)
          · rw [Set.indicator_of_notMem hmem2]
      have hint2 :
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume =
          ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.integral_indicator (measurableSet_norm_gt n (K₁ : ℝ))
      exact
        lt_of_le_of_lt (MeasureTheory.integral_mono hT2int hψ₂int hpt)
          (lt_of_le_of_lt (le_of_eq hint2) hK₁')
    -- assemble
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hdct' δ hδpos)
    refine Filter.eventually_atTop.mpr ⟨N₁, fun k hk => ?_⟩
    have hA :
      ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
          (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume <
        δ := by
      have h0 :
        0 ≤
          ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
            (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
        MeasureTheory.setIntegral_nonneg hmeasCore (fun x _ => by positivity)
      have h := hN₁ k hk
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at h
    have hAint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
            x)
        volume := by
      refine MeasureTheory.Integrable.mono (hintg k) ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
                  (fun x : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖x‖) *
                      |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
                  x)).aestronglyMeasurable
      · filter_upwards with x
        have hχpos :
          0 ≤
            (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| := by
          positivity
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem, abs_of_nonneg hχpos]
        · rw [Set.indicator_of_notMem hmem, abs_zero]
          exact abs_nonneg _
    have hT2int :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x)
        volume := by
      refine MeasureTheory.Integrable.mono hwfint ?_ ?_
      · exact
          (((by fun_prop :
                  Measurable fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)).indicator
              (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
      · filter_upwards with x
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem, abs_of_nonneg (hwnonneg x)]
        · rw [Set.indicator_of_notMem hmem, abs_zero]
          exact abs_nonneg _
    have hpoint :
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
          ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
                (fun x : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖x‖) *
                    |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|))
              x +
            ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
                (fun x : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|))
              x +
            ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
                (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x))
              x := by
      intro x
      rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) with hmem | hmem
      · have hmem' : ‖x‖ ≤ (K₁ : ℝ) + 1 := by simpa only [Set.mem_ofPred_eq] using hmem
        have hmem2 : x ∉ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} := not_lt.mpr hmem'
        have hT1rw :
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x =
            0 := by
          rw [Set.indicator_of_notMem hmem2]
        have hT2rw :
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x =
            0 := by
          rw [Set.indicator_of_notMem hmem2]
        simp only [Set.indicator_of_mem hmem, hT1rw, hT2rw]
        linarith [abs_nonneg
            ((1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)]
      · have hmem' : ¬(‖x‖ ≤ (K₁ : ℝ) + 1) := by simpa only [Set.mem_ofPred_eq] using hmem
        have hmem2 : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} := not_le.mp hmem'
        have hT1rw :
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x =
            (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| := by
          rw [Set.indicator_of_mem hmem2]
        have hT2rw :
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x =
            (1 + ‖x‖) * f x := by
          rw [Set.indicator_of_mem hmem2]
        rw [Set.indicator_of_notMem hmem, hT1rw, hT2rw]
        have habs :
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        have hstep1 :
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ≤
            (1 + ‖x‖) *
              (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x|) :=
          mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
        rw [mul_add, abs_of_nonneg (hf0 x)] at hstep1
        linarith [hstep1]
    have hgnonneg :
      0 ≤
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
      MeasureTheory.integral_nonneg (fun x => by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hgnonneg]
    have h1 := MeasureTheory.integral_mono (hintg k) ((hAint.add (hT1intall k)).add hT2int) hpoint
    refine lt_of_le_of_lt h1 ?_
    rw [MeasureTheory.integral_add' (hAint.add (hT1intall k)) hT2int,
      MeasureTheory.integral_add' hAint (hT1intall k)]
    have hT2pos :
      ∀ x : EuclideanSpace ℝ (Fin n),
        0 ≤
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x' : EuclideanSpace ℝ (Fin n) => (1 + ‖x'‖) * f x') x := by
      intro x
      rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
      · rw [Set.indicator_of_mem hmem]
        exact mul_nonneg (by linarith [norm_nonneg x]) (hf0 x)
      · rw [Set.indicator_of_notMem hmem]
    have hT2le :
      ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
              x ∂volume +
          ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x ∂volume ≤
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
              x ∂volume +
          ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)
              x ∂volume +
          ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume :=
      le_add_of_nonneg_right (MeasureTheory.integral_nonneg hT2pos)
    have hAeq :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
            x ∂volume =
        ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
          (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
      MeasureTheory.integral_indicator hmeasCore
    linarith [hT2le, hA, hAeq, hT1 k, hT2, hδε]
  exact (Filter.tendsto_add_atTop_iff_nat k₀).mp hmain

/-- Translation invariance of Bochner integrals, in the `y − c` form (cf.
`integral_toLp_trans_right`). -/
theorem integral_shift_neg {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [OpensMeasurableSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [SecondCountableTopology F] (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)) ∂volume =
      ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show
      (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) - c))) =
        fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + (-c)))
      from by
      funext y; rw [sub_eq_add_neg]]
  exact integral_toLp_trans_right n (-c) g hg

/-- Translation invariance of Lebesgue integrals, in the `y − c` form. -/
theorem lintegral_shift_neg (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)) ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show
      (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) - c))) =
        fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + (-c)))
      from by
      funext y; rw [sub_eq_add_neg]]
  exact lintegral_toLp_trans_right n (-c) g hg

/-- Lebesgue mass of the mollifier: `∫⁻ ψ_σ = 1`. -/
theorem lintegral_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) :
    ∫⁻ u : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (mollifier n C hC σ hσ u) ∂volume = 1 := by
  classical
  -- the pointwise ofReal-split, typed (the ∫⁻ keeps the opaque mollifier)
  have hpt :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC σ hσ u) =
        ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          ENNReal.ofReal
            (multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))) := by
    intro u
    simp only [mollifier]
    exact ENNReal.ofReal_mul (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n)
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- the scaling transport: ∫⁻ (ofReal ∘ φ_C ∘ (·/σ)) ∂volume = (σ^n) • ∫⁻ (ofReal ∘ φ_C)
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hTapp : ∀ u : EuclideanSpace ℝ (Fin n), T u = WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)) :=
    fun u => toEuclideanLin_smul_one n ((σ : ℝ)⁻¹) u
  have hFmeas' :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (multivariateGaussianPDF n 0 C hC z)) :=
    Measurable.ennreal_ofReal (measurable_multivariateGaussianPDF n 0 C hC)
  have hLdet : (LinearMap.det T) = (σ : ℝ)⁻¹ ^ n := by
    show
      (LinearMap.det
          (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
            ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)))) =
        (σ : ℝ)⁻¹ ^ n
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
  have hLne : (LinearMap.det T) ≠ 0 := by
    rw [hLdet]
    exact pow_ne_zero n (ne_of_gt (inv_pos.mpr hσ))
  have hLabs : ENNReal.ofReal |(LinearMap.det T)⁻¹| = ENNReal.ofReal (σ ^ n) := by
    rw [hLdet, inv_pow, inv_inv, abs_of_pos (pow_pos hσ n)]
  have hptr :
    (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          ENNReal.ofReal
            (multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (a : Fin n → ℝ))))) =
      fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) * ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) := by
    funext a; rw [hTapp]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall (funext_iff.mp hptr))]
  have hFmeas :
    Measurable
      (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a))) :=
    hFmeas'.comp (by fun_prop : Measurable T)
  have htrans :
    ∫⁻ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) ∂(Measure.map T volume) :=
    (MeasureTheory.lintegral_map hFmeas' (by fun_prop : Measurable T)).symm
  have hφint : MeasureTheory.Integrable (multivariateGaussianPDF n 0 C hC) volume :=
    integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC)
  have hφnn : 0 ≤ᵐ[volume] multivariateGaussianPDF n 0 C hC :=
    Filter.Eventually.of_forall fun x => le_of_lt (multivariateGaussianPDF_pos n 0 C hC x)
  have hφlint :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) ∂volume =
      1 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hφint hφnn,
      integral_gaussianPDF n 0 C hC, ENNReal.ofReal_one]
  rw [lintegral_const_mul (ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n)) hFmeas, htrans,
    MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLabs,
    lintegral_smul_measure, hφlint, smul_eq_mul]
  -- goal: ofReal ((σ⁻¹)^n) * (ofReal (σ^n) * 1) = 1
  rw [mul_one, mul_comm, ← ENNReal.ofReal_mul (pow_nonneg (le_of_lt hσ) n), inv_pow,
    mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), ENNReal.ofReal_one]

/-- The mollifier is bounded by its peak value at the origin: the centered Gaussian pdf
is maximal at its mean (the quadratic form in the exponent is nonnegative). -/
theorem mollifier_le_zero (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (u : EuclideanSpace ℝ (Fin n)) :
    mollifier n C hC σ hσ u ≤ mollifier n C hC σ hσ 0 := by
  have hd :
    mollifier n C hC σ hσ u =
      (σ : ℝ)⁻¹ ^ n *
        multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) :=
    rfl
  rw [hd, mollifier]
  have h0 : ((0 : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = 0 := rfl
  rw [h0, smul_zero]
  refine
    le_trans
      (mul_le_mul_of_nonneg_left (multivariateGaussianPDF_le_const n 0 C hC _)
        (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n))
      ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n)
  rw [multivariateGaussianPDF_eq n 0 C hC]
  simp

/-- The mollifier is integrable (measurable, with Lebesgue mass one). -/
theorem mollifier_integrable (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) : MeasureTheory.Integrable (mollifier n C hC σ hσ) volume := by
  have hψmeas : Measurable (mollifier n C hC σ hσ) := by
    show
      Measurable
        (fun u : EuclideanSpace ℝ (Fin n) =>
          (σ : ℝ)⁻¹ ^ n *
            multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
    exact
      ((measurable_multivariateGaussianPDF n 0 C hC).comp
            (by fun_prop :
              Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul
        ((σ : ℝ)⁻¹ ^ n)
  have hnn : 0 ≤ᵐ[volume] mollifier n C hC σ hσ :=
    Filter.Eventually.of_forall fun u => mollifier_nonneg n C hC σ hσ u
  refine ⟨hψmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn, lintegral_mollifier n C hC σ hσ]
  exact ENNReal.one_lt_top

/-- The first moment of the mollifier in Lebesgue form:
`∫⁻ ψ_σ(u) * ‖u‖ₑ = ofReal (σ * M_φ)` where `M_φ = ∫ ‖v‖ * φ_C v ∂volume`, proved by the same
linear-change-of-variables transport as `lintegral_mollifier`. -/
theorem lintegral_mollifier_mul_norm (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) :
    ∫⁻ u : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC σ hσ u) * ENNReal.ofReal ‖u‖ ∂volume =
      ENNReal.ofReal
        (σ * ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
  classical
  -- the pointwise ofReal-split, typed (the ∫⁻ keeps the opaque mollifier)
  have hpt :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC σ hσ u) * ENNReal.ofReal ‖u‖ =
        ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          (ENNReal.ofReal
              (multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))) *
            ENNReal.ofReal ‖u‖) := by
    intro u
    simp only [mollifier]
    rw [ENNReal.ofReal_mul (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n), mul_assoc]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- the scaling transport
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hTapp : ∀ u : EuclideanSpace ℝ (Fin n), T u = WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)) :=
    fun u => toEuclideanLin_smul_one n ((σ : ℝ)⁻¹) u
  have hnormT :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal ‖u‖ = ENNReal.ofReal σ * ENNReal.ofReal ‖T u‖ := by
    intro u
    rw [← ENNReal.ofReal_mul (le_of_lt hσ)]
    congr 1
    rw [hTapp u, show (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) = (σ : ℝ)⁻¹ • u from rfl,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ), ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hσ), one_mul]
  have hptr :
    (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          (ENNReal.ofReal
              (multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (a : Fin n → ℝ)))) *
            ENNReal.ofReal ‖a‖)) =
      fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
        (ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) * ENNReal.ofReal ‖T a‖) := by
    funext a
    rw [← hTapp, hnormT a]
    ring
  rw [lintegral_congr_ae (Filter.Eventually.of_forall (funext_iff.mp hptr))]
  have hGmeas :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC z) * ENNReal.ofReal ‖z‖) :=
    (Measurable.ennreal_ofReal (measurable_multivariateGaussianPDF n 0 C hC)).mul
      (Measurable.ennreal_ofReal continuous_norm.measurable)
  have hGTmeas :
    Measurable
      (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) * ENNReal.ofReal ‖T a‖) :=
    hGmeas.comp (by fun_prop : Measurable T)
  rw [lintegral_const_mul (ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n)) hGTmeas]
  -- the transport of ∫⁻ G̃ (T a) to ∫⁻ G̃ y
  have htrans :
    ∫⁻ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) * ENNReal.ofReal ‖T a‖ ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) *
          ENNReal.ofReal ‖y‖ ∂(Measure.map T volume) :=
    (MeasureTheory.lintegral_map hGmeas (by fun_prop : Measurable T)).symm
  have hLdet : (LinearMap.det T) = (σ : ℝ)⁻¹ ^ n := by
    show
      (LinearMap.det
          (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
            ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)))) =
        (σ : ℝ)⁻¹ ^ n
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
  have hLne : (LinearMap.det T) ≠ 0 := by
    rw [hLdet]
    exact pow_ne_zero n (ne_of_gt (inv_pos.mpr hσ))
  have hLabs : ENNReal.ofReal |(LinearMap.det T)⁻¹| = ENNReal.ofReal (σ ^ n) := by
    rw [hLdet, inv_pow, inv_inv, abs_of_pos (pow_pos hσ n)]
  have hMoφint :
    MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ * multivariateGaussianPDF n 0 C hC v) volume :=
    integrable_norm_mul_gaussianPDF_center n C hC
  have hMoφnn :
    0 ≤ᵐ[volume] (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ * multivariateGaussianPDF n 0 C hC v) :=
    Filter.Eventually.of_forall fun v =>
      mul_nonneg (norm_nonneg v) (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  have hGval :
    ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) * ENNReal.ofReal ‖y‖ ∂volume =
      ENNReal.ofReal
        (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * multivariateGaussianPDF n 0 C hC y ∂volume) := by
    rw [lintegral_congr_ae
        (Filter.Eventually.of_forall fun y => by
          rw [mul_comm, ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMoφint hMoφnn]
  rw [htrans, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLabs,
    lintegral_smul_measure, hGval, smul_eq_mul]
  -- goal: (sₑ · σ⁻ⁿₑ) * (σⁿₑ · Mₑ) = ofReal (σ * M)
  have hMnn :
    0 ≤ ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume :=
    MeasureTheory.integral_nonneg fun v =>
      mul_nonneg (norm_nonneg v) (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  have hcancel : ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) * ENNReal.ofReal (σ ^ n) = 1 := by
    rw [inv_pow, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (pow_pos hσ n))),
      inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), ENNReal.ofReal_one]
  rw [ENNReal.ofReal_mul (le_of_lt hσ)]
  have hfin :
    ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
        (ENNReal.ofReal (σ ^ n) *
          ENNReal.ofReal
            (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * multivariateGaussianPDF n 0 C hC y)) =
      ENNReal.ofReal σ *
        ENNReal.ofReal
          (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * multivariateGaussianPDF n 0 C hC y) := by
    rw [mul_assoc, ←
      mul_assoc (ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n)) (ENNReal.ofReal (σ ^ n))
        (ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * multivariateGaussianPDF n 0 C hC y)),
      hcancel, one_mul]
  rw [hfin]

/-- The Gaussian-smoothed prior is a pdf (nonnegative with mass 1). -/
public theorem isPdf_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hpdf : IsPdf f)
    (hfm : Measurable f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    IsPdf (gaussSmoothed n f C hC σ hσ) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψmeas' : Measurable (mollifier n C hC σ hσ) := by
    show
      Measurable
        (fun u : EuclideanSpace ℝ (Fin n) =>
          (σ : ℝ)⁻¹ ^ n *
            multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
    exact
      ((measurable_multivariateGaussianPDF n 0 C hC).comp
            (by fun_prop :
              Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul
        ((σ : ℝ)⁻¹ ^ n)
  have hgnonneg :
    ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤
        ∫ u : EuclideanSpace ℝ (Fin n),
          mollifier n C hC σ hσ u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume :=
    fun x =>
    MeasureTheory.integral_nonneg (fun u => mul_nonneg (mollifier_nonneg n C hC σ hσ u) (hf0 _))
  refine ⟨?_, ?_⟩
  · exact hgnonneg
  · -- the mass via Fubini over the pair (x, u)
    have hflint : ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖f x‖ₑ ∂volume = 1 := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n), ‖f x‖ₑ = ENNReal.ofReal (f x) := fun x =>
        Real.enorm_eq_ofReal (hf0 x)
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt), ←
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
        hpdf.2]
      exact ENNReal.ofReal_one
    have hshift :
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
            ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ ∂volume =
          1 :=
      fun u => by
      rw [lintegral_shift_neg n (u : Fin n → ℝ) (fun x => ‖f x‖ₑ) hfm.enorm]
      exact hflint
    -- the joint integrand on the pair (x, u)
    have hΦmeas :
      Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC σ hσ p.1 * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) :=
      ((hψmeas'.comp
            (by fun_prop :
              Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1)).mul
        (hfm.comp
          (by fun_prop :
            Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
    -- joint integrability: Tonelli with the pair's FIRST coordinate carrying ψ,
    -- so the inner ∫⁻_x sees ψ as a constant and is transportable
    have hΦint :
      MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC σ hσ p.1 * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))
        (volume.prod volume) := by
      refine ⟨?_, ?_⟩
      · exact
          ((hψmeas'.comp
                  (by fun_prop :
                    Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                      p.1)).mul
              (hfm.comp
                (by fun_prop :
                  Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                    WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))).aestronglyMeasurable
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (MeasureTheory.lintegral_prod_le _) ?_
      -- the inner ∫⁻ transport: the ∫⁻_y integrand becomes the ψ·‖f‖ₑ split form
      have hpt :
        ∀ x y : EuclideanSpace ℝ (Fin n),
          ‖(fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                  mollifier n C hC σ hσ q.1 *
                    f (WithLp.toLp 2 ((q.2 : Fin n → ℝ) - (q.1 : Fin n → ℝ))))
                (x, y)‖ₑ =
            ENNReal.ofReal (mollifier n C hC σ hσ x) *
              ENNReal.ofReal (f (WithLp.toLp 2 ((y : Fin n → ℝ) - (x : Fin n → ℝ)))) := by
        intro x y
        rw [Real.enorm_eq_ofReal
            (mul_nonneg (mollifier_nonneg n C hC σ hσ x)
              (hf0 (WithLp.toLp 2 ((y : Fin n → ℝ) - (x : Fin n → ℝ))))),
          ENNReal.ofReal_mul (mollifier_nonneg n C hC σ hσ x)]
      rw [lintegral_congr_ae
          (Filter.Eventually.of_forall fun x => by
            exact lintegral_congr_ae (Filter.Eventually.of_forall (hpt x)))]
      -- the inner ∫⁻: ofReal (ψ a) · ofReal (f(·−a)) = ofReal (ψ a) · ‖f‖ₑ-form,
      --   then the transportable shift
      have hinner :
        ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal (mollifier n C hC σ hσ a) *
                ENNReal.ofReal (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))) ∂volume =
            ENNReal.ofReal (mollifier n C hC σ hσ a) := by
        intro a
        have hmeas' :
          Measurable
            (fun b : EuclideanSpace ℝ (Fin n) =>
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) := by
          have heq :
            (fun b : EuclideanSpace ℝ (Fin n) =>
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) =
              (fun x => ‖f x‖ₑ) ∘ fun b : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) :=
            rfl
          rw [heq]
          exact hfm.enorm.comp (by fun_prop)
        have hfpt :
          ∀ b : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC σ hσ a) *
                ENNReal.ofReal (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))) =
              ENNReal.ofReal (mollifier n C hC σ hσ a) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ := by
          intro b
          rw [(Real.enorm_eq_ofReal (hf0 _)).symm]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hfpt),
          MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC σ hσ a)) hmeas',
          hshift a, mul_one]
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hinner), lintegral_mollifier]
      exact ENNReal.one_lt_top
    -- the mass: ∫_x gaussSmoothed x dx = ∫_u ψ(u)·(∫_x f(x−u) dx) du = ∫_u ψ(u) du = 1
    have hAint' :
      MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC σ hσ p.2 * f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))
        (volume.prod volume) := by
      have hmp :
        MeasureTheory.MeasurePreserving
          (Prod.swap :
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
          (volume.prod volume) (volume.prod volume) :=
        MeasureTheory.Measure.measurePreserving_swap
      exact (hmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint
    have hshiftmass :
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∫ x : EuclideanSpace ℝ (Fin n),
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume =
          1 := by
      intro u
      rw [integral_shift_neg n (u : Fin n → ℝ) f hfi.1]
      exact hpdf.2
    show
      ∫ x : EuclideanSpace ℝ (Fin n),
          ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC σ hσ u *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume ∂volume =
        1
    rw [←
      MeasureTheory.integral_prod (f :=
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ p.2 * f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))
        hAint',
      ←
      MeasureTheory.integral_prod_swap (f :=
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ p.2 * f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))]
    -- the swapped-pair congr: the projs reduce (z.swap.2 = z.1, z.swap.1 = z.2),
    -- turning the integrand into the Φ form with ψ on the FIRST coordinate
    have hcongr :
      ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        mollifier n C hC σ hσ z.swap.2 *
            f (WithLp.toLp 2 ((z.swap.1 : Fin n → ℝ) - (z.swap.2 : Fin n → ℝ))) =
          mollifier n C hC σ hσ z.1 *
            f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) := by
      intro z
      simp [Prod.swap]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_prod (f :=
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ p.1 * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) (μ :=
        volume) (ν := volume) hΦint,
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => by
          rw [MeasureTheory.integral_const_mul (mollifier n C hC σ hσ x), hshiftmass x, mul_one]),
      integral_mollifier]

/-- The weighted translation modulus (the `(T)`-integrand of `weighted_modulus_tendsto_seq`,
packaged as a function of the shift `u`):
`G(u) = ∫ (1 + ‖x‖) * |f (x − u) − f x| ∂volume`. -/
public noncomputable def weightedModulus (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin n),
    (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume

/-- The weighted translation modulus satisfies the uniform bound
`G(u) ≤ (1 + M_f) * (2 + ‖u‖)`, where `M_f = ∫ ‖y‖ * f y ∂volume`: the shifted weighted mass
`∫ (1 + ‖x‖) f (x − u)` is at most `(1 + ‖u‖) (1 + M_f)` by the triangle inequality and the
translation invariance of `volume`. -/
public theorem weightedModulus_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfm : Measurable f)
    (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (u : EuclideanSpace ℝ (Fin n)) :
    weightedModulus n f u ≤
      (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  show
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume ≤
      (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖)
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  have heqw :
    (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) = fun x : EuclideanSpace ℝ (Fin n) =>
      f x + ‖x‖ * f x := by
    funext x; ring
  have hwfint :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) volume := by
    rw [heqw]; exact hfi.add hfmom
  have hmass :
    ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume =
      1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume := by
    rw [heqw, MeasureTheory.integral_add hfi hfmom, hpdf.2]
  -- the shifted weighted mass, as an integral of the translated integrand
  have hfuadd :
    (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) =
      fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖) *
        f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) := by
    funext x
    have heqx : (WithLp.toLp 2 ((u : Fin n → ℝ) + ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) = x := by
      rw [add_sub_cancel, WithLp.toLp_ofLp]
    rw [show (1 + ‖x‖) = 1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
        from congrArg (fun w : EuclideanSpace ℝ (Fin n) => 1 + ‖w‖) heqx.symm]
  have hfuM :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z) := by
    fun_prop
  have hfuin :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z)
      volume := by
    refine MeasureTheory.Integrable.mono' (hwfint.mul_const (1 + ‖u‖)) ?_ ?_
    · exact hfuM.aestronglyMeasurable
    · filter_upwards with z
      show
        ‖(1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z‖ ≤
          (1 + ‖z‖) * f z * (1 + ‖u‖)
      have hadd : (WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))) = u + z := rfl
      rw [hadd, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg (u + z)]) (hf0 z))]
      have htri : 1 + ‖u + z‖ ≤ (1 + ‖z‖) * (1 + ‖u‖) := by
        have h := norm_add_le u z
        have hexp : (1 + ‖z‖) * (1 + ‖u‖) = 1 + ‖u‖ + ‖z‖ + ‖z‖ * ‖u‖ := by ring
        rw [hexp]
        linarith [h, mul_nonneg (norm_nonneg z) (norm_nonneg u), norm_nonneg u, norm_nonneg z]
      calc
        (1 + ‖u + z‖) * f z ≤ (1 + ‖z‖) * (1 + ‖u‖) * f z := mul_le_mul_of_nonneg_right htri (hf0 z)
        _ = (1 + ‖z‖) * f z * (1 + ‖u‖) := by ring
  have hshift1 :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume =
      ∫ y : EuclideanSpace ℝ (Fin n),
        (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (y : Fin n → ℝ))‖) * f y ∂volume := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hfuadd x),
      integral_shift_neg n (u : Fin n → ℝ)
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z)
        hfuM.aestronglyMeasurable]
  have hb1 :
    ∫ y : EuclideanSpace ℝ (Fin n),
        (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (y : Fin n → ℝ))‖) * f y ∂volume ≤
      (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hR :
      ∫ y : EuclideanSpace ℝ (Fin n), (1 + ‖y‖) * f y * (1 + ‖u‖) ∂volume =
        (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
      rw [MeasureTheory.integral_mul_const (1 + ‖u‖), hmass, mul_comm]
    refine
      le_trans
        (MeasureTheory.integral_mono hfuin (hwfint.mul_const (1 + ‖u‖))
          (fun z => by
            show
              (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z ≤
                (1 + ‖z‖) * f z * (1 + ‖u‖)
            have hadd : (WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))) = u + z := rfl
            rw [hadd]
            have htri : 1 + ‖u + z‖ ≤ (1 + ‖z‖) * (1 + ‖u‖) := by
              have h := norm_add_le u z
              have hexp : (1 + ‖z‖) * (1 + ‖u‖) = 1 + ‖u‖ + ‖z‖ + ‖z‖ * ‖u‖ := by ring
              rw [hexp]
              linarith [h, mul_nonneg (norm_nonneg z) (norm_nonneg u), norm_nonneg u, norm_nonneg z]
            calc
              (1 + ‖u + z‖) * f z ≤ (1 + ‖z‖) * (1 + ‖u‖) * f z :=
                mul_le_mul_of_nonneg_right htri (hf0 z)
              _ = (1 + ‖z‖) * f z * (1 + ‖u‖) := by ring))
        (le_of_eq hR)
  -- |f (x−u) − f x| ≤ f (x−u) + f x, so the modulus splits
  have hsplit :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume ≤
      ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume +
        ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume := by
    have hA :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
        volume := by
      rw [hfuadd]
      exact
        integrable_toLp_shift n (-(u : Fin n → ℝ))
          (fun z : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z)
          hfuin hfuM
    have hintAB :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) + (1 + ‖x‖) * f x)
        volume :=
      hA.add hwfint
    have hLint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)
        volume := by
      refine MeasureTheory.Integrable.mono hintAB ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) -
                      f x|)).aestronglyMeasurable
      · filter_upwards with x
        have habs :
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ≤
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        rw [abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 x)] at habs
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg
            (by positivity :
              0 ≤ (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|),
          abs_of_nonneg
            (add_nonneg (mul_nonneg (by linarith [norm_nonneg x]) (hf0 _)) (hwnonneg x))]
        exact
          le_trans (mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x]))
            (le_of_eq (mul_add _ _ _))
    refine
      le_trans
        (MeasureTheory.integral_mono hLint hintAB
          (fun x => by
            have habs :
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ≤
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))| + |f x| :=
              abs_sub _ _
            rw [abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 x)] at habs
            have hstep1 :
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ≤
                (1 + ‖x‖) * (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) + f x) :=
              mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
            exact le_trans hstep1 (le_of_eq (mul_add _ _ _))))
        (le_of_eq (MeasureTheory.integral_add' hA hwfint))
  refine le_trans hsplit ?_
  rw [hshift1, hmass]
  refine le_trans (add_le_add hb1 (le_refl _)) ?_
  have hring :
    (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) +
        (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) =
      (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖) := by
    ring
  exact le_of_eq hring

/-- The weighted translation modulus is a.e.-measurable (it is the `x`-marginal integral of
the measurable joint function `(u, x) ↦ (1 + ‖x‖) * |f (x − u) − f x|`). -/
public theorem aemeasurable_weightedModulus (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) : AEMeasurable (weightedModulus n f) volume := by
  have hKmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := by
    fun_prop
  exact (hKmeas.stronglyMeasurable.integral_prod_right').aemeasurable

/-- Measurability of the mollifier. -/
public theorem measurable_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) : Measurable (mollifier n C hC σ hσ) := by
  show
    Measurable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        (σ : ℝ)⁻¹ ^ n *
          multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
  exact
    ((measurable_multivariateGaussianPDF n 0 C hC).comp
          (by fun_prop :
            Measurable fun u : EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul
      ((σ : ℝ)⁻¹ ^ n)

/-- Measurability of the ψ-weighted joint difference integrand (ψ on the first
coordinate). -/
public theorem measurable_joint_first (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
  have hψmeas := measurable_mollifier n C hC s hs
  fun_prop

/-- **Step A of the smoothing theorem**: the pointwise smoothing identity
`|f x − gaussSmoothed x| ≤ ∫ ψ_σ(u) |f (x − u) − f x| du`, via `∫ ψ_σ = 1`, the
subtraction identity and `|∫ g| ≤ ∫ |g|`; per-x integrability of the two subtracted
integrand factors follows from the reflection `u ↦ −u` (measure-preserving) and the
peak domination `ψ_σ(u) ≤ ψ_σ(0)`. -/
public theorem stepA_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfm : Measurable f)
    (hpdf : IsPdf f)
    (_hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    |f x - gaussSmoothed n f C hC s hs x| ≤
      ∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC s hs u *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume := by
  classical
  have hnegmp :
    MeasureTheory.MeasurePreserving (fun u : EuclideanSpace ℝ (Fin n) => -u) volume volume :=
    Measure.measurePreserving_neg _
  have hψint := mollifier_integrable n C hC s hs
  have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u := fun u =>
    mollifier_nonneg n C hC s hs u
  have hψ0le : ∀ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u ≤ mollifier n C hC s hs 0 :=
    mollifier_le_zero n C hC s hs
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψmeas := measurable_mollifier n C hC s hs
  have h2 :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs u * f x)
      volume :=
    hψint.mul_const (f x)
  have hshifted :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ))))
      volume :=
    integrable_toLp_shift n (x : Fin n → ℝ) f hfi hfm
  have hcomp :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ))))
          (-u))
      volume :=
    (hnegmp.integrable_comp hshifted.1).mpr hshifted
  have h3 :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
      volume := by
    have hcomp' :
      MeasureTheory.Integrable
        (fun u : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
        volume := by
      refine hcomp.congr' ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
      · filter_upwards with u
        show
          ‖f (WithLp.toLp 2 (((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) + (x : Fin n → ℝ)))‖ =
            ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
        congr 1
        simp only [WithLp.ofLp_neg]
        rw [add_comm, ← sub_eq_add_neg]
    refine MeasureTheory.Integrable.mono' (hcomp'.mul_const (mollifier n C hC s hs 0)) ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun u : EuclideanSpace ℝ (Fin n) =>
              mollifier n C hC s hs u *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
    · filter_upwards with u
      show
        ‖mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ ≤
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) * mollifier n C hC s hs 0
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψpos u), abs_of_nonneg (hf0 _)]
      exact le_trans (mul_le_mul_of_nonneg_right (hψ0le u) (hf0 _)) (le_of_eq (mul_comm _ _))
  have h1 : f x = ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u * f x ∂volume := by
    rw [MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun u => mul_comm (mollifier n C hC s hs u) (f x)),
      MeasureTheory.integral_const_mul (f x), integral_mollifier n C hC s hs, mul_one]
  have hsub :
    f x - gaussSmoothed n f C hC s hs x =
      ∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC s hs u *
          (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume := by
    conv_lhs => rw [h1]
    have hgs :
      gaussSmoothed n f C hC s hs x =
        ∫ u : EuclideanSpace ℝ (Fin n),
          mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume :=
      rfl
    rw [hgs, ← MeasureTheory.integral_sub h2 h3]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show
      mollifier n C hC s hs u * f x -
          mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) =
        mollifier n C hC s hs u * (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
    rw [mul_sub]
  rw [hsub]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun u => by
        rw [abs_mul, abs_of_nonneg (hψpos u),
          abs_sub_comm (f x) (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))])]

/-- **Step B of the smoothing theorem**: joint integrability of the ψ-weighted
difference integrand, ψ on the first coordinate (the `(T)`-lemma's Tonelli
orientation), via the ∫⁻ Tonelli bound with the mollifier's first moment. -/
public theorem integrable_joint_first (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
      (volume.prod volume) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u := fun u =>
    mollifier_nonneg n C hC s hs u
  have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => Real.enorm_eq_ofReal (hf0 y)), ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
      hpdf.2, ENNReal.ofReal_one]
  have hMoe :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume =
      ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    rw [lintegral_congr_ae
        (Filter.Eventually.of_forall fun y => by
          rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
  -- (ψ on the first coordinate, the `(T)`-lemma's Tonelli orientation)
  have hψmeas := measurable_mollifier n C hC s hs
  have hΦmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
    fun_prop
  have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
    le_trans (by norm_num : (0 : ENNReal) ≤ ENNReal.ofReal 0) (ENNReal.ofReal_le_ofReal hx)
  have hψe :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
    Measurable.ennreal_ofReal
      (by fun_prop :
        Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs p.1)
  have hwe :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖p.2‖)) :=
    Measurable.ennreal_ofReal
      (by fun_prop :
        Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖p.2‖)
  have hfa :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) :=
    hfm.enorm.comp
      (by fun_prop :
        Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))
  have hfb : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖f p.2‖ₑ) :=
    hfm.enorm.comp
      (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2)
  have hP1meas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)) :=
    hψe.mul (hwe.mul hfa)
  have hP2meas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) :=
    hψe.mul (hwe.mul hfb)
  have hΦnn :
    ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      0 ≤
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) :=
    fun p => mul_nonneg (hψpos p.1) (mul_nonneg (by linarith [norm_nonneg p.2]) (abs_nonneg _))
  -- the ∫⁻ pointwise split
  have hpt :
    ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal
          (mollifier n C hC s hs p.1 *
            ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) ≤
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) *
              ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) +
          ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
    intro p
    have hw0 : 0 ≤ (1 : ℝ) + ‖p.2‖ := by linarith [norm_nonneg p.2]
    have hab :
      |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2| ≤
        |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))| + |f p.2| :=
      abs_sub _ _
    have hstep :
      ENNReal.ofReal
          ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) ≤
        ENNReal.ofReal (1 + ‖p.2‖) *
          (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ) := by
      rw [ENNReal.ofReal_mul hw0]
      refine mul_le_mul_of_nonneg_left ?_ (hofnn _ hw0)
      refine le_trans (ENNReal.ofReal_le_ofReal hab) ?_
      rw [Real.enorm_eq_ofReal_abs (f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))),
        Real.enorm_eq_ofReal_abs (f p.2), ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    rw [ENNReal.ofReal_mul (hψpos p.1)]
    calc
      ENNReal.ofReal (mollifier n C hC s hs p.1) *
            ENNReal.ofReal
              ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) ≤
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) *
              (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ)) :=
        mul_le_mul_of_nonneg_left hstep (hofnn _ (hψpos p.1))
      _ =
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) +
            ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) :=
        by
        rw [mul_add]
        ring
  -- the weighted-marginal identity
  have hMoval :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume =
      1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hpt2 :
      ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
      intro y
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul, ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2), lintegral_add_left hfm.enorm _,
      hflint, hMoe]
  have hbnd : ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume < ⊤ := by
    rw [hMoval]
    exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
  -- the ψ-weighted shifted enorm marginal (piece 1)
  have hinner1 :
    ∀ a : EuclideanSpace ℝ (Fin n),
      ∫⁻ b : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖b‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ∂volume ≤
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
    intro a
    have hbmeas :
      Measurable
        (fun b : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖b‖) * ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
      (Measurable.ennreal_ofReal
            (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖b‖)).mul
        (hfm.enorm.comp
          (by fun_prop :
            Measurable fun b : EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))
    have hGmeas :
      Measurable (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) :=
      (Measurable.ennreal_ofReal
            (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖z‖)).mul
        hfm.enorm
    have hptw :
      ∀ b : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖b‖) * ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ≤
          ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖a‖) *
              (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) := by
      intro b
      have hba : WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) = b - a := rfl
      have htri : ‖b‖ ≤ ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ + ‖a‖ := by
        rw [hba]
        calc
          ‖b‖ = ‖(b - a) + a‖ := by rw [sub_add_cancel]
          _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le (b - a) a
      have hle :
        (1 : ℝ) + ‖b‖ ≤ (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) := by
        have hexp :
          (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) =
            1 + ‖a‖ + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ +
              ‖a‖ * ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ := by
          ring
        rw [hexp]
        linarith [htri, norm_nonneg a,
          mul_nonneg (norm_nonneg a)
            (norm_nonneg (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))]
      have henn : ∀ r : ℝ, 0 ≤ ‖r‖ₑ := fun r =>
        le_trans (hofnn _ (abs_nonneg r)) (le_of_eq (Real.enorm_eq_ofReal_abs r).symm)
      refine mul_le_mul_of_nonneg_left ?_ (hofnn _ (hψpos a))
      rw [←
        mul_assoc (ENNReal.ofReal (1 + ‖a‖))
          (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖))
          ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ,
        ← ENNReal.ofReal_mul (by linarith [norm_nonneg a] : 0 ≤ (1 : ℝ) + ‖a‖)]
      exact
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle)
          (henn (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
    have hbmeas2 :
      Measurable
        (fun b : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖a‖) *
            (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) :=
      (Measurable.ennreal_ofReal
            (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖a‖)).mul
        ((Measurable.ennreal_ofReal
              (by fun_prop :
                Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                  (1 : ℝ) + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)).mul
          (hfm.enorm.comp
            (by fun_prop :
              Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
    have hshiftbmeas :
      Measurable
        (fun b : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
            ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
      hGmeas.comp
        (by fun_prop :
          Measurable fun b : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))
    refine le_trans (MeasureTheory.lintegral_mono hptw) ?_
    rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas2,
      MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖a‖)) hshiftbmeas,
      lintegral_shift_neg n (a : Fin n → ℝ)
        (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) hGmeas,
      hMoval]
    have hring :
      ENNReal.ofReal (mollifier n C hC s hs a) *
          (ENNReal.ofReal (1 + ‖a‖) *
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))) =
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
      ring
    rw [hring]
  have hψea :
    Measurable (fun a : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (mollifier n C hC s hs a)) :=
    Measurable.ennreal_ofReal
      (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
  have hsplit :
    ∫⁻ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume =
      1 +
        ENNReal.ofReal
          (s *
            ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
    have hpt4 :
      ∀ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) =
          ENNReal.ofReal (mollifier n C hC s hs a) +
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
      intro a
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add, ENNReal.ofReal_one, mul_one]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4), lintegral_add_left hψea _,
      lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
  have hlint1 :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) ∂(volume.prod volume) <
      ⊤ := by
    rw [MeasureTheory.lintegral_prod (f :=
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ))
        hP1meas.aemeasurable]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner1) ?_
    have hpullmeas :
      Measurable
        (fun a : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
      (hψea).mul
        (Measurable.ennreal_ofReal
          (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖a‖))
    rw [MeasureTheory.lintegral_const_mul
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hpullmeas,
      hsplit]
    exact
      ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
        ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
  -- piece 2: the ψ-weighted unshifted enorm marginal
  have hbmeas0 :
    Measurable (fun b : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) :=
    (Measurable.ennreal_ofReal
          (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖b‖)).mul
      hfm.enorm
  have hinner2 :
    ∀ a : EuclideanSpace ℝ (Fin n),
      ∫⁻ b : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs a) * (ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) ∂volume ≤
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          ENNReal.ofReal (mollifier n C hC s hs a) := by
    intro a
    rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas0,
      hMoval]
    exact
      le_of_eq
        (mul_comm (ENNReal.ofReal (mollifier n C hC s hs a))
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
  have hlint2 :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) ∂(volume.prod volume) <
      ⊤ := by
    rw [MeasureTheory.lintegral_prod (f :=
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ))
        hP2meas.aemeasurable]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner2) ?_
    rw [MeasureTheory.lintegral_const_mul
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hψea,
      lintegral_mollifier n C hC s hs, mul_one]
    exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
  have hlint :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal
          (mollifier n C hC s hs p.1 *
            ((1 + ‖p.2‖) *
              |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) -
                  f p.2|)) ∂(volume.prod volume) <
      ⊤ := by
    refine
      lt_of_le_of_lt
        (le_trans (MeasureTheory.lintegral_mono hpt) (le_of_eq (lintegral_add_left hP1meas _))) ?_
    exact (ENNReal.add_lt_top).mpr ⟨hlint1, hlint2⟩
  refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn)]
  exact hlint

/-- **Step B of the smoothing theorem**: joint integrability of the ψ-weighted
difference integrand in the x-first orientation, by the measure-preserving swap. -/
public theorem integrable_joint_second (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.1‖) *
          (mollifier n C hC s hs p.2 *
            |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
      (volume.prod volume) := by
  have hψmeas := measurable_mollifier n C hC s hs
  have hswapmp :
    MeasureTheory.MeasurePreserving
      (Prod.swap :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hΦmeas := measurable_joint_first n f hfm C hC s hs
  have hΦint := integrable_joint_first n f hfm hpdf hfmom C hC s hs
  refine ((hswapmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint).congr' ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1 + ‖p.1‖) *
              (mollifier n C hC s hs p.2 *
                |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) -
                    f p.1|))).aestronglyMeasurable
  · filter_upwards with p
    show
      ‖mollifier n C hC s hs (p.swap).1 *
            ((1 + ‖(p.swap).2‖) *
              |f (WithLp.toLp 2 (((p.swap).2 : Fin n → ℝ) - ((p.swap).1 : Fin n → ℝ))) -
                  f (p.swap).2|)‖ =
        ‖(1 + ‖p.1‖) *
            (mollifier n C hC s hs p.2 *
              |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|)‖
    simp only [Prod.swap, Real.norm_eq_abs, abs_mul]
    ring

/-- **Weighted integrability of the smoothed prior**: the joint function
`(u, x) ↦ ψ_σ(u) · (1 + ‖x‖) · f (x − u)` is integrable on the product, via the
∫⁻ Tonelli bound: `w(x) ≤ (1 + ‖u‖) (1 + ‖x − u‖)`, the `x − u`-shift, and the
mollifier's first moment `∫⁻ ψ_σ(u) (1 + ‖u‖) = 1 + ofReal (σ · M_φ)`. -/
public theorem integrable_joint_smooth_prior (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
      (volume.prod volume) := by
  classical
  have hψmeas := measurable_mollifier n C hC s hs
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  have heqw :
    (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) = fun x : EuclideanSpace ℝ (Fin n) =>
      f x + ‖x‖ * f x := by
    funext x; ring
  have hwfint :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) volume := by
    rw [heqw]; exact hfi.add hfmom
  have hwnn : 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) :=
    Filter.Eventually.of_forall hwnonneg
  have hmass :
    ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume =
      1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume := by
    rw [heqw, MeasureTheory.integral_add hfi hfmom, hpdf.2]
  -- the ∫⁻ marginal identity of the weighted `f`
  have hMoval :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume =
      1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
      rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => Real.enorm_eq_ofReal (hf0 y)), ←
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
        hpdf.2, ENNReal.ofReal_one]
    have hMoe :
      ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume =
        ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
      rw [lintegral_congr_ae
          (Filter.Eventually.of_forall fun y => by
            rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
        ←
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
          (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
    have hpt2 :
      ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
      intro y
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul, ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2), lintegral_add_left hfm.enorm _,
      hflint, hMoe]
  -- the mollifier's first moment
  have hψmea :
    ∫⁻ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume =
      1 +
        ENNReal.ofReal
          (s *
            ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
    have hψea :
      Measurable (fun a : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (mollifier n C hC s hs a)) :=
      Measurable.ennreal_ofReal
        (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
    have hpt4 :
      ∀ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) =
          ENNReal.ofReal (mollifier n C hC s hs a) +
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
      intro a
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add, ENNReal.ofReal_one, mul_one]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4), lintegral_add_left hψea _,
      lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
  -- the ∫⁻ Tonelli bound for the ψ-first joint function
  have hΦmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))) := by
    fun_prop
  have hKnn :
    ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      0 ≤
        mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) :=
    fun p =>
    mul_nonneg (mollifier_nonneg n C hC s hs p.1)
      (mul_nonneg (by linarith [norm_nonneg p.2]) (hf0 _))
  refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hKnn)]
  have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
    le_trans (by norm_num : (0 : ENNReal) ≤ ENNReal.ofReal 0) (ENNReal.ofReal_le_ofReal hx)
  have hψe :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
    Measurable.ennreal_ofReal
      (by fun_prop :
        Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs p.1)
  have hinner :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal
            (mollifier n C hC s hs u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))) ∂volume ≤
        (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs u) * ENNReal.ofReal (1 + ‖u‖)) := by
    intro u
    have hu : 0 ≤ (1 : ℝ) + ‖u‖ := by linarith [norm_nonneg u]
    have hpsi : 0 ≤ mollifier n C hC s hs u := mollifier_nonneg n C hC s hs u
    have hxmeas :
      Measurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
            ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ) :=
      (Measurable.ennreal_ofReal
            (by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                (1 : ℝ) + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖)).mul
        (hfm.enorm.comp
          (by fun_prop :
            Measurable fun x : EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
    refine
      le_trans
        (MeasureTheory.lintegral_mono (f := fun (x : EuclideanSpace ℝ (Fin n)) =>
          ENNReal.ofReal
            (mollifier n C hC s hs u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))))
          (g := fun (x : EuclideanSpace ℝ (Fin n)) =>
          ENNReal.ofReal (mollifier n C hC s hs u) *
            (ENNReal.ofReal (1 + ‖u‖) *
              (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
                ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ)))
          (fun x => ?_))
        ?_
    · -- pointwise
      have hba : WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)) = x - u := rfl
      have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖ + ‖u‖ := by
        rw [hba]
        calc
          ‖x‖ = ‖(x - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le (x - u) u
      have hle :
        (1 : ℝ) + ‖x‖ ≤ (1 + ‖u‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) := by
        have hexp :
          (1 + ‖u‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) =
            1 + ‖u‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖ +
              ‖u‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖ := by
          ring
        rw [hexp]
        linarith [htri, norm_nonneg u,
          mul_nonneg (norm_nonneg u)
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))]
      have hfxnn : 0 ≤ f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) := hf0 _
      have hwnx : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
      have hkey :
        ENNReal.ofReal ((1 : ℝ) + ‖x‖) *
            ENNReal.ofReal (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ≤
          ENNReal.ofReal (1 + ‖u‖) *
            (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
              ENNReal.ofReal (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))) := by
        rw [←
          ENNReal.ofReal_mul
            (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))] :
              0 ≤ (1 : ℝ) + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖),
          ← ENNReal.ofReal_mul (by linarith [norm_nonneg u] : 0 ≤ (1 : ℝ) + ‖u‖), ←
          ENNReal.ofReal_mul hwnx]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hle hfxnn
      simp only []
      have hsplit :
        ENNReal.ofReal
            (mollifier n C hC s hs u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))) =
          ENNReal.ofReal (mollifier n C hC s hs u) *
            ENNReal.ofReal ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) :=
        ENNReal.ofReal_mul hpsi
      rw [hsplit, ENNReal.ofReal_mul (by linarith [norm_nonneg x] : 0 ≤ (1 : ℝ) + ‖x‖),
        Real.enorm_eq_ofReal hfxnn]
      exact mul_le_mul_of_nonneg_left hkey (hofnn _ hpsi)
    · -- the two const-pulls and the `x − u`-shift
      have hxfn :
        Measurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖u‖) *
              (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
                ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ)) :=
        (Measurable.ennreal_ofReal
              (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖u‖)).mul
          hxmeas
      rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs u)) hxfn,
        MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖u‖)) hxmeas,
        lintegral_shift_neg n (u : Fin n → ℝ)
          (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ)
          ((Measurable.ennreal_ofReal
                (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖z‖)).mul
            hfm.enorm),
        hMoval]
      have hring :
        ENNReal.ofReal (mollifier n C hC s hs u) *
            (ENNReal.ofReal (1 + ‖u‖) *
              (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))) =
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
            (ENNReal.ofReal (mollifier n C hC s hs u) * ENNReal.ofReal (1 + ‖u‖)) := by
        ring
      exact le_of_eq hring
  rw [MeasureTheory.lintegral_prod (f :=
      fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal
        (mollifier n C hC s hs p.1 *
          ((1 + ‖p.2‖) * f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))))
      ((Measurable.ennreal_ofReal hΦmeas).aemeasurable)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner) ?_
  have hpullmeas :
    Measurable
      (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
    (Measurable.ennreal_ofReal hψmeas).mul
      (Measurable.ennreal_ofReal
        (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖a‖))
  rw [MeasureTheory.lintegral_const_mul
      (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hpullmeas,
    hψmea]
  exact
    ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
      ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)

set_option maxHeartbeats 4000000 in
/-- **Smoothing theorem**: for a continuous pdf `f` with finite first moment, the weighted L¹
distance between `f` and its Gaussian smoothing tends to `0` along every positive sequence
`σ k → 0`. This produces the `hw`-hypothesis of `cme_uniform_balls_R` for the Gaussian-smoothed
priors `fhK K = gaussSmoothed … (1/(K+1))`. -/
public theorem weighted_smoothing_tendsto_seq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℕ → ℝ) (hσ : ∀ k, 0 < σ k)
    (hσ0 : Filter.Tendsto σ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |f x - gaussSmoothed n f C hC (σ k) (hσ k) x| ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  have hMnn : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume :=
    MeasureTheory.integral_nonneg fun y => mul_nonneg (norm_nonneg y) (hf0 y)
  -- the `weightedModulus` form of the `(T)`-lemma
  have hwmseq :
    ∀ (u : ℕ → EuclideanSpace ℝ (Fin n)),
      Filter.Tendsto u Filter.atTop (nhds 0) →
        Filter.Tendsto (fun k : ℕ => weightedModulus n f (u k)) Filter.atTop (nhds 0) :=
    fun u hu => weighted_modulus_tendsto_seq n f hf hpdf hfmom u hu
  have hwmAe := aemeasurable_weightedModulus n f hfm
  -- the Lebesgue-mass basics for `f`
  have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => Real.enorm_eq_ofReal (hf0 y)), ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
      hpdf.2, ENNReal.ofReal_one]
  have hMoe :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume =
      ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    rw [lintegral_congr_ae
        (Filter.Eventually.of_forall fun y => by
          rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
  -- the per-σ chain
  have hchain :
    ∀ (s : ℝ) (hs : 0 < s),
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume ≤
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((s : ℝ) • (v : Fin n → ℝ))) ∂volume := by
    intro s hs
    classical
    have hψmeas : Measurable (mollifier n C hC s hs) := by
      show
        Measurable
          (fun u : EuclideanSpace ℝ (Fin n) =>
            (s : ℝ)⁻¹ ^ n *
              multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((s : ℝ)⁻¹ • (u : Fin n → ℝ))))
      exact
        ((measurable_multivariateGaussianPDF n 0 C hC).comp
              (by fun_prop :
                Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                  WithLp.toLp 2 ((s : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul
          ((s : ℝ)⁻¹ ^ n)
    have hψint := mollifier_integrable n C hC s hs
    have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u := fun u =>
      mollifier_nonneg n C hC s hs u
    have hψ0le :
      ∀ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u ≤ mollifier n C hC s hs 0 :=
      mollifier_le_zero n C hC s hs
    have hgsi : MeasureTheory.Integrable (gaussSmoothed n f C hC s hs) volume :=
      integrable_of_isPdf (isPdf_gaussSmoothed n f hpdf hfm C hC s hs)
    -- measurability of the smoothing: the x-marginal integral of the joint function
    have hGxmeas :
      Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs p.2 *
            f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) := by
      fun_prop
    have hgsmeas : Measurable (gaussSmoothed n f C hC s hs) :=
      (hGxmeas.stronglyMeasurable.integral_prod_right').measurable
    -- the reflection is measure-preserving
    have hnegmp :
      MeasureTheory.MeasurePreserving (fun u : EuclideanSpace ℝ (Fin n) => -u) volume volume :=
      Measure.measurePreserving_neg _
    -- Step A: the pointwise smoothing identity, via `∫ ψ = 1` and `|∫ g| ≤ ∫ |g|`
    have hstepA :
      ∀ x : EuclideanSpace ℝ (Fin n),
        |f x - gaussSmoothed n f C hC s hs x| ≤
          ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume := by
      intro x
      have h2 :
        MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs u * f x)
          volume :=
        hψint.mul_const (f x)
      have hshifted :
        MeasureTheory.Integrable
          (fun z : EuclideanSpace ℝ (Fin n) =>
            f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ))))
          volume :=
        integrable_toLp_shift n (x : Fin n → ℝ) f hfi hfm
      have hcomp :
        MeasureTheory.Integrable
          (fun u : EuclideanSpace ℝ (Fin n) =>
            (fun z : EuclideanSpace ℝ (Fin n) =>
                f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ))))
              (-u))
          volume :=
        (hnegmp.integrable_comp hshifted.1).mpr hshifted
      have h3 :
        MeasureTheory.Integrable
          (fun u : EuclideanSpace ℝ (Fin n) =>
            mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
          volume := by
        have hcomp' :
          MeasureTheory.Integrable
            (fun u : EuclideanSpace ℝ (Fin n) =>
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
            volume := by
          refine hcomp.congr' ?_ ?_
          · exact
              ((by fun_prop :
                  Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                    f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
          · filter_upwards with u
            show
              ‖f
                    (WithLp.toLp 2
                      (((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) + (x : Fin n → ℝ)))‖ =
                ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
            congr 1
            simp only [WithLp.ofLp_neg]
            rw [add_comm, ← sub_eq_add_neg]
        refine MeasureTheory.Integrable.mono' (hcomp'.mul_const (mollifier n C hC s hs 0)) ?_ ?_
        · exact
            ((by fun_prop :
                Measurable fun u : EuclideanSpace ℝ (Fin n) =>
                  mollifier n C hC s hs u *
                    f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
        · filter_upwards with u
          show
            ‖mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ ≤
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) * mollifier n C hC s hs 0
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψpos u), abs_of_nonneg (hf0 _)]
          exact le_trans (mul_le_mul_of_nonneg_right (hψ0le u) (hf0 _)) (le_of_eq (mul_comm _ _))
      have h1 : f x = ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u * f x ∂volume := by
        rw [MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun u => mul_comm (mollifier n C hC s hs u) (f x)),
          MeasureTheory.integral_const_mul (f x), integral_mollifier n C hC s hs, mul_one]
      have hsub :
        f x - gaussSmoothed n f C hC s hs x =
          ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume := by
        conv_lhs => rw [h1]
        have hgs :
          gaussSmoothed n f C hC s hs x =
            ∫ u : EuclideanSpace ℝ (Fin n),
              mollifier n C hC s hs u *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume :=
          rfl
        rw [hgs, ← MeasureTheory.integral_sub h2 h3]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show
          mollifier n C hC s hs u * f x -
              mollifier n C hC s hs u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) =
            mollifier n C hC s hs u * (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
        rw [mul_sub]
      rw [hsub]
      refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
      rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun u => by
            rw [abs_mul, abs_of_nonneg (hψpos u),
              abs_sub_comm (f x) (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))])]
    -- Step B: the joint integrability of the ψ-weighted integrand, via the ∫⁻ Tonelli bound
    -- (ψ on the first coordinate, the `(T)`-lemma's Tonelli orientation)
    have hΦmeas :
      Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs p.1 *
            ((1 + ‖p.2‖) *
              |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
      fun_prop
    have hΦint :
      MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs p.1 *
            ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
        (volume.prod volume) := by
      classical
      have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
        le_trans (by norm_num : (0 : ENNReal) ≤ ENNReal.ofReal 0) (ENNReal.ofReal_le_ofReal hx)
      have hψe :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
        Measurable.ennreal_ofReal
          (by fun_prop :
            Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              mollifier n C hC s hs p.1)
      have hwe :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖p.2‖)) :=
        Measurable.ennreal_ofReal
          (by fun_prop :
            Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (1 : ℝ) + ‖p.2‖)
      have hfa :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) :=
        hfm.enorm.comp
          (by fun_prop :
            Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))
      have hfb :
        Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖f p.2‖ₑ) :=
        hfm.enorm.comp
          (by fun_prop :
            Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2)
      have hP1meas :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)) :=
        hψe.mul (hwe.mul hfa)
      have hP2meas :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) :=
        hψe.mul (hwe.mul hfb)
      have hΦnn :
        ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          0 ≤
            mollifier n C hC s hs p.1 *
              ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) :=
        fun p => mul_nonneg (hψpos p.1) (mul_nonneg (by linarith [norm_nonneg p.2]) (abs_nonneg _))
      -- the ∫⁻ pointwise split
      have hpt :
        ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal
              (mollifier n C hC s hs p.1 *
                ((1 + ‖p.2‖) *
                  |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) ≤
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
                (ENNReal.ofReal (1 + ‖p.2‖) *
                  ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) +
              ENNReal.ofReal (mollifier n C hC s hs p.1) *
                (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
        intro p
        have hw0 : 0 ≤ (1 : ℝ) + ‖p.2‖ := by linarith [norm_nonneg p.2]
        have hab :
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2| ≤
            |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))| + |f p.2| :=
          abs_sub _ _
        have hstep :
          ENNReal.ofReal
              ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) ≤
            ENNReal.ofReal (1 + ‖p.2‖) *
              (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ) := by
          rw [ENNReal.ofReal_mul hw0]
          refine mul_le_mul_of_nonneg_left ?_ (hofnn _ hw0)
          refine le_trans (ENNReal.ofReal_le_ofReal hab) ?_
          rw [Real.enorm_eq_ofReal_abs (f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))),
            Real.enorm_eq_ofReal_abs (f p.2), ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        rw [ENNReal.ofReal_mul (hψpos p.1)]
        calc
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
                ENNReal.ofReal
                  ((1 + ‖p.2‖) *
                    |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) ≤
              ENNReal.ofReal (mollifier n C hC s hs p.1) *
                (ENNReal.ofReal (1 + ‖p.2‖) *
                  (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ)) :=
            mul_le_mul_of_nonneg_left hstep (hofnn _ (hψpos p.1))
          _ =
              ENNReal.ofReal (mollifier n C hC s hs p.1) *
                  (ENNReal.ofReal (1 + ‖p.2‖) *
                    ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) +
                ENNReal.ofReal (mollifier n C hC s hs p.1) *
                  (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) :=
            by
            rw [mul_add]
            ring
      -- the weighted-marginal identity
      have hMoval :
        ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume =
          1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
        have hpt2 :
          ∀ y : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
          intro y
          rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul, ENNReal.ofReal_one,
            one_mul]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2), lintegral_add_left hfm.enorm _,
          hflint, hMoe]
      have hbnd :
        ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume < ⊤ := by
        rw [hMoval]
        exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
      -- the ψ-weighted shifted enorm marginal (piece 1)
      have hinner1 :
        ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖b‖) *
                  ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ∂volume ≤
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
              (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
        intro a
        have hbmeas :
          Measurable
            (fun b : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (1 + ‖b‖) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
          (Measurable.ennreal_ofReal
                (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖b‖)).mul
            (hfm.enorm.comp
              (by fun_prop :
                Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                  WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))
        have hGmeas :
          Measurable (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) :=
          (Measurable.ennreal_ofReal
                (by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖z‖)).mul
            hfm.enorm
        have hptw :
          ∀ b : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖b‖) *
                  ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ≤
              ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖a‖) *
                  (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
                    ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) := by
          intro b
          have hba : WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) = b - a := rfl
          have htri : ‖b‖ ≤ ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ + ‖a‖ := by
            rw [hba]
            calc
              ‖b‖ = ‖(b - a) + a‖ := by rw [sub_add_cancel]
              _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le (b - a) a
          have hle :
            (1 : ℝ) + ‖b‖ ≤
              (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) := by
            have hexp :
              (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) =
                1 + ‖a‖ + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ +
                  ‖a‖ * ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ := by
              ring
            rw [hexp]
            linarith [htri, norm_nonneg a,
              mul_nonneg (norm_nonneg a)
                (norm_nonneg (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))]
          have henn : ∀ r : ℝ, 0 ≤ ‖r‖ₑ := fun r =>
            le_trans (hofnn _ (abs_nonneg r)) (le_of_eq (Real.enorm_eq_ofReal_abs r).symm)
          refine mul_le_mul_of_nonneg_left ?_ (hofnn _ (hψpos a))
          rw [←
            mul_assoc (ENNReal.ofReal (1 + ‖a‖))
              (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖))
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ,
            ← ENNReal.ofReal_mul (by linarith [norm_nonneg a] : 0 ≤ (1 : ℝ) + ‖a‖)]
          exact
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle)
              (henn (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
        have hbmeas2 :
          Measurable
            (fun b : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (1 + ‖a‖) *
                (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
                  ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) :=
          (Measurable.ennreal_ofReal
                (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖a‖)).mul
            ((Measurable.ennreal_ofReal
                  (by fun_prop :
                    Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                      (1 : ℝ) + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)).mul
              (hfm.enorm.comp
                (by fun_prop :
                  Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                    WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
        have hshiftbmeas :
          Measurable
            (fun b : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
          hGmeas.comp
            (by fun_prop :
              Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))
        refine le_trans (MeasureTheory.lintegral_mono hptw) ?_
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas2,
          MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖a‖)) hshiftbmeas,
          lintegral_shift_neg n (a : Fin n → ℝ)
            (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) hGmeas,
          hMoval]
        have hring :
          ENNReal.ofReal (mollifier n C hC s hs a) *
              (ENNReal.ofReal (1 + ‖a‖) *
                (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))) =
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
              (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
          ring
        rw [hring]
      have hψea :
        Measurable (fun a : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (mollifier n C hC s hs a)) :=
        Measurable.ennreal_ofReal
          (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
      have hsplit :
        ∫⁻ a : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume =
          1 +
            ENNReal.ofReal
              (s *
                ∫ v : EuclideanSpace ℝ (Fin n),
                  ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
        have hpt4 :
          ∀ a : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) =
              ENNReal.ofReal (mollifier n C hC s hs a) +
                ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
          intro a
          rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add, ENNReal.ofReal_one,
            mul_one]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4), lintegral_add_left hψea _,
          lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
      have hlint1 :
        ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f
                    (WithLp.toLp 2
                      ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) ∂(volume.prod volume) <
          ⊤ := by
        rw [MeasureTheory.lintegral_prod (f :=
            fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ))
            hP1meas.aemeasurable]
        refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner1) ?_
        have hpullmeas :
          Measurable
            (fun a : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
          (hψea).mul
            (Measurable.ennreal_ofReal
              (by fun_prop : Measurable fun a : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖a‖))
        rw [MeasureTheory.lintegral_const_mul
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hpullmeas,
          hsplit]
        exact
          ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
            ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
      -- piece 2: the ψ-weighted unshifted enorm marginal
      have hbmeas0 :
        Measurable (fun b : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) :=
        (Measurable.ennreal_ofReal
              (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖b‖)).mul
          hfm.enorm
      have hinner2 :
        ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) ∂volume ≤
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
              ENNReal.ofReal (mollifier n C hC s hs a) := by
        intro a
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas0,
          hMoval]
        exact
          le_of_eq
            (mul_comm (ENNReal.ofReal (mollifier n C hC s hs a))
              (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
      have hlint2 :
        ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) ∂(volume.prod volume) <
          ⊤ := by
        rw [MeasureTheory.lintegral_prod (f :=
            fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) * (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ))
            hP2meas.aemeasurable]
        refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner2) ?_
        rw [MeasureTheory.lintegral_const_mul
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hψea,
          lintegral_mollifier n C hC s hs, mul_one]
        exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
      have hlint :
        ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal
              (mollifier n C hC s hs p.1 *
                ((1 + ‖p.2‖) *
                  |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) -
                      f p.2|)) ∂(volume.prod volume) <
          ⊤ := by
        refine
          lt_of_le_of_lt
            (le_trans (MeasureTheory.lintegral_mono hpt) (le_of_eq (lintegral_add_left hP1meas _)))
            ?_
        exact (ENNReal.add_lt_top).mpr ⟨hlint1, hlint2⟩
      refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn)]
      exact hlint
    -- Step B: the Fubini chain
    have hswapmp :
      MeasureTheory.MeasurePreserving
        (Prod.swap :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        (volume.prod volume) (volume.prod volume) :=
      MeasureTheory.Measure.measurePreserving_swap
    have hFxint :
      MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (1 + ‖p.1‖) *
            (mollifier n C hC s hs p.2 *
              |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
        (volume.prod volume) := by
      refine ((hswapmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint).congr' ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                (1 + ‖p.1‖) *
                  (mollifier n C hC s hs p.2 *
                    |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) -
                        f p.1|))).aestronglyMeasurable
      · filter_upwards with p
        show
          ‖mollifier n C hC s hs (p.swap).1 *
                ((1 + ‖(p.swap).2‖) *
                  |f (WithLp.toLp 2 (((p.swap).2 : Fin n → ℝ) - ((p.swap).1 : Fin n → ℝ))) -
                      f (p.swap).2|)‖ =
            ‖(1 + ‖p.1‖) *
                (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|)‖
        simp only [Prod.swap, Real.norm_eq_abs, abs_mul]
        ring
    have hRint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ∫ y : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              (mollifier n C hC s hs y *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume)
        volume :=
      hFxint.integral_prod_left
    have hA :
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ≤
          ∫ y : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              (mollifier n C hC s hs y *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume := by
      intro x
      refine le_trans (mul_le_mul_of_nonneg_left (hstepA x) (by linarith [norm_nonneg x])) ?_
      exact
        le_of_eq
          ((MeasureTheory.integral_const_mul (1 + ‖x‖)
              (fun u =>
                mollifier n C hC s hs u *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)).symm)
    have hLint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)
        volume := by
      refine MeasureTheory.Integrable.mono' hRint ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun x : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)).aestronglyMeasurable
      · filter_upwards with x
        show
          ‖(1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|‖ ≤
            ∫ y : EuclideanSpace ℝ (Fin n),
              (1 + ‖x‖) *
                (mollifier n C hC s hs y *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))]
        exact hA x
    have hB1 :
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume ≤
        ∫ u : EuclideanSpace ℝ (Fin n),
          ∫ x : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              ((1 + ‖x‖) *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume := by
      refine le_trans (MeasureTheory.integral_mono hLint hRint hA) ?_
      calc
        ∫ x : EuclideanSpace ℝ (Fin n),
              ∫ u : EuclideanSpace ℝ (Fin n),
                (1 + ‖x‖) *
                  (mollifier n C hC s hs u *
                    |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume ≤
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.1‖) *
                (mollifier n C hC s hs z.2 *
                  |f (WithLp.toLp 2 ((z.1 : Fin n → ℝ) - (z.2 : Fin n → ℝ))) -
                      f z.1|) ∂(volume.prod volume) :=
          by
          rw [←
            MeasureTheory.integral_prod (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (1 + ‖p.1‖) *
                (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume) hFxint]
        _ =
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.swap.1‖) *
                (mollifier n C hC s hs z.swap.2 *
                  |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) -
                      f z.swap.1|) ∂(volume.prod volume) :=
          by
          rw [←
            MeasureTheory.integral_prod_swap (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (1 + ‖p.1‖) *
                (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume)]
        _ =
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              mollifier n C hC s hs z.1 *
                ((1 + ‖z.2‖) *
                  |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) -
                      f z.2|) ∂(volume.prod volume) :=
          by
          have hswapcongr :
            ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.swap.1‖) *
                  (mollifier n C hC s hs z.swap.2 *
                    |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) - f z.swap.1|) =
                mollifier n C hC s hs z.1 *
                  ((1 + ‖z.2‖) *
                    |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) - f z.2|) := by
            intro z
            simp only [Prod.swap]
            ring
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hswapcongr)
        _ =
            ∫ u : EuclideanSpace ℝ (Fin n),
              ∫ x : EuclideanSpace ℝ (Fin n),
                mollifier n C hC s hs u *
                  ((1 + ‖x‖) *
                    |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) -
                        f x|) ∂volume ∂volume :=
          by
          rw [MeasureTheory.integral_prod (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              mollifier n C hC s hs p.1 *
                ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
              (μ := volume) (ν := volume) hΦint]
    refine
      le_trans
        (le_trans hB1
          (le_of_eq
            (MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall fun u => by
                simp only [weightedModulus]
                rw [MeasureTheory.integral_const_mul (mollifier n C hC s hs u)]))))
        (le_of_eq (integral_mollifier_mul n C hC s hs (weightedModulus n f) hwmAe))
  -- Step C: the dominated convergence on the shifted sequence `σ (· + k₀)`
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ0 1 one_pos)
  have hσ1 : ∀ k : ℕ, (σ (k + k₀) : ℝ) ≤ 1 := by
    intro k
    have h := hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h
    exact le_of_lt h
  have hσ' : Filter.Tendsto (fun k : ℕ => σ (k + k₀)) Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ0 δ hδ)
    exact
      Filter.eventually_atTop.mpr
        ⟨N, fun k hk => hN (k + k₀) (Nat.le_trans hk (Nat.le_add_right k k₀))⟩
  have hdct :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
      Filter.atTop (nhds 0) := by
    have hbdint :
      MeasureTheory.Integrable
        (fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v *
            ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
        volume := by
      have hφCint : MeasureTheory.Integrable (multivariateGaussianPDF n 0 C hC) volume :=
        integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC)
      have h1 :
        MeasureTheory.Integrable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2))
          volume :=
        hφCint.mul_const _
      have h2 :
        MeasureTheory.Integrable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
              (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))
          volume :=
        (integrable_norm_mul_gaussianPDF_center n C hC).mul_const _
      have heq :
        (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖))) =
          (fun v : EuclideanSpace ℝ (Fin n) =>
              multivariateGaussianPDF n 0 C hC v *
                ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2)) +
            (fun v : EuclideanSpace ℝ (Fin n) =>
              (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
                (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) := by
        funext v
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact h1.add h2
    have hwmSm : StronglyMeasurable (weightedModulus n f) := by
      have hKmeas :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := by
        fun_prop
      exact hKmeas.stronglyMeasurable.integral_prod_right'
    have hFmeas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
          volume :=
      fun k =>
      ((measurable_multivariateGaussianPDF n 0 C hC).stronglyMeasurable.mul
          (hwmSm.comp_measurable
            (by fun_prop :
              Measurable fun v : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))).aestronglyMeasurable
    have hbound :
      ∀ k : ℕ,
        ∀ᵐ (v : EuclideanSpace ℝ (Fin n)) ∂volume,
          ‖multivariateGaussianPDF n 0 C hC v *
                weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))‖ ≤
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)) :=
      fun k =>
      Filter.Eventually.of_forall
        (fun v => by
          have hwmnn :
            0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) :=
            show
              0 ≤
                ∫ x : EuclideanSpace ℝ (Fin n),
                  (1 + ‖x‖) *
                    |f
                          (WithLp.toLp 2
                            ((x : Fin n → ℝ) -
                              (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)) : Fin n → ℝ))) -
                        f x| ∂volume
              from
              MeasureTheory.integral_nonneg fun x =>
                mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (multivariateGaussianPDF_pos n 0 C hC v),
            abs_of_nonneg hwmnn]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
          refine
            le_trans
              (weightedModulus_le n f hfm hpdf hfmom
                (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
              ?_
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [hMnn])
          have hnorm :
            ‖WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))‖ = (σ (k + k₀) : ℝ) * ‖v‖ := by
            rw [show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) = (σ (k + k₀) : ℝ) • v
                from rfl,
              norm_smul]
            congr 1
            rw [Real.norm_eq_abs, abs_of_pos (hσ _)]
          rw [hnorm]
          linarith [mul_le_mul_of_nonneg_right (hσ1 k) (norm_nonneg v)])
    have hlim :
      ∀ᵐ v : EuclideanSpace ℝ (Fin n),
        Filter.Tendsto
          (fun k : ℕ =>
            multivariateGaussianPDF n 0 C hC v *
              weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
          Filter.atTop (nhds 0) := by
      filter_upwards with v
      have hv0 :
        Filter.Tendsto (fun k : ℕ => WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))
          Filter.atTop (nhds 0) := by
        refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
        rcases eq_or_ne v 0 with hv | hv
        · refine Filter.Eventually.of_forall fun k => ?_
          rw [hv, show ((0 : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = 0 from rfl, smul_zero,
            show (WithLp.toLp 2 (0 : Fin n → ℝ)) = (0 : EuclideanSpace ℝ (Fin n)) from rfl,
            dist_self]
          exact hδ
        · obtain ⟨N, hN⟩ :=
            Filter.eventually_atTop.mp
              (Metric.tendsto_nhds.mp hσ' (δ / ‖v‖) (div_pos hδ (norm_pos_iff.2 hv)))
          refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have h1 := hN k hk
          rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h1
          rw [dist_zero_right,
            show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) = (σ (k + k₀) : ℝ) • v from
              rfl,
            norm_smul, Real.norm_eq_abs, abs_of_pos (hσ _)]
          calc
            (σ (k + k₀) : ℝ) * ‖v‖ < (δ / ‖v‖) * ‖v‖ :=
              mul_lt_mul_of_pos_right h1 (norm_pos_iff.2 hv)
            _ = δ := by rw [div_mul_cancel₀ _ (ne_of_gt (norm_pos_iff.2 hv))]
      have hwm0 := hwmseq _ hv0
      have := (tendsto_const_nhds (x := multivariateGaussianPDF n 0 C hC v)).mul hwm0
      simpa using this
    have hdct' :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v *
            ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
        (f := fun _ => (0 : ℝ)) hFmeas hbdint hbound hlim
    rw [integral_zero] at hdct'
    exact hdct'
  have hmain :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ))))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat k₀).mp hdct
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hmain ε hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  have hNk := hN k hk
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (MeasureTheory.integral_nonneg
        (fun v : EuclideanSpace ℝ (Fin n) =>
          mul_nonneg (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
            (show 0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ))) from
              MeasureTheory.integral_nonneg fun x =>
                mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))))] at hNk
  have h0 :
    0 ≤
      ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC (σ k) (hσ k) x| ∂volume :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h0]
  exact lt_of_le_of_lt (hchain (σ k) (hσ k)) hNk

/-! ### The smoothed-prior sequence satisfies the `hw` hypothesis -/

/-- Measurability of the Gaussian-smoothed prior: the `x`-marginal integral of the
joint `(x, u) ↦ ψ_σ(u) · f (x − u)`. -/
public theorem measurable_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    Measurable (gaussSmoothed n f C hC σ hσ) := by
  have hψmeas : Measurable (mollifier n C hC σ hσ) := measurable_mollifier n C hC σ hσ
  have hGxmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ p.2 * f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) := by
    fun_prop
  exact (hGxmeas.stronglyMeasurable.integral_prod_right').measurable

/-- The smoothed-prior sequence: `K ↦ gaussSmoothed … (1/(K+1))`, with `1/(K+1) → 0`. -/
public noncomputable def smoothedPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun K =>
  gaussSmoothed n f C hC ((1 : ℝ) / ((K : ℝ) + 1)) (by positivity)

/-- **Weighted integrability of the smoothed-prior gap**: `(1 + ‖x‖) · |f x − gaussSmoothed x|`
is integrable, by domination with `(1 + ‖x‖) · f x + ∫ ψ_σ(u) · (1 + ‖x‖) · f (x − u) du`
(the second piece is the `x`-marginal of the ψ-first joint function). -/
public theorem integrable_weighted_abs_diff_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)
      volume := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψmeas : Measurable (mollifier n C hC s hs) := measurable_mollifier n C hC s hs
  have hgsmm : Measurable (gaussSmoothed n f C hC s hs) :=
    measurable_gaussSmoothed n f hfm C hC s hs
  have hx : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 : ℝ) + ‖x‖ := fun x => by
    linarith [norm_nonneg x]
  have hgsmpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gaussSmoothed n f C hC s hs x := fun x =>
    MeasureTheory.integral_nonneg fun u => mul_nonneg (mollifier_nonneg n C hC s hs u) (hf0 _)
  -- piece 1: `(1 + ‖x‖) · f x`
  have hg1 :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) volume := by
    have heq :
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) = fun x : EuclideanSpace ℝ (Fin n) =>
        f x + ‖x‖ * f x := by
      funext x; ring
    rw [heq]; exact hfi.add hfmom
  -- piece 2: `(1 + ‖x‖) · gaussSmoothed x`, via the ψ-first joint's `x`-marginal
  have hg2 :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * gaussSmoothed n f C hC s hs x) volume := by
    refine
      MeasureTheory.Integrable.mono'
        ((integrable_joint_smooth_prior n f hfm hpdf hfmom C hC s hs).integral_prod_right) ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) * gaussSmoothed n f C hC s hs x)).aestronglyMeasurable
    · filter_upwards with x
      show
        ‖(1 + ‖x‖) * gaussSmoothed n f C hC s hs x‖ ≤
          ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume
      have hsplit :
        ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume =
          ∫ u : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              (mollifier n C hC s hs u *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hx x), abs_of_nonneg (hgsmpos x), hsplit,
        MeasureTheory.integral_const_mul (1 + ‖x‖)]
      exact mul_le_mul_of_nonneg_left (le_refl _) (hx x)
  -- the domination
  refine MeasureTheory.Integrable.mono' (hg1.add hg2) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)).aestronglyMeasurable
  · filter_upwards with x
    show
      ‖(1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|‖ ≤
        (1 + ‖x‖) * f x + (1 + ‖x‖) * gaussSmoothed n f C hC s hs x
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hx x)]
    calc
      (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ≤
          (1 + ‖x‖) * (|f x| + |gaussSmoothed n f C hC s hs x|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (hx x)
      _ = (1 + ‖x‖) * (f x + gaussSmoothed n f C hC s hs x) := by
        rw [abs_of_nonneg (hf0 x), abs_of_nonneg (hgsmpos x)]
      _ = (1 + ‖x‖) * f x + (1 + ‖x‖) * gaussSmoothed n f C hC s hs x := by rw [mul_add]

/-- **The `hw` hypothesis for the smoothed-prior sequence**: the ∫⁻ form of the weighted-L¹
convergence `∫ (1 + ‖x‖) |f x − gaussSmoothed … (1/(K+1)) x| → 0` along `K → ∞`. -/
public theorem hw_smoothedPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    ∀ ε > 0,
      ∃ K₀ : ℕ,
        ∀ K ≥ K₀,
          ∫⁻ h : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal ((1 + ‖h‖) * |f h - smoothedPriorSeq n f C hC K h|) ∂volume <
            ENNReal.ofReal ε := by
  intro ε hε
  classical
  have hσpos : ∀ K : ℕ, 0 < (1 : ℝ) / ((K : ℝ) + 1) := fun K => div_pos one_pos (by positivity)
  have hσ0 : Filter.Tendsto (fun K : ℕ => (1 : ℝ) / ((K : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv :=
    weighted_smoothing_tendsto_seq n f hf hpdf hfmom C hC (fun K => (1 : ℝ) / ((K : ℝ) + 1)) hσpos
      hσ0
  -- per-K integrability and the ∫⁻ ↔ ∫ bridge
  have hKint :
    ∀ K : ℕ,
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x|)
        volume :=
    fun K =>
    integrable_weighted_abs_diff_gaussSmoothed n f hf.measurable hpdf hfmom C hC
      ((1 : ℝ) / ((K : ℝ) + 1)) (hσpos K)
  have hwnn :
    ∀ K : ℕ,
      0 ≤ᵐ[volume]
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x|) :=
    fun K =>
    Filter.Eventually.of_forall fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  have hbridge :
    ∀ K : ℕ,
      ENNReal.ofReal
          (∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| ∂volume) =
        ∫⁻ h : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal ((1 + ‖h‖) * |f h - smoothedPriorSeq n f C hC K h|) ∂volume :=
    fun K => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hKint K) (hwnn K)
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hconv ε hε)
  refine ⟨K₀, fun K hK => ?_⟩
  have hK₀K := hK₀ K hK
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))] at hK₀K
  rw [← hbridge K]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hK₀K

/-- **Phase 1**: the conditional mean estimates computed from the Gaussian-smoothed priors
`smoothedPriorSeq … K` converge to the CME of the true prior `f` locally uniformly —
uniformly on every closed ball of radius `r > 0` in `ℝ^m`, for arbitrary dimensions `m, n`
and observation matrix `A`. This is `cme_uniform_balls_R` with the smoothed-prior sequence,
whose `hw` hypothesis is `hw_smoothedPriorSeq`. -/
public theorem cme_uniform_balls_smoothed_prior (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun K : ℕ =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A f y - cmeR m n S hS A (smoothedPriorSeq n f C hC K) y‖)
      atTop (nhds 0) := by
  have hσpos : ∀ K : ℕ, 0 < (1 : ℝ) / ((K : ℝ) + 1) := fun K => div_pos one_pos (by positivity)
  exact
    cme_uniform_balls_R m n S hS A f hpdf hfmom (smoothedPriorSeq n f C hC)
      (fun K => isPdf_gaussSmoothed n f hpdf hf.measurable C hC ((1 : ℝ) / ((K : ℝ) + 1)) (hσpos K))
      (hw_smoothedPriorSeq n f hf hpdf hfmom C hC) r hr

/-! ## Phase 2, Step 0: weighted translation continuity for integrable `f` (no continuity)

The (T)-lemma of Phase 1 requires `f` continuous (pointwise convergence for the DCT core).
For the general (integrable-only) case the core is instead Mathlib's L¹ translation
continuity, formalized through the continuous `DomAddAct` action on `Lp ℝ 1 volume`: the
coerced function of `DomAddAct.mk u +ᵥ MemLp.toLp f hmem` is a.e. `fun x => f (u +ᵥ x)`,
and the `L¹`-distance of the action translates computes to the translation modulus
(`L1.dist_def`). -/

/-- Bridge between the `DomAddAct` translation form and the `WithLp`-idiom pointwise form
(the two coordinate-wise additions commute). -/
theorem vadd_toLp_add {n : ℕ} (x u : EuclideanSpace ℝ (Fin n)) :
    (u +ᵥ x : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)) := by
  apply WithLp.ofLp_injective
  show
    (u + x : EuclideanSpace ℝ (Fin n)).ofLp =
      (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))).ofLp
  rw [WithLp.ofLp_add, WithLp.ofLp_toLp]
  exact add_comm _ _

set_option maxHeartbeats 800000 in
/-- **Unweighted translation modulus** of an integrable `f` tends to `0` (no continuity of
`f` needed): `∫ |f x − f (x + u)| dx → 0` as `u → 0`. -/
public theorem modulus_tendsto_integrable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfi : MeasureTheory.Integrable f volume) :
    Filter.Tendsto
      (fun u : EuclideanSpace ℝ (Fin n) =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume)
      (nhds 0) (nhds 0) := by
  classical
  have hmem : MemLp f (1 : ℝ≥0∞) volume := memLp_one_iff_integrable.mpr hfi
  have hFact : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have hcv :
    ContinuousVAdd (EuclideanSpace ℝ (Fin n))ᵈᵃᵃ
      (Lp ℝ (1 : ℝ≥0∞) (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
    inferInstance
  have hslice :
    Continuous (fun u : EuclideanSpace ℝ (Fin n) => DomAddAct.mk u +ᵥ MemLp.toLp f hmem) :=
    hcv.continuous_vadd.comp ((DomAddAct.mkHomeomorph.continuous).prodMk continuous_const)
  have hzero :
    DomAddAct.mk (0 : EuclideanSpace ℝ (Fin n)) +ᵥ MemLp.toLp f hmem = MemLp.toLp f hmem := by simp
  -- the `L¹`-distance of the action translate tends to `0`
  have hdistlim :
    Filter.Tendsto
      (fun u : EuclideanSpace ℝ (Fin n) =>
        dist (DomAddAct.mk u +ᵥ MemLp.toLp f hmem) (MemLp.toLp f hmem))
      (nhds 0) (nhds 0) := by
    have h := (hslice.continuousAt (x := 0)).tendsto
    rw [hzero] at h
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    exact
      (Metric.tendsto_nhds.mp h ε hε).mono fun u hu => by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
        exact hu
  -- the per-`u` value of the distance, as the unweighted translation modulus
  have hval :
    ∀ u : EuclideanSpace ℝ (Fin n),
      dist (DomAddAct.mk u +ᵥ MemLp.toLp f hmem) (MemLp.toLp f hmem) =
        ∫ x : EuclideanSpace ℝ (Fin n), |f x - f (u +ᵥ x)| ∂volume := by
    intro u
    -- the shifted function's integrability, via the `Lp` action
    have hmp := MeasureTheory.measurePreserving_vadd u (volume : Measure (EuclideanSpace ℝ (Fin n)))
    have hSR := hmem.comp_measurePreserving hmp
    have hshift :
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => f (u +ᵥ x)) volume :=
      memLp_one_iff_integrable.mp hSR
    have hdiff :
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => f (u +ᵥ x) - f x) volume :=
      hshift.sub hfi
    have hdiffabs :
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => |f (u +ᵥ x) - f x|) volume :=
      hdiff.abs
    -- the pointwise a.e. identification of the coerced shifted function
    have hshiftae : ∀ᵐ x ∂volume, ⇑(MemLp.toLp f hmem) (u +ᵥ x) = f (u +ᵥ x) := by
      filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hmem)] with x h
      simpa using h
    have hintg :
      ∀ᵐ x ∂volume,
        edist (⇑(DomAddAct.mk u +ᵥ MemLp.toLp f hmem) x) (⇑(MemLp.toLp f hmem) x) =
          ENNReal.ofReal |f (u +ᵥ x) - f x| := by
      filter_upwards [(DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk u) (MemLp.toLp f hmem)), hshiftae,
        MemLp.coeFn_toLp hmem] with x h0 h1 h2
      rw [edist_dist, dist_eq_norm, Real.norm_eq_abs, h0]
      simp only [show DomAddAct.mk.symm (DomAddAct.mk u) = u from rfl]
      rw [h1, h2]
    rw [MeasureTheory.L1.dist_def, lintegral_congr_ae hintg, ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hdiffabs
        (Filter.Eventually.of_forall fun x => abs_nonneg _),
      ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg (fun x => abs_nonneg _))]
    exact
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun x => by
          simp only []
          rw [abs_sub_comm])
  -- assemble: the modulus tends to `0` (the `hb` bridge back to the statement form)
  have hb :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ∫ x : EuclideanSpace ℝ (Fin n), |f x - f (u +ᵥ x)| ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume :=
    fun u =>
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => by
        simp only []
        rw [vadd_toLp_add x u])
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  exact
    (Metric.tendsto_nhds.mp hdistlim ε hε).mono fun u hu => by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, hval u, hb u] at hu
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun x => abs_nonneg _))]
      exact hu

set_option maxHeartbeats 2000000 in
/-- **Weighted translation modulus** of an integrable nonnegative `f` with finite first
moment tends to `0` (no continuity of `f` needed):
`∫ (1 + ‖x‖) · |f x − f (x + u)| dx → 0` as `u → 0`. This is Phase 2 Step 0: the
weighted L¹ translation continuity, with the core supplied by
`modulus_tendsto_integrable` (Mathlib's L¹ translation continuity via the `DomAddAct`
action) and the tails by the moment-tail exhaustion with the threshold-shift transport
(the `(T)`-lemma's architecture). -/
public theorem weighted_modulus_tendsto_integrable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : 0 ≤ f) (hfi : MeasureTheory.Integrable f volume)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume) :
    Filter.Tendsto
      (fun u : EuclideanSpace ℝ (Fin n) =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume)
      (nhds 0) (nhds 0) := by
  classical
  have hwnonneg : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖y‖) * f y := fun y =>
    mul_nonneg (by linarith [norm_nonneg y]) (hf0 y)
  have hwfint :
    MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) volume := by
    have heq :
      (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) = fun y : EuclideanSpace ℝ (Fin n) =>
        f y + ‖y‖ * f y := by
      funext y; ring
    rw [heq]; exact hfi.add hfmom
  have htail :=
    setIntegral_tail_tendsto n (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) hwfint hwnonneg
  -- the ε-budget
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨K₁, hK₁⟩ :=
    Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp htail (ε / 8) (by linarith))
  set K := K₁ + 1 with hKdef
  -- core smallness and the `‖u‖ < 1` smallness, both eventually in `𝓝 0`
  have hcore' :
    Filter.Eventually
      (fun u : EuclideanSpace ℝ (Fin n) =>
        dist
            (∫ x : EuclideanSpace ℝ (Fin n),
              |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume)
            0 <
          ε / (2 * (1 + (K : ℝ))))
      (nhds 0) :=
    Metric.tendsto_nhds.mp (modulus_tendsto_integrable f hfi) _ (by positivity)
  have hsmall : Filter.Eventually (fun u : EuclideanSpace ℝ (Fin n) => dist u 0 < 1) (nhds 0) :=
    Metric.tendsto_nhds.mp (Filter.tendsto_id) 1 one_pos
  refine (hcore'.and hsmall).mono fun u hu => ?_
  obtain ⟨hcoreu, husmall⟩ := hu
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (MeasureTheory.integral_nonneg (fun x => abs_nonneg _))] at hcoreu
  rw [dist_eq_norm, sub_zero] at husmall
  -- the tail values at `K` and `K − 1`
  have hK₁K :
    ∀ k ≥ K₁,
      ∫ x in {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume < ε / 8 :=
    fun k hk => by
    have h := hK₁ k hk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (MeasureTheory.integral_nonneg fun y => hwnonneg y)] at h
    exact h
  have htK := hK₁K K (by omega)
  have htK1 := hK₁K (K - 1) (by omega)
  -- the split sets and their measurability
  set A : Set (EuclideanSpace ℝ (Fin n)) := {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} with
    hAdef
  set B : Set (EuclideanSpace ℝ (Fin n)) := {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖} with
    hBdef
  have hBmeas : MeasurableSet B := measurableSet_norm_gt n K
  have hB2meas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖} :=
    measurableSet_norm_gt n K₁
  have hAm : MeasurableSet A := by
    have hAeq : A = Bᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hBdef, hAdef, not_lt]
    rw [hAeq]
    exact hBmeas.compl
  -- the per-`u` pieces (all in the statement's `toLp`-form, via the `coeFn` chains)
  have hmem : MemLp f (1 : ℝ≥0∞) volume := memLp_one_iff_integrable.mpr hfi
  have hmp := MeasureTheory.measurePreserving_vadd u (volume : Measure (EuclideanSpace ℝ (Fin n)))
  have hSR := hmem.comp_measurePreserving hmp
  have hshift :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))
      volume := by
    have e2 :
      (fun x : EuclideanSpace ℝ (Fin n) => f (u +ᵥ x)) =ᵐ[volume]
        (fun x : EuclideanSpace ℝ (Fin n) =>
          f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))) :=
      Filter.Eventually.of_forall fun x => by
        simp only []
        rw [vadd_toLp_add x u]
    exact (memLp_one_iff_integrable.mp hSR).congr e2
  have hd :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))|)
      volume := by
    refine (hshift.sub hfi).abs.congr ?_
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply, abs_sub_comm]
  have hwabs :
    AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))|)
      volume :=
    ((by fun_prop :
          Measurable fun x : EuclideanSpace ℝ (Fin n) => (1 : ℝ) + ‖x‖)).aestronglyMeasurable.mul
      hd.aestronglyMeasurable
  have hwfLp : MemLp (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) (1 : ℝ≥0∞) volume :=
    memLp_one_iff_integrable.mpr hwfint
  have hWfcomp := hwfLp.comp_measurePreserving hmp
  have hWf'shift :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))
      volume := by
    have e2 :
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖u +ᵥ x‖) * f (u +ᵥ x)) =ᵐ[volume]
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))) :=
      Filter.Eventually.of_forall fun x => by
        simp only []
        rw [vadd_toLp_add x u]
    exact (memLp_one_iff_integrable.mp hWfcomp).congr e2
  -- the weighted integrand's integrability (dominated by the weighted tails of `f`)
  have hWint :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))|)
      volume := by
    refine
      MeasureTheory.Integrable.mono' (hwfint.add (hWf'shift.const_mul ((1 : ℝ) + ‖u‖))) hwabs ?_
    filter_upwards with x
    have hxnn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
    have hufnn : 0 ≤ (1 : ℝ) + ‖u‖ := by linarith [norm_nonneg u]
    have hxeq : (x : EuclideanSpace ℝ (Fin n)) = (u +ᵥ x) - u := by
      apply WithLp.ofLp_injective
      show x.ofLp = ((u +ᵥ x) - u).ofLp
      rw [WithLp.ofLp_sub, show (u +ᵥ x).ofLp = u.ofLp + x.ofLp from rfl, add_comm u.ofLp x.ofLp,
        add_sub_cancel_right]
    have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ + ‖u‖ := by
      rw [← vadd_toLp_add x u]
      calc
        ‖x‖ = ‖(u +ᵥ x) - u‖ := by rw [← hxeq]
        _ ≤ ‖u +ᵥ x‖ + ‖u‖ := norm_sub_le _ _
    have habsle :
      |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ≤
        f x + f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))) := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_nonneg (hf0 x), abs_of_nonneg (hf0 _)]
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxnn (abs_nonneg _))]
    calc
      (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ≤
          (1 + ‖x‖) * (f x + f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))) :=
        mul_le_mul_of_nonneg_left habsle hxnn
      _ = (1 + ‖x‖) * f x + (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))) := by
        rw [mul_add]
      _ ≤
          (1 + ‖x‖) * f x +
            ((1 : ℝ) + ‖u‖) *
              ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))) :=
        by
        refine add_le_add (le_refl _) ?_
        rw [← mul_assoc]
        refine
          mul_le_mul_of_nonneg_right ?_ (hf0 (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))
        have hexp :
          ((1 : ℝ) + ‖u‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) =
            1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ + ‖u‖ +
              ‖u‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ := by
          ring
        rw [hexp]
        linarith [htri, norm_nonneg u,
          mul_nonneg (norm_nonneg u)
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))]
  -- the split sets and the pointwise decomposition
  set A : Set (EuclideanSpace ℝ (Fin n)) := {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} with
    hAdef
  set B : Set (EuclideanSpace ℝ (Fin n)) := {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖} with
    hBdef
  have hBmeas : MeasurableSet B := measurableSet_norm_gt n K
  have hB2meas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖} :=
    measurableSet_norm_gt n K₁
  have hAm : MeasurableSet A := by
    have hAeq : A = Bᶜ := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hBdef, hAdef, not_lt]
    rw [hAeq]
    exact hBmeas.compl
  have hB3meas : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖} :=
    measurableSet_norm_gt n ((K - 1 : ℕ) : ℝ)
  have hinteq :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| =
        {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
            x +
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
            x := by
    intro x
    rcases le_or_gt ‖x‖ (K : ℝ) with hm | hm
    · rw [Set.indicator_of_mem (show x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} from hm),
        Set.indicator_of_notMem
          (fun hc : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖} =>
            not_lt.mpr hm (show (K : ℝ) < ‖x‖ from hc)),
        add_zero]
    · rw [Set.indicator_of_notMem
          (fun hc : x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} =>
            not_le.mpr hm (show ‖x‖ ≤ (K : ℝ) from hc)),
        Set.indicator_of_mem (show x ∈ {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖} from hm),
        zero_add]
  -- the core part: inside the ball, dominated by the unweighted core
  have hcoreB :
    ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
          x ∂volume ≤
      ((1 : ℝ) + K) *
        ∫ x : EuclideanSpace ℝ (Fin n),
          |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume := by
    refine
      le_trans (MeasureTheory.integral_mono (hWint.indicator hAm) (hd.const_mul ((1 : ℝ) + K)) ?_)
        ?_
    · exact fun x => by
        rcases le_or_gt ‖x‖ (K : ℝ) with hm | hm
        · rw [Set.indicator_of_mem
              (show x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} from hm)]
          exact mul_le_mul_of_nonneg_right (by linarith [hm]) (abs_nonneg _)
        · rw [Set.indicator_of_notMem
              (fun hc : x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)} =>
                not_le.mpr hm (show ‖x‖ ≤ (K : ℝ) from hc))]
          exact mul_nonneg (by positivity) (abs_nonneg _)
    · rw [MeasureTheory.integral_const_mul ((1 : ℝ) + K)]
  -- the tail piece 1: exactly the tail value at `K`
  have hI1' :
    ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x ∂volume =
      ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
    MeasureTheory.integral_indicator hBmeas
  -- the tail piece 2's integrability and the shifted-tail transport
  have hWf'2int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
          x)
      volume := by
    refine
      MeasureTheory.Integrable.mono' ((hWf'shift.indicator hBmeas).const_mul ((1 : ℝ) + ‖u‖)) ?_ ?_
    · exact
        (((by fun_prop :
                  Measurable fun y : EuclideanSpace ℝ (Fin n) =>
                    (1 : ℝ) + ‖y‖)).aestronglyMeasurable.mul
              hshift.aestronglyMeasurable).indicator
          hBmeas
    · filter_upwards with x
      rcases em (x ∈ B) with hm | hm
      · have hxnn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
        have hf'nn :
          0 ≤
            (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))) :=
          mul_nonneg (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))])
            (hf0 _)
        have hexp :
          ((1 : ℝ) + ‖u‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖) =
            1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ + ‖u‖ +
              ‖u‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ := by
          ring
        have hxeq2 : (x : EuclideanSpace ℝ (Fin n)) = (u +ᵥ x) - u := by
          apply WithLp.ofLp_injective
          show x.ofLp = ((u +ᵥ x) - u).ofLp
          rw [WithLp.ofLp_sub, show (u +ᵥ x).ofLp = u.ofLp + x.ofLp from rfl,
            add_comm u.ofLp x.ofLp, add_sub_cancel_right]
        have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))‖ + ‖u‖ := by
          rw [← vadd_toLp_add x u]
          calc
            ‖x‖ = ‖(u +ᵥ x) - u‖ := congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) hxeq2
            _ ≤ ‖u +ᵥ x‖ + ‖u‖ := norm_sub_le _ _
        rw [Set.indicator_of_mem hm, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxnn (hf0 _)),
          Set.indicator_of_mem hm]
        rw [← mul_assoc]
        refine
          mul_le_mul_of_nonneg_right ?_ (hf0 (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))
        rw [hexp]
        linarith [htri, norm_nonneg u,
          mul_nonneg (norm_nonneg u)
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))))]
      · rw [Set.indicator_of_notMem hm, norm_zero, Set.indicator_of_notMem hm, mul_zero]
  have hgmeas :
    AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) |
                (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}.indicator
            (fun _ => (1 : ℝ)) z *
          ((1 + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f z))
      volume := by
    have hSm :
      MeasurableSet
        {y : EuclideanSpace ℝ (Fin n) |
          (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖} :=
      (measurableSet_norm_gt n K).preimage
        (by fun_prop :
          Measurable fun y : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ)))
    exact
      (((by fun_prop :
                  Measurable fun _ : EuclideanSpace ℝ (Fin n) =>
                    (1 : ℝ)).aestronglyMeasurable).indicator
            hSm).mul
        (((by fun_prop :
              Measurable fun z : EuclideanSpace ℝ (Fin n) =>
                (1 : ℝ) +
                  ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖)).aestronglyMeasurable.mul
          hfi.aestronglyMeasurable)
  have hgint :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) |
                (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}.indicator
            (fun _ => (1 : ℝ)) z *
          ((1 + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f z))
      volume := by
    refine MeasureTheory.Integrable.mono' (hwfint.mul_const ((1 : ℝ) + ‖u‖)) hgmeas ?_
    filter_upwards with z
    have hznn : 0 ≤ (1 : ℝ) + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖ := by
      linarith [norm_nonneg (WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ)))]
    have hznn2 : 0 ≤ (1 : ℝ) + ‖z‖ := by linarith [norm_nonneg z]
    rcases
      em
        (z ∈
          {y : EuclideanSpace ℝ (Fin n) |
            (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}) with
      hm | hm
    · rw [Set.indicator_of_mem hm, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hznn (hf0 z))]
      have hexp : ((1 : ℝ) + ‖z‖) * ((1 : ℝ) + ‖u‖) = 1 + ‖z‖ + ‖u‖ + ‖z‖ * ‖u‖ := by ring
      have hsub : ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖ ≤ ‖z‖ + ‖u‖ := norm_sub_le _ _
      calc
        (1 + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f z ≤
            ((1 : ℝ) + ‖z‖) * ((1 : ℝ) + ‖u‖) * f z :=
          by
          refine mul_le_mul_of_nonneg_right ?_ (hf0 z)
          rw [hexp]
          linarith [hsub, norm_nonneg z, norm_nonneg u, mul_nonneg (norm_nonneg z) (norm_nonneg u)]
        _ = ((1 + ‖z‖) * f z) * ((1 : ℝ) + ‖u‖) := by ring
    · rw [Set.indicator_of_notMem hm, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hznn2 (hf0 z)) (by linarith [norm_nonneg u])
  have hg2meas :
    MeasureTheory.AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) z *
          ((1 + ‖z‖) * f z))
      volume :=
    (((by fun_prop :
                Measurable fun _ : EuclideanSpace ℝ (Fin n) =>
                  (1 : ℝ)).aestronglyMeasurable).indicator
          (measurableSet_norm_gt n ((K - 1 : ℕ) : ℝ))).mul
      (((by fun_prop :
              Measurable fun z : EuclideanSpace ℝ (Fin n) =>
                (1 : ℝ) + ‖z‖).aestronglyMeasurable).mul
        hfi.aestronglyMeasurable)
  have hg2int :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) z *
          ((1 + ‖z‖) * f z))
      volume := by
    refine MeasureTheory.Integrable.mono' hwfint hg2meas ?_
    filter_upwards with z
    have hznn2 : 0 ≤ (1 : ℝ) + ‖z‖ := by linarith [norm_nonneg z]
    rcases em (z ∈ {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}) with hm | hm
    · rw [Set.indicator_of_mem hm, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hznn2 (hf0 z))]
    · rw [Set.indicator_of_notMem hm, zero_mul, norm_zero]
      exact mul_nonneg hznn2 (hf0 z)
  -- the tail piece 2's transport and bound
  have hI2'le :
    ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
          x ∂volume ≤
      ((1 : ℝ) + ‖u‖) *
        ∫ x in {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖},
          (1 + ‖x‖) * f x ∂volume := by
    have hshift :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
            (WithLp.toLp 2 ((x : Fin n → ℝ) + -(u : Fin n → ℝ))) ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
            x ∂volume :=
      integral_toLp_trans_right n (-(u : Fin n → ℝ))
        (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
            x)
        hWf'2int.aestronglyMeasurable
    have hptx :
      ∀ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
            (WithLp.toLp 2 ((x : Fin n → ℝ) + -(u : Fin n → ℝ))) =
          {y : EuclideanSpace ℝ (Fin n) |
                  (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}.indicator
              (fun _ => (1 : ℝ)) x *
            ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f x) :=
      fun x => by
      rcases
        em
          (WithLp.toLp 2 ((x : Fin n → ℝ) + -(u : Fin n → ℝ)) ∈
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}) with
        hm | hm
      · have hx :
          x ∈
            {y : EuclideanSpace ℝ (Fin n) |
              (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖} := by
          show (K : ℝ) < ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖
          exact hm
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem hx]
        show
          (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
              f (WithLp.toLp 2 (((x : Fin n → ℝ) - (u : Fin n → ℝ)) + (u : Fin n → ℝ))) =
            1 * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f x)
        rw [one_mul, sub_add_cancel, WithLp.toLp_ofLp]
      · have hx :
          x ∉
            {y : EuclideanSpace ℝ (Fin n) |
              (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖} := by
          intro hc
          apply hm
          show (K : ℝ) < ‖WithLp.toLp 2 ((x : Fin n → ℝ) + -(u : Fin n → ℝ))‖
          exact hc
        rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hx, zero_mul]
    have htr :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
            x ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) |
                  (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}.indicator
              (fun _ => (1 : ℝ)) x *
            ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f x) ∂volume := by
      rw [← hshift]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptx)
    rw [htr]
    have hpt :
      ∀ z : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) |
                  (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}.indicator
              (fun _ => (1 : ℝ)) z *
            ((1 + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f z) ≤
          ((1 : ℝ) + ‖u‖) *
            ({y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ))
                z *
              ((1 + ‖z‖) * f z)) := by
      intro z
      rcases
        em
          (z ∈
            {y : EuclideanSpace ℝ (Fin n) |
              (K : ℝ) < ‖WithLp.toLp 2 ((y : Fin n → ℝ) - (u : Fin n → ℝ))‖}) with
        hm | hm
      · have hm' : (K : ℝ) < ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖ := hm
        have hz2 : z ∈ {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖} := by
          show ((K - 1 : ℕ) : ℝ) < ‖z‖
          have hsub : ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖ ≤ ‖z‖ + ‖u‖ :=
            norm_sub_le _ _
          have hKm1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ K), Nat.cast_one]
          linarith [hm', hsub, husmall, hKm1]
        rw [Set.indicator_of_mem hm, Set.indicator_of_mem hz2]
        show
          1 * ((1 + ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖) * f z) ≤
            ((1 : ℝ) + ‖u‖) * (1 * ((1 + ‖z‖) * f z))
        rw [one_mul, one_mul]
        have hsub : ‖WithLp.toLp 2 ((z : Fin n → ℝ) - (u : Fin n → ℝ))‖ ≤ ‖z‖ + ‖u‖ :=
          norm_sub_le _ _
        have hexp : ((1 : ℝ) + ‖u‖) * (1 + ‖z‖) = 1 + ‖z‖ + ‖u‖ + ‖z‖ * ‖u‖ := by ring
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (hf0 z)
        rw [hexp]
        linarith [hsub, norm_nonneg z, norm_nonneg u, mul_nonneg (norm_nonneg z) (norm_nonneg u)]
      · rw [Set.indicator_of_notMem hm, zero_mul]
        rcases em (z ∈ {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}) with hz2 | hz2
        · rw [Set.indicator_of_mem hz2]
          show 0 ≤ ((1 : ℝ) + ‖u‖) * (1 * ((1 + ‖z‖) * f z))
          exact
            mul_nonneg (by linarith [norm_nonneg u])
              (mul_nonneg zero_le_one (mul_nonneg (by linarith [norm_nonneg z]) (hf0 z)))
        · rw [Set.indicator_of_notMem hz2, zero_mul, mul_zero]
    have hpt2 :
      ∀ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) x *
            ((1 + ‖x‖) * f x) =
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator
            (fun w => (1 + ‖w‖) * f w) x :=
      fun x => by
      rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}) with h | h
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        show (1 : ℝ) * ((1 + ‖x‖) * f x) = (1 + ‖x‖) * f x
        rw [one_mul]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
    have hstep1 :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) x *
            ((1 + ‖x‖) * f x) ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator
            (fun w => (1 + ‖w‖) * f w) x ∂volume :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt2)
    have hstep2 :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator
            (fun w => (1 + ‖w‖) * f w) x ∂volume =
        ∫ x in {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
      MeasureTheory.integral_indicator hB3meas
    have hconv :
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) x *
            ((1 + ‖x‖) * f x) ∂volume =
        ∫ x in {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
      hstep1.trans hstep2
    have hconst :
      ∫ x : EuclideanSpace ℝ (Fin n),
          ((1 : ℝ) + ‖u‖) *
            ({y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ))
                x *
              ((1 + ‖x‖) * f x)) ∂volume =
        ((1 : ℝ) + ‖u‖) *
          ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ))
                x *
              ((1 + ‖x‖) * f x) ∂volume :=
      MeasureTheory.integral_const_mul ((1 : ℝ) + ‖u‖)
        (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ)) x *
            ((1 + ‖x‖) * f x))
    refine le_trans (MeasureTheory.integral_mono hgint (hg2int.const_mul ((1 : ℝ) + ‖u‖)) hpt) ?_
    show
      ∫ x : EuclideanSpace ℝ (Fin n),
          ((1 : ℝ) + ‖u‖) *
            ({y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}.indicator (fun _ => (1 : ℝ))
                x *
              ((1 + ‖x‖) * f x)) ∂volume ≤
        ((1 : ℝ) + ‖u‖) *
          ∫ x in {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume
    rw [hconst, hconv]
  -- the tail-dominated bound for the outside-ball piece
  have htailB :
    ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
          x ∂volume <
      ε / 8 + ε / 4 := by
    refine
      lt_of_le_of_lt
        (MeasureTheory.integral_mono (hWint.indicator hBmeas)
          ((hwfint.indicator hBmeas).add hWf'2int) ?_)
        ?_
    · exact fun x => by
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}) with hm | hm
        · show
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
                x ≤
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                  (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x +
                {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                  (fun y : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
                  x
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Set.indicator_of_mem hm]
          show
            (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ≤
              (1 + ‖x‖) * f x + (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))
          have habsle :
            |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ≤
              f x + f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))) := by
            refine le_trans (abs_sub _ _) ?_
            rw [abs_of_nonneg (hf0 x), abs_of_nonneg (hf0 _)]
          calc
            (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ≤
                (1 + ‖x‖) * (f x + f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))) :=
              mul_le_mul_of_nonneg_left habsle (by linarith [norm_nonneg x])
            _ =
                (1 + ‖x‖) * f x +
                  (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ))) :=
              by rw [mul_add]
        · show
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
                x ≤
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                  (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x +
                {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                  (fun y : EuclideanSpace ℝ (Fin n) =>
                    (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
                  x
          rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
          norm_num
    · show
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x +
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
                x ∂volume <
          ε / 8 + ε / 4
      have hadd :
        (∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x +
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
                x ∂volume) =
          (∫ x : EuclideanSpace ℝ (Fin n),
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * f y) x ∂volume) +
            (∫ x : EuclideanSpace ℝ (Fin n),
              {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
                (fun y : EuclideanSpace ℝ (Fin n) =>
                  (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
                x ∂volume) :=
        MeasureTheory.integral_add (hwfint.indicator hBmeas) hWf'2int
      rw [hadd, hI1']
      have h1 :
        ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume < ε / 8 :=
        htK
      have h2 :
        ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
              (fun y : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖y‖) * f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ))))
              x ∂volume ≤
          ε / 4 := by
        refine le_trans hI2'le ?_
        have hA :
          ((1 : ℝ) + ‖u‖) *
              ∫ x in {y : EuclideanSpace ℝ (Fin n) | ((K - 1 : ℕ) : ℝ) < ‖y‖},
                (1 + ‖x‖) * f x ∂volume ≤
            ((1 : ℝ) + ‖u‖) * (ε / 8) :=
          mul_le_mul_of_nonneg_left (le_of_lt htK1) (by linarith [norm_nonneg u])
        have hu2 : (1 : ℝ) + ‖u‖ ≤ 2 := by linarith [husmall]
        have hε0 : (0 : ℝ) ≤ ε := hε.le
        have hB : ((1 : ℝ) + ‖u‖) * (ε / 8) ≤ ε / 4 := by
          have hhalf : ((1 : ℝ) + ‖u‖) * (ε / 8) ≤ 2 * (ε / 8) :=
            mul_le_mul_of_nonneg_right hu2 (div_nonneg hε0 (by norm_num))
          have heq : (2 : ℝ) * (ε / 8) = ε / 4 := by ring
          linarith
        exact le_trans hA hB
      linarith
  -- the sandwich and the final arithmetic
  have hsplit :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume =
      ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
            x ∂volume +
        ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
            x ∂volume := by
    have heq :
      (∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume) =
        (∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)}.indicator
              (fun y : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
              x +
            {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}.indicator
              (fun y : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
              x ∂volume) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinteq)
    rw [heq, MeasureTheory.integral_add (hWint.indicator hAm) (hWint.indicator hBmeas)]
  have hcoreu2 :
    ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K : ℝ)}.indicator
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖y‖) * |f y - f (WithLp.toLp 2 ((y : Fin n → ℝ) + (u : Fin n → ℝ)))|)
          x ∂volume <
      ε / 2 := by
    refine lt_of_le_of_lt hcoreB ?_
    calc
      ((1 : ℝ) + K) *
            ∫ x : EuclideanSpace ℝ (Fin n),
              |f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) + (u : Fin n → ℝ)))| ∂volume <
          ((1 : ℝ) + K) * (ε / (2 * (1 + (K : ℝ)))) :=
        mul_lt_mul_of_pos_left hcoreu (by positivity)
      _ = ε / 2 := by
        have hcpos : (0 : ℝ) < 2 * (1 + (K : ℝ)) := by positivity
        field_simp [hcpos]
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)),
    hsplit]
  refine lt_trans (add_lt_add hcoreu2 htailB) ?_
  linarith

/-! ## Phase 2, Step 1: weighted Gaussian smoothing for general (measurable) `f`

Using `weighted_modulus_tendsto_integrable` (Step 0), we remove the continuity hypothesis
from `weightedModulus`'s limit at `0` and from the Phase 1 Gaussian smoothing theorem. -/

/-- The weighted translation modulus `weightedModulus n f u = ∫ (1 + ‖x‖) * |f (x − u) − f x| dx`
tends to `0` as `u → 0` for any nonnegative integrable `f` with finite first moment (no continuity
assumption on `f`). -/
public theorem weightedModulus_tendsto_integrable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : 0 ≤ f) (hfi : MeasureTheory.Integrable f volume)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume) :
    Filter.Tendsto (weightedModulus n f) (nhds 0) (nhds 0) := by
  have hneg : Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin n) => -u) (nhds 0) (nhds 0) := by
    simpa only [neg_zero] using (continuous_neg.tendsto (0 : EuclideanSpace ℝ (Fin n)))
  have hcomp := (weighted_modulus_tendsto_integrable f hf0 hfi hfmom).comp hneg
  refine hcomp.congr fun u => ?_
  show
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          |f x -
              f
                (WithLp.toLp 2
                  ((x : Fin n → ℝ) + ((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)))| ∂volume =
      ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show
    (1 + ‖x‖) *
        |f x -
            f (WithLp.toLp 2 ((x : Fin n → ℝ) + ((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)))| =
      (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|
  have hsub :
    WithLp.toLp 2 ((x : Fin n → ℝ) + ((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) =
      WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)) :=
    rfl
  rw [hsub, abs_sub_comm]

/-- **Phase 2, Step 1 (`weighted_smoothing_integrable`)**: for any measurable pdf `f` with finite
first moment (no continuity needed), the weighted L¹ distance between `f` and its Gaussian
smoothing tends to `0` along every positive sequence `σ k → 0`. -/
public theorem weighted_smoothing_integrable (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℕ → ℝ) (hσ : ∀ k, 0 < σ k)
    (hσ0 : Filter.Tendsto σ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |f x - gaussSmoothed n f C hC (σ k) (hσ k) x| ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hMnn : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume :=
    MeasureTheory.integral_nonneg fun y => mul_nonneg (norm_nonneg y) (hf0 y)
  have hwmseq :
    ∀ (u : ℕ → EuclideanSpace ℝ (Fin n)),
      Filter.Tendsto u Filter.atTop (nhds 0) →
        Filter.Tendsto (fun k : ℕ => weightedModulus n f (u k)) Filter.atTop (nhds 0) :=
    fun u hu => (weightedModulus_tendsto_integrable f hf0 hfi hfmom).comp hu
  have hwmAe := aemeasurable_weightedModulus n f hfm
  -- the per-σ chain, reusing the extracted Step A and Step B lemmas
  have hchain :
    ∀ (s : ℝ) (hs : 0 < s),
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume ≤
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((s : ℝ) • (v : Fin n → ℝ))) ∂volume := by
    intro s hs
    have hstepA := stepA_gaussSmoothed n f hfm hpdf hfmom C hC s hs
    have hΦint := integrable_joint_first n f hfm hpdf hfmom C hC s hs
    have hFxint := integrable_joint_second n f hfm hpdf hfmom C hC s hs
    have hRint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ∫ y : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              (mollifier n C hC s hs y *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume)
        volume :=
      hFxint.integral_prod_left
    have hA :
      ∀ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ≤
          ∫ y : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              (mollifier n C hC s hs y *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume := by
      intro x
      refine le_trans (mul_le_mul_of_nonneg_left (hstepA x) (by linarith [norm_nonneg x])) ?_
      exact
        le_of_eq
          ((MeasureTheory.integral_const_mul (1 + ‖x‖)
              (fun u =>
                mollifier n C hC s hs u *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)).symm)
    have hLint :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)
        volume :=
      integrable_weighted_abs_diff_gaussSmoothed n f hfm hpdf hfmom C hC s hs
    have hB1 :
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume ≤
        ∫ u : EuclideanSpace ℝ (Fin n),
          ∫ x : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              ((1 + ‖x‖) *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume := by
      refine le_trans (MeasureTheory.integral_mono hLint hRint hA) ?_
      calc
        ∫ x : EuclideanSpace ℝ (Fin n),
              ∫ u : EuclideanSpace ℝ (Fin n),
                (1 + ‖x‖) *
                  (mollifier n C hC s hs u *
                    |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume ≤
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.1‖) *
                (mollifier n C hC s hs z.2 *
                  |f (WithLp.toLp 2 ((z.1 : Fin n → ℝ) - (z.2 : Fin n → ℝ))) -
                      f z.1|) ∂(volume.prod volume) :=
          by
          rw [←
            MeasureTheory.integral_prod (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (1 + ‖p.1‖) *
                (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume) hFxint]
        _ =
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.swap.1‖) *
                (mollifier n C hC s hs z.swap.2 *
                  |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) -
                      f z.swap.1|) ∂(volume.prod volume) :=
          by
          rw [←
            MeasureTheory.integral_prod_swap (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              (1 + ‖p.1‖) *
                (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume)]
        _ =
            ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              mollifier n C hC s hs z.1 *
                ((1 + ‖z.2‖) *
                  |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) -
                      f z.2|) ∂(volume.prod volume) :=
          by
          have hswapcongr :
            ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.swap.1‖) *
                  (mollifier n C hC s hs z.swap.2 *
                    |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) - f z.swap.1|) =
                mollifier n C hC s hs z.1 *
                  ((1 + ‖z.2‖) *
                    |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) - f z.2|) := by
            intro z
            simp only [Prod.swap]
            ring
          exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hswapcongr)
        _ =
            ∫ u : EuclideanSpace ℝ (Fin n),
              ∫ x : EuclideanSpace ℝ (Fin n),
                mollifier n C hC s hs u *
                  ((1 + ‖x‖) *
                    |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) -
                        f x|) ∂volume ∂volume :=
          by
          rw [MeasureTheory.integral_prod (f :=
              fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              mollifier n C hC s hs p.1 *
                ((1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
              (μ := volume) (ν := volume) hΦint]
    refine
      le_trans
        (le_trans hB1
          (le_of_eq
            (MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall fun u => by
                simp only [weightedModulus]
                rw [MeasureTheory.integral_const_mul (mollifier n C hC s hs u)]))))
        (le_of_eq (integral_mollifier_mul n C hC s hs (weightedModulus n f) hwmAe))
  -- Step C: dominated convergence on the shifted sequence `σ (· + k₀)`
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ0 1 one_pos)
  have hσ1 : ∀ k : ℕ, (σ (k + k₀) : ℝ) ≤ 1 := by
    intro k
    have h := hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h
    exact le_of_lt h
  have hσ' : Filter.Tendsto (fun k : ℕ => σ (k + k₀)) Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ0 δ hδ)
    exact
      Filter.eventually_atTop.mpr
        ⟨N, fun k hk => hN (k + k₀) (Nat.le_trans hk (Nat.le_add_right k k₀))⟩
  have hdct :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
      Filter.atTop (nhds 0) := by
    have hbdint :
      MeasureTheory.Integrable
        (fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v *
            ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
        volume := by
      have hφCint : MeasureTheory.Integrable (multivariateGaussianPDF n 0 C hC) volume :=
        integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC)
      have h1 :
        MeasureTheory.Integrable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2))
          volume :=
        hφCint.mul_const _
      have h2 :
        MeasureTheory.Integrable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
              (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))
          volume :=
        (integrable_norm_mul_gaussianPDF_center n C hC).mul_const _
      have heq :
        (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖))) =
          (fun v : EuclideanSpace ℝ (Fin n) =>
              multivariateGaussianPDF n 0 C hC v *
                ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2)) +
            (fun v : EuclideanSpace ℝ (Fin n) =>
              (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
                (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) := by
        funext v
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact h1.add h2
    have hwmSm : StronglyMeasurable (weightedModulus n f) := by
      have hKmeas :
        Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := by
        fun_prop
      exact hKmeas.stronglyMeasurable.integral_prod_right'
    have hFmeas :
      ∀ k : ℕ,
        AEStronglyMeasurable
          (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
          volume :=
      fun k =>
      ((measurable_multivariateGaussianPDF n 0 C hC).stronglyMeasurable.mul
          (hwmSm.comp_measurable
            (by fun_prop :
              Measurable fun v : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))).aestronglyMeasurable
    have hbound :
      ∀ k : ℕ,
        ∀ᵐ (v : EuclideanSpace ℝ (Fin n)) ∂volume,
          ‖multivariateGaussianPDF n 0 C hC v *
                weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))‖ ≤
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)) :=
      fun k =>
      Filter.Eventually.of_forall
        (fun v => by
          have hwmnn :
            0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) :=
            show
              0 ≤
                ∫ x : EuclideanSpace ℝ (Fin n),
                  (1 + ‖x‖) *
                    |f
                          (WithLp.toLp 2
                            ((x : Fin n → ℝ) -
                              (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)) : Fin n → ℝ))) -
                        f x| ∂volume
              from
              MeasureTheory.integral_nonneg fun x =>
                mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (multivariateGaussianPDF_pos n 0 C hC v),
            abs_of_nonneg hwmnn]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
          refine
            le_trans
              (weightedModulus_le n f hfm hpdf hfmom
                (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
              ?_
          refine mul_le_mul_of_nonneg_left ?_ (by linarith [hMnn])
          have hnorm :
            ‖WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))‖ = (σ (k + k₀) : ℝ) * ‖v‖ := by
            rw [show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) = (σ (k + k₀) : ℝ) • v
                from rfl,
              norm_smul]
            congr 1
            rw [Real.norm_eq_abs, abs_of_pos (hσ _)]
          rw [hnorm]
          linarith [mul_le_mul_of_nonneg_right (hσ1 k) (norm_nonneg v)])
    have hlim :
      ∀ᵐ v : EuclideanSpace ℝ (Fin n),
        Filter.Tendsto
          (fun k : ℕ =>
            multivariateGaussianPDF n 0 C hC v *
              weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
          Filter.atTop (nhds 0) := by
      filter_upwards with v
      have hv0 :
        Filter.Tendsto (fun k : ℕ => WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))
          Filter.atTop (nhds 0) := by
        refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
        rcases eq_or_ne v 0 with hv | hv
        · refine Filter.Eventually.of_forall fun k => ?_
          rw [hv, show ((0 : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = 0 from rfl, smul_zero,
            show (WithLp.toLp 2 (0 : Fin n → ℝ)) = (0 : EuclideanSpace ℝ (Fin n)) from rfl,
            dist_self]
          exact hδ
        · obtain ⟨N, hN⟩ :=
            Filter.eventually_atTop.mp
              (Metric.tendsto_nhds.mp hσ' (δ / ‖v‖) (div_pos hδ (norm_pos_iff.2 hv)))
          refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have h1 := hN k hk
          rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h1
          rw [dist_zero_right,
            show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) = (σ (k + k₀) : ℝ) • v from
              rfl,
            norm_smul, Real.norm_eq_abs, abs_of_pos (hσ _)]
          calc
            (σ (k + k₀) : ℝ) * ‖v‖ < (δ / ‖v‖) * ‖v‖ :=
              mul_lt_mul_of_pos_right h1 (norm_pos_iff.2 hv)
            _ = δ := by rw [div_mul_cancel₀ _ (ne_of_gt (norm_pos_iff.2 hv))]
      have hwm0 := hwmseq _ hv0
      have := (tendsto_const_nhds (x := multivariateGaussianPDF n 0 C hC v)).mul hwm0
      simpa using this
    have hdct' :=
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v *
            ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
        (f := fun _ => (0 : ℝ)) hFmeas hbdint hbound hlim
    rw [integral_zero] at hdct'
    exact hdct'
  have hmain :
    Filter.Tendsto
      (fun k : ℕ =>
        ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ))))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat k₀).mp hdct
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hmain ε hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  have hNk := hN k hk
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (MeasureTheory.integral_nonneg
        (fun v : EuclideanSpace ℝ (Fin n) =>
          mul_nonneg (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
            (show 0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ))) from
              MeasureTheory.integral_nonneg fun x =>
                mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))))] at hNk
  have h0 :
    0 ≤
      ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC (σ k) (hσ k) x| ∂volume :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h0]
  exact lt_of_le_of_lt (hchain (σ k) (hσ k)) hNk

/-! ## Phase 2, Step 2: half-open lattice cell construction

We discretize the box `[-Nδ, Nδ)^n` into half-open cells `cell δ k` indexed by integer
grid vectors `k ∈ gridFinset n N = [-N, N)^n ∩ ℤ^n`. Because `cell δ k` is defined by
`k_i * δ ≤ t_i < (k_i + 1) * δ` (equivalently `⌊t_i / δ⌋ = k_i` for `δ > 0`), the cells
are measurably partitioned with no boundary overlap, and their union `coveredBox n δ N`
satisfies `MeasureTheory.integral_biUnion_finset` directly. -/

/-- The finite index set `[-N, N)^n ∩ ℤ^n` of integer grid vectors for a box of integer
half-width `N : ℕ`. -/
@[expose]
public def gridFinset (n : ℕ) (N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Ico (-(N : ℤ)) (N : ℤ))

/-- Componentwise floor-index map `t ↦ (⌊t_i / δ⌋)_i`. -/
@[expose]
public noncomputable def latticeIdx {n : ℕ} (δ : ℝ) (t : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ :=
  fun i => ⌊(t : Fin n → ℝ) i / δ⌋

/-- Componentwise lattice floor-quantizer `Q_δ(t) = (δ * ⌊t_i / δ⌋)_i`. -/
@[expose]
public noncomputable def latticeQ {n : ℕ} (δ : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ))

/-- The lattice center point `x_k = (δ * k_i)_i` of cell `k : Fin n → ℤ`. -/
@[expose]
public noncomputable def gridPoint {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => δ * (k i : ℝ))

/-- The half-open lattice cell `∏_i [k_i δ, (k_i + 1) δ)`. -/
@[expose]
public def cell {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {t | ∀ i : Fin n, (k i : ℝ) * δ ≤ (t : Fin n → ℝ) i ∧ (t : Fin n → ℝ) i < ((k i : ℝ) + 1) * δ}

/-- The union of the half-open cells `cell δ k` over `k ∈ gridFinset n N`, equal to
`[-Nδ, Nδ)^n`. -/
@[expose]
public def coveredBox (n : ℕ) (δ : ℝ) (N : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  ⋃ k ∈ gridFinset n N, cell δ k

/-- The prior mass on cell `k`: `W_k = ∫_{cell δ k} f(t) dt`. -/
@[expose]
public noncomputable def cellWeight {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (δ : ℝ)
    (k : Fin n → ℤ) : ℝ :=
  ∫ t in cell δ k, f t ∂volume

/-- Membership in `cell δ k` is equivalent to `latticeIdx δ t = k` when `0 < δ`. -/
public theorem mem_cell_iff_latticeIdx {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ)
    (t : EuclideanSpace ℝ (Fin n)) : t ∈ cell δ k ↔ latticeIdx δ t = k := by
  simp only [cell, Set.mem_ofPred_eq, latticeIdx, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]

/-- On `t ∈ cell δ k`, the floor quantizer `latticeQ δ t` coincides with `gridPoint δ k`. -/
public theorem latticeQ_eq_gridPoint_of_mem_cell {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {k : Fin n → ℤ}
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ cell δ k) : latticeQ δ t = gridPoint δ k := by
  have hk := (mem_cell_iff_latticeIdx hδ k t).mp ht
  apply WithLp.ofLp_injective
  ext i
  have hki : ⌊(t : Fin n → ℝ) i / δ⌋ = k i := congrFun hk i
  show δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) = δ * (k i : ℝ)
  rw [hki]

/-- Each half-open cell `cell δ k` is measurable. -/
public theorem measurableSet_cell {n : ℕ} (δ : ℝ) (k : Fin n → ℤ) : MeasurableSet (cell δ k) := by
  have heq :
    cell δ k =
      ⋂ i : Fin n,
        (fun t : EuclideanSpace ℝ (Fin n) => (t : Fin n → ℝ) i) ⁻¹'
          Set.Ico ((k i : ℝ) * δ) (((k i : ℝ) + 1) * δ) := by
    ext t
    simp [cell]
  rw [heq]
  refine MeasurableSet.iInter fun i => ?_
  exact measurableSet_Ico.preimage (by fun_prop)

/-- The covered box `coveredBox n δ N` is measurable. -/
public theorem measurableSet_coveredBox (n : ℕ) (δ : ℝ) (N : ℕ) :
    MeasurableSet (coveredBox n δ N) :=
  (gridFinset n N).measurableSet_biUnion fun k _ => measurableSet_cell δ k

/-- Distinct cells `cell δ k₁` and `cell δ k₂` are disjoint for `0 < δ`. -/
public theorem pairwiseDisjoint_cell {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (s : Set (Fin n → ℤ)) :
    s.PairwiseDisjoint (cell δ) := by
  intro k₁ _ k₂ _ hne
  change Disjoint (cell δ k₁) (cell δ k₂)
  rw [Set.disjoint_left]
  intro t ht₁ ht₂
  apply hne
  rw [← (mem_cell_iff_latticeIdx hδ k₁ t).mp ht₁, ← (mem_cell_iff_latticeIdx hδ k₂ t).mp ht₂]

/-- **Partition identity**: the sum of cell integrals over `gridFinset n N` equals the set
integral over `coveredBox n δ N`. -/
public theorem sum_setIntegral_cell {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (g : EuclideanSpace ℝ (Fin n) → E)
    (hg : MeasureTheory.Integrable g volume) :
    ∑ k ∈ gridFinset n N, ∫ t in cell δ k, g t ∂volume = ∫ t in coveredBox n δ N, g t ∂volume := by
  exact
    (MeasureTheory.integral_biUnion_finset (gridFinset n N) (fun k _ => measurableSet_cell δ k)
        (pairwiseDisjoint_cell hδ (gridFinset n N : Set (Fin n → ℤ)))
        (fun k _ => hg.integrableOn)).symm

/-- Every point `t` with `‖t‖ < N * δ` belongs to `coveredBox n δ N` whenever `0 < δ`. -/
public theorem norm_lt_subset_coveredBox {n : ℕ} {δ R : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hRN : R < (N : ℝ) * δ) : {t : EuclideanSpace ℝ (Fin n) | ‖t‖ ≤ R} ⊆ coveredBox n δ N := by
  intro t ht
  have ht' : ‖t‖ ≤ R := ht
  rw [coveredBox, Set.mem_iUnion₂]
  refine ⟨latticeIdx δ t, ?_, (mem_cell_iff_latticeIdx hδ (latticeIdx δ t) t).mpr rfl⟩
  rw [gridFinset, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Ico]
  have hti_abs : |(t : Fin n → ℝ) i| ≤ ‖t‖ := by
    have h := PiLp.norm_apply_le (p := 2) t i
    simpa [Real.norm_eq_abs] using h
  have hti_lt : |(t : Fin n → ℝ) i| < (N : ℝ) * δ := lt_of_le_of_lt (le_trans hti_abs ht') hRN
  have hlow : -((N : ℝ) * δ) < (t : Fin n → ℝ) i := (abs_lt.mp hti_lt).1
  have hhigh : (t : Fin n → ℝ) i < (N : ℝ) * δ := (abs_lt.mp hti_lt).2
  dsimp only [latticeIdx]
  refine ⟨?_, ?_⟩
  · rw [Int.le_floor, Int.cast_neg, Int.cast_natCast, le_div_iff₀ hδ, neg_mul]
    exact le_of_lt hlow
  · rw [Int.floor_lt, Int.cast_natCast, div_lt_iff₀ hδ]
    exact hhigh

/-- The complement of `coveredBox n δ N` is contained in the tail `{t | R < ‖t‖}` whenever
`0 < δ` and `R < N * δ`. -/
public theorem compl_coveredBox_subset_norm_gt {n : ℕ} {δ R : ℝ} {N : ℕ} (hδ : 0 < δ)
    (hRN : R < (N : ℝ) * δ) : (coveredBox n δ N)ᶜ ⊆ {t : EuclideanSpace ℝ (Fin n) | R < ‖t‖} := by
  intro t ht
  change R < ‖t‖
  by_contra hle
  exact ht (norm_lt_subset_coveredBox hδ hRN (not_lt.mp hle))

/-- **Displacement bound (`norm_latticeQ_sub_le`)**: the Euclidean distance between `t` and
its floor quantization `latticeQ δ t` is at most `δ * √n` for `0 < δ`. -/
public theorem norm_latticeQ_sub_le {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (t : EuclideanSpace ℝ (Fin n)) :
    ‖latticeQ δ t - t‖ ≤ δ * Real.sqrt (n : ℝ) := by
  have hcoord : ∀ i : Fin n, ‖(latticeQ δ t - t : EuclideanSpace ℝ (Fin n)) i‖ ≤ δ := by
    intro i
    change |δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) - (t : Fin n → ℝ) i| ≤ δ
    have h1 : (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) ≤ (t : Fin n → ℝ) i / δ :=
      Int.floor_le ((t : Fin n → ℝ) i / δ)
    have h2 : (t : Fin n → ℝ) i / δ < (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) + 1 :=
      Int.lt_floor_add_one ((t : Fin n → ℝ) i / δ)
    have h1' : δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) ≤ (t : Fin n → ℝ) i := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hδ)
      rwa [mul_div_cancel₀ _ (ne_of_gt hδ)] at this
    have h2' : (t : Fin n → ℝ) i < δ * (⌊(t : Fin n → ℝ) i / δ⌋ : ℝ) + δ := by
      have := mul_lt_mul_of_pos_left h2 hδ
      rwa [mul_div_cancel₀ _ (ne_of_gt hδ), mul_add, mul_one] at this
    rw [abs_le]
    constructor <;> linarith
  rw [EuclideanSpace.norm_eq]
  have hsum :
    ∑ i : Fin n, ‖(latticeQ δ t - t : EuclideanSpace ℝ (Fin n)) i‖ ^ 2 ≤ ∑ _i : Fin n, δ ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact
      sq_le_sq.mpr
        (by
          rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ]
          exact hcoord i)
  have hcard : (∑ _i : Fin n, δ ^ 2) = (n : ℝ) * δ ^ 2 := by simp [Finset.sum_const]
  calc
    Real.sqrt (∑ i : Fin n, ‖(latticeQ δ t - t : EuclideanSpace ℝ (Fin n)) i‖ ^ 2) ≤
        Real.sqrt ((n : ℝ) * δ ^ 2) :=
      by
      rw [← hcard]
      exact Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (n : ℝ) * Real.sqrt (δ ^ 2) := Real.sqrt_mul (Nat.cast_nonneg n) (δ ^ 2)
    _ = δ * Real.sqrt (n : ℝ) := by rw [Real.sqrt_sq (le_of_lt hδ), mul_comm]

/-- For `t ∈ cell δ k`, `‖gridPoint δ k - t‖ ≤ δ * √n` and `‖t - gridPoint δ k‖ ≤ δ * √n`. -/
public theorem norm_gridPoint_sub_le_of_mem_cell {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {k : Fin n → ℤ}
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ cell δ k) :
    ‖gridPoint δ k - t‖ ≤ δ * Real.sqrt (n : ℝ) := by
  rw [← latticeQ_eq_gridPoint_of_mem_cell hδ ht]
  exact norm_latticeQ_sub_le hδ t

public theorem norm_sub_gridPoint_le_of_mem_cell {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {k : Fin n → ℤ}
    {t : EuclideanSpace ℝ (Fin n)} (ht : t ∈ cell δ k) :
    ‖t - gridPoint δ k‖ ≤ δ * Real.sqrt (n : ℝ) := by
  rw [norm_sub_rev]
  exact norm_gridPoint_sub_le_of_mem_cell hδ ht

/-- Each cell weight `cellWeight f δ k` is nonnegative when `0 ≤ f`. -/
public theorem cellWeight_nonneg {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf0 : 0 ≤ f) (δ : ℝ)
    (k : Fin n → ℤ) : 0 ≤ cellWeight f δ k :=
  MeasureTheory.setIntegral_nonneg (measurableSet_cell δ k) (fun t _ => hf0 t)

/-- The sum of cell weights over `gridFinset n N` equals `∫ t in coveredBox n δ N, f t`. -/
public theorem sum_cellWeight {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfi : MeasureTheory.Integrable f volume) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    ∑ k ∈ gridFinset n N, cellWeight f δ k = ∫ t in coveredBox n δ N, f t ∂volume :=
  sum_setIntegral_cell hδ N f hfi

/-- For a pdf `f`, the sum of cell weights over `gridFinset n N` is in `[0, 1]`, and the
residual weight `1 - ∑ k ∈ gridFinset n N, cellWeight f δ k` equals the complement integral
`∫ t in (coveredBox n δ N)ᶜ, f t ∂volume ≥ 0`. -/
public theorem one_sub_sum_cellWeight_eq {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hpdf : IsPdf f)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    1 - ∑ k ∈ gridFinset n N, cellWeight f δ k = ∫ t in (coveredBox n δ N)ᶜ, f t ∂volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  rw [sum_cellWeight hfi hδ N, ← hpdf.2, ←
    MeasureTheory.integral_add_compl (measurableSet_coveredBox n δ N) hfi]
  ring

public theorem sum_cellWeight_le_one {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hpdf : IsPdf f)
    {δ : ℝ} (hδ : 0 < δ) (N : ℕ) : ∑ k ∈ gridFinset n N, cellWeight f δ k ≤ 1 := by
  have h := one_sub_sum_cellWeight_eq hpdf hδ N
  have hnn : 0 ≤ ∫ t in (coveredBox n δ N)ᶜ, f t ∂volume :=
    MeasureTheory.setIntegral_nonneg (measurableSet_coveredBox n δ N).compl (fun t _ => hpdf.1 t)
  linarith

/-! ## Phase 2, Step 3a: mollifier scaling, weighted moments, and shifted-kernel bounds

Pure Gaussian/mollifier analysis (independent of the prior `f` and the lattice grid):
* `isPdf_mollifier`, `integrable_norm_mul_mollifier`, `integrable_weighted_mollifier_sub`:
  the mollifier `ψ_σ` is a pdf with finite first moment, and `(1 + ‖x‖) * ψ_σ(x - t)` is
  Bochner-integrable for every shift `t`;
* `integral_weighted_mollifier_sub_le`: for `0 < σ ≤ 1`,
  `∫ x, (1 + ‖x‖) * ψ_σ(x - t) dx ≤ (1 + ‖t‖) * (1 + M_φ)`;
* `weighted_mollifier_shift_le`: for `0 < σ ≤ 1` and any `t, x_k`,
  `∫ x, (1 + ‖x‖) * |ψ_σ(x - x_k) - ψ_σ(x - t)| dx
    ≤ (1 + ‖t‖) * weightedModulus n φ_C (σ⁻¹ • (x_k - t))`. -/

/-- The Gaussian mollifier `mollifier n C hC σ hσ` is a pdf. -/
public theorem isPdf_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) : IsPdf (mollifier n C hC σ hσ) :=
  ⟨fun x => mollifier_nonneg n C hC σ hσ x, integral_mollifier n C hC σ hσ⟩

/-- The first moment of `mollifier n C hC σ hσ` is Bochner-integrable. -/
public theorem integrable_norm_mul_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * mollifier n C hC σ hσ u)
      volume := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hmeas : Measurable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * mollifier n C hC σ hσ u) := by
    fun_prop
  have hnn : 0 ≤ᵐ[volume] (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ * mollifier n C hC σ hσ u) :=
    Filter.Eventually.of_forall fun u => mul_nonneg (norm_nonneg u) (mollifier_nonneg n C hC σ hσ u)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
  have hpt :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (‖u‖ * mollifier n C hC σ hσ u) =
        ENNReal.ofReal (mollifier n C hC σ hσ u) * ENNReal.ofReal ‖u‖ :=
    fun u => by rw [mul_comm ‖u‖ _, ENNReal.ofReal_mul (mollifier_nonneg n C hC σ hσ u)]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
    lintegral_mollifier_mul_norm n C hC σ hσ]
  exact ENNReal.ofReal_lt_top

/-- `(1 + ‖u‖) * mollifier n C hC σ hσ u` is Bochner-integrable. -/
public theorem integrable_weighted_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin n) => (1 + ‖u‖) * mollifier n C hC σ hσ u) volume := by
  have heq :
    (fun u : EuclideanSpace ℝ (Fin n) => (1 + ‖u‖) * mollifier n C hC σ hσ u) =
      fun u : EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC σ hσ u + ‖u‖ * mollifier n C hC σ hσ u := by
    funext u; ring
  rw [heq]
  exact (mollifier_integrable n C hC σ hσ).add (integrable_norm_mul_mollifier n C hC σ hσ)

/-- The exact weighted mass of the mollifier:
`∫ u, (1 + ‖u‖) * ψ_σ(u) du = 1 + σ * ∫ v, ‖v‖ * φ_C(v) dv`. -/
public theorem integral_weighted_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    ∫ u : EuclideanSpace ℝ (Fin n), (1 + ‖u‖) * mollifier n C hC σ hσ u ∂volume =
      1 + σ * ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume := by
  have htr :=
    integral_mollifier_mul n C hC σ hσ (fun u : EuclideanSpace ℝ (Fin n) => 1 + ‖u‖) (by fun_prop)
  have h1 :
    (∫ u : EuclideanSpace ℝ (Fin n), (1 + ‖u‖) * mollifier n C hC σ hσ u ∂volume) =
      ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ u * (1 + ‖u‖) ∂volume :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  rw [h1, htr]
  have hpt :
    (fun v : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC v * (1 + ‖WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))‖)) =
      fun v : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n 0 C hC v + σ * (‖v‖ * multivariateGaussianPDF n 0 C hC v) := by
    funext v
    have hnorm : ‖WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))‖ = σ * ‖v‖ := by
      rw [show (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) = (σ : ℝ) • v from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_pos hσ]
    rw [hnorm]
    ring
  rw [hpt,
    MeasureTheory.integral_add (integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC))
      ((integrable_norm_mul_gaussianPDF_center n C hC).const_mul σ),
    integral_gaussianPDF n 0 C hC, MeasureTheory.integral_const_mul]

/-- For any shift `t`, `x ↦ (1 + ‖x‖) * mollifier n C hC σ hσ (x - t)` is integrable. -/
public theorem integrable_weighted_mollifier_sub (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (t : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))
      volume := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hwψ := integrable_weighted_mollifier n C hC σ hσ
  have hwψ_meas :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) := by
    fun_prop
  have hshift :=
    integrable_toLp_shift n (-(t : Fin n → ℝ))
      (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) hwψ hwψ_meas
  refine MeasureTheory.Integrable.mono' (hshift.const_mul (1 + ‖t‖)) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))).aestronglyMeasurable
  · filter_upwards with x
    show
      ‖(1 + ‖x‖) * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))‖ ≤
        (1 + ‖t‖) *
          ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) + -(t : Fin n → ℝ))‖) *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) + -(t : Fin n → ℝ))))
    have hsub :
      WithLp.toLp 2 ((x : Fin n → ℝ) + -(t : Fin n → ℝ)) =
        WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) :=
      rfl
    rw [hsub, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg x]) (mollifier_nonneg n C hC σ hσ _)), ←
      mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (mollifier_nonneg n C hC σ hσ _)
    have hxt : WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) = x - t := rfl
    have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ + ‖t‖ := by
      rw [hxt]
      calc
        ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le (x - t) t
    have hexp :
      (1 + ‖t‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) =
        1 + ‖t‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ +
          ‖t‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ := by
      ring
    rw [hexp]
    linarith [htri, norm_nonneg t,
      mul_nonneg (norm_nonneg t) (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))]

/-- **Shifted weighted mollifier integral bound (`integral_weighted_mollifier_sub_le`)**:
for `0 < σ ≤ 1` and any `t`,
`∫ x, (1 + ‖x‖) * ψ_σ(x - t) dx ≤ (1 + ‖t‖) * (1 + ∫ v, ‖v‖ * φ_C(v) dv)`. -/
public theorem integral_weighted_mollifier_sub_le (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t : EuclideanSpace ℝ (Fin n)) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume ≤
      (1 + ‖t‖) *
        (1 + ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hwψ := integrable_weighted_mollifier n C hC σ hσ
  have hwψ_meas :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) := by
    fun_prop
  have hshift :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) *
          mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))
      volume := by
    exact
      integrable_toLp_shift n (-(t : Fin n → ℝ))
        (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) hwψ hwψ_meas
  have hpt :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ≤
        (1 + ‖t‖) *
          ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) := by
    intro x
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (mollifier_nonneg n C hC σ hσ _)
    have hxt : WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) = x - t := rfl
    have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ + ‖t‖ := by
      rw [hxt]
      calc
        ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le (x - t) t
    have hexp :
      (1 + ‖t‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) =
        1 + ‖t‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ +
          ‖t‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ := by
      ring
    rw [hexp]
    linarith [htri, norm_nonneg t,
      mul_nonneg (norm_nonneg t) (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))]
  refine
    le_trans
      (MeasureTheory.integral_mono (integrable_weighted_mollifier_sub n C hC σ hσ t)
        (hshift.const_mul (1 + ‖t‖)) hpt)
      ?_
  rw [MeasureTheory.integral_const_mul (1 + ‖t‖),
    integral_shift_neg n (t : Fin n → ℝ)
      (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y)
      hwψ.aestronglyMeasurable,
    integral_weighted_mollifier n C hC σ hσ]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [norm_nonneg t])
  have hMnn :
    0 ≤ ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume :=
    MeasureTheory.integral_nonneg fun v =>
      mul_nonneg (norm_nonneg v) (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  linarith [mul_le_of_le_one_left hMnn hσ1]

/-- **Single combined shifted-mollifier modulus bound (`weighted_mollifier_shift_le`)**:
for `0 < σ ≤ 1` and any `t, x_k : EuclideanSpace ℝ (Fin n)`,
`∫ x, (1 + ‖x‖) * |ψ_σ(x - x_k) - ψ_σ(x - t)| dx
  ≤ (1 + ‖t‖) * weightedModulus n φ_C (σ⁻¹ • (x_k - t))`. -/
public theorem weighted_mollifier_shift_le (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (t x_k : EuclideanSpace ℝ (Fin n)) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume ≤
      (1 + ‖t‖) *
        weightedModulus n (multivariateGaussianPDF n 0 C hC)
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ)))) := by
  classical
  have hψmeas := measurable_mollifier n C hC σ hσ
  set s : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 ((x_k : Fin n → ℝ) - (t : Fin n → ℝ)) with
    hs_def
  -- Integrability of the LHS integrand by domination with `(1+‖x‖)ψ_σ(x-x_k) + (1+‖x‖)ψ_σ(x-t)`
  have hLHS_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|)
      volume := by
    refine
      MeasureTheory.Integrable.mono'
        ((integrable_weighted_mollifier_sub n C hC σ hσ x_k).add
          (integrable_weighted_mollifier_sub n C hC σ hσ t))
        ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) *
                |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|)).aestronglyMeasurable
    · filter_upwards with x
      simp only [Pi.add_apply]
      have hxnn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hxnn (abs_nonneg _))]
      have habs :
        |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ≤
          mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) +
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) := by
        refine le_trans (abs_sub _ _) ?_
        rw [abs_of_nonneg (mollifier_nonneg n C hC σ hσ _),
          abs_of_nonneg (mollifier_nonneg n C hC σ hσ _)]
      calc
        (1 + ‖x‖) *
              |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ≤
            (1 + ‖x‖) *
              (mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) +
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) :=
          mul_le_mul_of_nonneg_left habs hxnn
        _ =
            (1 + ‖x‖) *
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) +
              (1 + ‖x‖) *
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) :=
          by rw [mul_add]
  -- Integrability of `y ↦ (1 + ‖y‖) * |ψ_σ(y - s) - ψ_σ(y)|`
  have hY_int :
    MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖y‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ y|)
      volume := by
    refine
      MeasureTheory.Integrable.mono'
        ((integrable_weighted_mollifier_sub n C hC σ hσ s).add
          (integrable_weighted_mollifier n C hC σ hσ))
        ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun y : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖y‖) *
                |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
                    mollifier n C hC σ hσ y|)).aestronglyMeasurable
    · filter_upwards with y
      simp only [Pi.add_apply]
      have hynn : 0 ≤ (1 : ℝ) + ‖y‖ := by linarith [norm_nonneg y]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hynn (abs_nonneg _))]
      have habs :
        |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ y| ≤
          mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) +
            mollifier n C hC σ hσ y := by
        refine le_trans (abs_sub _ _) ?_
        rw [abs_of_nonneg (mollifier_nonneg n C hC σ hσ _),
          abs_of_nonneg (mollifier_nonneg n C hC σ hσ _)]
      calc
        (1 + ‖y‖) *
              |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
                  mollifier n C hC σ hσ y| ≤
            (1 + ‖y‖) *
              (mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) +
                mollifier n C hC σ hσ y) :=
          mul_le_mul_of_nonneg_left habs hynn
        _ =
            (1 + ‖y‖) * mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) +
              (1 + ‖y‖) * mollifier n C hC σ hσ y :=
          by rw [mul_add]
  have hY_meas :
    Measurable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖y‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ y|) := by
    fun_prop
  -- Shifted version of `hY_int` along `x ↦ x - t`
  have hY_shift :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) *
          |mollifier n C hC σ hσ
                (WithLp.toLp 2
                  (((WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
                      Fin n → ℝ) -
                    (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|)
      volume := by
    exact
      integrable_toLp_shift n (-(t : Fin n → ℝ))
        (fun y : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖y‖) *
            |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
                mollifier n C hC σ hσ y|)
        hY_int hY_meas
  -- Pointwise bound: `(1 + ‖x‖) * |ψ_σ(x - x_k) - ψ_σ(x - t)| ≤ (1 + ‖t‖) * shifted(x)`
  have hpt1 :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ))) -
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ≤
        (1 + ‖t‖) *
          ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) *
            |mollifier n C hC σ hσ
                  (WithLp.toLp 2
                    (((WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) :
                          EuclideanSpace ℝ (Fin n)) :
                        Fin n → ℝ) -
                      (s : Fin n → ℝ))) -
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|) := by
    intro x
    have harg :
      WithLp.toLp 2
          (((WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
              Fin n → ℝ) -
            (s : Fin n → ℝ)) =
        WithLp.toLp 2 ((x : Fin n → ℝ) - (x_k : Fin n → ℝ)) := by
      apply WithLp.ofLp_injective
      ext i
      show
        ((x : Fin n → ℝ) i - (t : Fin n → ℝ) i) - ((x_k : Fin n → ℝ) i - (t : Fin n → ℝ) i) =
          (x : Fin n → ℝ) i - (x_k : Fin n → ℝ) i
      ring
    rw [harg, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hxt : WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) = x - t := rfl
    have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ + ‖t‖ := by
      rw [hxt]
      calc
        ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le (x - t) t
    have hexp :
      (1 + ‖t‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) =
        1 + ‖t‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ +
          ‖t‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ := by
      ring
    rw [hexp]
    linarith [htri, norm_nonneg t,
      mul_nonneg (norm_nonneg t) (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))]
  refine le_trans (MeasureTheory.integral_mono hLHS_int (hY_shift.const_mul (1 + ‖t‖)) hpt1) ?_
  rw [MeasureTheory.integral_const_mul (1 + ‖t‖),
    integral_shift_neg n (t : Fin n → ℝ)
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖y‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ y|)
      hY_meas.aestronglyMeasurable]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [norm_nonneg t])
  -- Now prove `∫ y, (1 + ‖y‖) * |ψ_σ(y - s) - ψ_σ(y)| dy ≤ weightedModulus n φ_C (σ⁻¹ • s)`
  -- via linear change of variables `y = (σ • 1) v` (`integral_subst`).
  have hBdet : 0 < ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_pos hσ n
  have hsub :=
    integral_subst n 0 ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) hBdet
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖y‖) *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((y : Fin n → ℝ) - (s : Fin n → ℝ))) -
              mollifier n C hC σ hσ y|)
      hY_meas.aemeasurable
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, smul_eq_mul] at hsub
  simp only [zero_add] at hsub
  rw [hsub]
  -- Pull `(σ : ℝ) ^ n` inside the integral and cancel with `(σ : ℝ)⁻¹ ^ n` in `mollifier`
  rw [← MeasureTheory.integral_const_mul ((σ : ℝ) ^ n)]
  have hpt_scale :
    ∀ v : EuclideanSpace ℝ (Fin n),
      (σ : ℝ) ^ n *
          ((1 +
              ‖(Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                    ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                  v‖) *
            |mollifier n C hC σ hσ
                  (WithLp.toLp 2
                    (((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                            ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) v :
                          EuclideanSpace ℝ (Fin n)) :
                        Fin n → ℝ) -
                      (s : Fin n → ℝ))) -
                mollifier n C hC σ hσ
                  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                      ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                    v)|) ≤
        (1 + ‖v‖) *
          |multivariateGaussianPDF n 0 C hC
                (WithLp.toLp 2
                  ((v : Fin n → ℝ) -
                    ((WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ))) :
                        EuclideanSpace ℝ (Fin n)) :
                      Fin n → ℝ))) -
              multivariateGaussianPDF n 0 C hC v| := by
    intro v
    rw [toEuclideanLin_smul_one]
    have hnorm : ‖WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))‖ ≤ ‖v‖ := by
      rw [show (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) = (σ : ℝ) • v from rfl, norm_smul,
        Real.norm_eq_abs, abs_of_pos hσ]
      exact mul_le_of_le_one_left (norm_nonneg v) hσ1
    have h1 :
      WithLp.toLp 2
          ((σ : ℝ)⁻¹ •
            ((WithLp.toLp 2
                  (((WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
                      Fin n → ℝ) -
                    (s : Fin n → ℝ)) :
                EuclideanSpace ℝ (Fin n)) :
              Fin n → ℝ)) =
        WithLp.toLp 2
          ((v : Fin n → ℝ) -
            ((WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ))) :
                EuclideanSpace ℝ (Fin n)) :
              Fin n → ℝ)) := by
      apply WithLp.ofLp_injective
      ext i
      show
        (σ : ℝ)⁻¹ * (σ * (v : Fin n → ℝ) i - ((x_k : Fin n → ℝ) i - (t : Fin n → ℝ) i)) =
          (v : Fin n → ℝ) i - (σ : ℝ)⁻¹ * ((x_k : Fin n → ℝ) i - (t : Fin n → ℝ) i)
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hσ), one_mul]
    have h2 :
      WithLp.toLp 2
          ((σ : ℝ)⁻¹ •
            ((WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) =
        v := by
      apply WithLp.ofLp_injective
      ext i
      show (σ : ℝ)⁻¹ * (σ * (v : Fin n → ℝ) i) = (v : Fin n → ℝ) i
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hσ), one_mul]
    simp only [mollifier, h1, h2, ← mul_sub]
    rw [abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hσ) n)]
    have hcancel :
      (σ : ℝ) ^ n *
          ((1 + ‖WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))‖) *
            ((σ : ℝ)⁻¹ ^ n *
              |multivariateGaussianPDF n 0 C hC
                    (WithLp.toLp 2
                      ((v : Fin n → ℝ) -
                        ((WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ))) :
                            EuclideanSpace ℝ (Fin n)) :
                          Fin n → ℝ))) -
                  multivariateGaussianPDF n 0 C hC v|)) =
        ((σ : ℝ) ^ n * (σ : ℝ)⁻¹ ^ n) *
          ((1 + ‖WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))‖) *
            |multivariateGaussianPDF n 0 C hC
                  (WithLp.toLp 2
                    ((v : Fin n → ℝ) -
                      ((WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ))) :
                          EuclideanSpace ℝ (Fin n)) :
                        Fin n → ℝ))) -
                multivariateGaussianPDF n 0 C hC v|) := by
      ring
    rw [hcancel, inv_pow, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), one_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [hnorm]) (abs_nonneg _)
  -- Integrability of both sides of `hpt_scale`
  set u_scaled : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((x_k : Fin n → ℝ) - (t : Fin n → ℝ)))
  have hφ_pdf := isPdf_multivariateGaussianPDF n 0 C hC
  have hφ_meas := measurable_multivariateGaussianPDF n 0 C hC
  have hφ_mom := integrable_norm_mul_gaussianPDF_center n C hC
  have hRHS_int :
    MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖v‖) *
          |multivariateGaussianPDF n 0 C hC
                (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) -
              multivariateGaussianPDF n 0 C hC v|)
      volume := by
    have hwφ :
      MeasureTheory.Integrable
        (fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) * multivariateGaussianPDF n 0 C hC v)
        volume := by
      have heq :
        (fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) * multivariateGaussianPDF n 0 C hC v) =
          fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v + ‖v‖ * multivariateGaussianPDF n 0 C hC v := by
        funext v; ring
      rw [heq]
      exact (integrable_of_isPdf hφ_pdf).add hφ_mom
    have hwφ_meas :
      Measurable
        (fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) * multivariateGaussianPDF n 0 C hC v) := by
      fun_prop
    have hwφ_shift :
      MeasureTheory.Integrable
        (fun v : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖v‖) *
            multivariateGaussianPDF n 0 C hC
              (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))))
        volume := by
      have h1 :=
        integrable_toLp_shift n (-(u_scaled : Fin n → ℝ))
          (fun v : EuclideanSpace ℝ (Fin n) => (1 + ‖v‖) * multivariateGaussianPDF n 0 C hC v) hwφ
          hwφ_meas
      refine MeasureTheory.Integrable.mono' (h1.const_mul (1 + ‖u_scaled‖)) ?_ ?_
      · exact
          ((by fun_prop :
              Measurable fun v : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖v‖) *
                  multivariateGaussianPDF n 0 C hC
                    (WithLp.toLp 2
                      ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))))).aestronglyMeasurable
      · filter_upwards with v
        show
          ‖(1 + ‖v‖) *
                multivariateGaussianPDF n 0 C hC
                  (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ)))‖ ≤
            (1 + ‖u_scaled‖) *
              ((1 + ‖WithLp.toLp 2 ((v : Fin n → ℝ) + -(u_scaled : Fin n → ℝ))‖) *
                multivariateGaussianPDF n 0 C hC
                  (WithLp.toLp 2 ((v : Fin n → ℝ) + -(u_scaled : Fin n → ℝ))))
        have hsub' :
          WithLp.toLp 2 ((v : Fin n → ℝ) + -(u_scaled : Fin n → ℝ)) =
            WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ)) :=
          rfl
        rw [hsub', Real.norm_eq_abs,
          abs_of_nonneg
            (mul_nonneg (by linarith [norm_nonneg v])
              (le_of_lt (multivariateGaussianPDF_pos n 0 C hC _))),
          ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (multivariateGaussianPDF_pos n 0 C hC _))
        have hvu : WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ)) = v - u_scaled := rfl
        have htri :
          ‖v‖ ≤ ‖WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))‖ + ‖u_scaled‖ := by
          rw [hvu]
          calc
            ‖v‖ = ‖(v - u_scaled) + u_scaled‖ := by rw [sub_add_cancel]
            _ ≤ ‖v - u_scaled‖ + ‖u_scaled‖ := norm_add_le (v - u_scaled) u_scaled
        have hexp :
          (1 + ‖u_scaled‖) * (1 + ‖WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))‖) =
            1 + ‖u_scaled‖ + ‖WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))‖ +
              ‖u_scaled‖ * ‖WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))‖ := by
          ring
        rw [hexp]
        linarith [htri, norm_nonneg u_scaled,
          mul_nonneg (norm_nonneg u_scaled)
            (norm_nonneg (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))))]
    refine MeasureTheory.Integrable.mono' (hwφ_shift.add hwφ) ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun v : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖v‖) *
                |multivariateGaussianPDF n 0 C hC
                      (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) -
                    multivariateGaussianPDF n 0 C hC v|)).aestronglyMeasurable
    · filter_upwards with v
      simp only [Pi.add_apply]
      have hvnn : 0 ≤ (1 : ℝ) + ‖v‖ := by linarith [norm_nonneg v]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hvnn (abs_nonneg _))]
      have habs :
        |multivariateGaussianPDF n 0 C hC
                (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) -
              multivariateGaussianPDF n 0 C hC v| ≤
          multivariateGaussianPDF n 0 C hC
              (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) +
            multivariateGaussianPDF n 0 C hC v := by
        refine le_trans (abs_sub _ _) ?_
        rw [abs_of_pos (multivariateGaussianPDF_pos n 0 C hC _),
          abs_of_pos (multivariateGaussianPDF_pos n 0 C hC _)]
      calc
        (1 + ‖v‖) *
              |multivariateGaussianPDF n 0 C hC
                    (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) -
                  multivariateGaussianPDF n 0 C hC v| ≤
            (1 + ‖v‖) *
              (multivariateGaussianPDF n 0 C hC
                  (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) +
                multivariateGaussianPDF n 0 C hC v) :=
          mul_le_mul_of_nonneg_left habs hvnn
        _ =
            (1 + ‖v‖) *
                multivariateGaussianPDF n 0 C hC
                  (WithLp.toLp 2 ((v : Fin n → ℝ) - (u_scaled : Fin n → ℝ))) +
              (1 + ‖v‖) * multivariateGaussianPDF n 0 C hC v :=
          by rw [mul_add]
  have hLHS_v_int :
    MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin n) =>
        (σ : ℝ) ^ n *
          ((1 +
              ‖(Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                    ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                  v‖) *
            |mollifier n C hC σ hσ
                  (WithLp.toLp 2
                    (((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                            ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) v :
                          EuclideanSpace ℝ (Fin n)) :
                        Fin n → ℝ) -
                      (s : Fin n → ℝ))) -
                mollifier n C hC σ hσ
                  ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                      ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                    v)|))
      volume := by
    refine MeasureTheory.Integrable.mono' hRHS_int ?_ ?_
    · exact
        ((hY_meas.comp
                (by fun_prop :
                  Measurable
                    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                      ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))))).const_mul
            ((σ : ℝ) ^ n)).aestronglyMeasurable
    · filter_upwards with v
      have hTv_nn :
        0 ≤
          (1 : ℝ) +
            ‖(Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
                  ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
                v‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (le_of_lt (pow_pos hσ n)) (mul_nonneg hTv_nn (abs_nonneg _)))]
      exact hpt_scale v
  exact MeasureTheory.integral_mono hLHS_v_int hRHS_int hpt_scale

/-! ## Phase 2, Step 3b: `gmmApprox` definition, symmetric `gaussSmoothed`, and pointwise decomposition

We define the finite Gaussian mixture approximation `gmmApprox` (with a residual origin
component of weight `1 - ∑ W_k` so that its total mass is `1`), rewrite `gaussSmoothed`
in the symmetric convolution form `∫ t, f t * ψ_σ(x - t) dt`, and bound the pointwise
gap `|gmmApprox … x - gaussSmoothed … x|` by the sum of cell quantization integrals plus
the residual and outside-box tail terms. -/

/-- The finite Gaussian mixture approximation to a prior `f` on `coveredBox n δ N`, with
lattice cell weights `cellWeight f δ k` at centers `gridPoint δ k` (`k ∈ gridFinset n N`)
and a residual origin component of weight `1 - ∑ k ∈ gridFinset n N, cellWeight f δ k`. -/
@[expose]
public noncomputable def gmmApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (N : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
  (∑ k ∈ gridFinset n N,
      cellWeight f δ k *
        mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ)))) +
    (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x

/-- Bochner integral invariance under the reflection-translation `h ↦ toLp 2 (c - h)`. -/
public theorem integral_toLp_sub {n : ℕ} (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ h : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) ∂volume =
      ∫ h : EuclideanSpace ℝ (Fin n), g h ∂volume := by
  have hBdet :
    0 <
      ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det *
        ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, ← sq]
    exact sq_pos_of_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero))
  have h1 :=
    MeasureTheory.integral_neg_eq_self
      (fun z : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((z : Fin n → ℝ) + (c : Fin n → ℝ))))
      volume
  have h2 := integral_toLp_trans_right n c g hg
  refine
    (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)).trans (h1.trans h2)
  show
    g (WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) =
      g (WithLp.toLp 2 (((-h : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) + (c : Fin n → ℝ)))
  congr 1
  ext i
  show (c : Fin n → ℝ) i - (h : Fin n → ℝ) i = -(h : Fin n → ℝ) i + (c : Fin n → ℝ) i
  ring

/-- The symmetric convolution integrand `t ↦ f t * mollifier n C hC σ hσ (x - t)` is
integrable for every `x` whenever `f` is a measurable pdf. -/
public theorem integrable_prior_mul_mollifier_sub (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin n) =>
        f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))
      volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hψ0le := mollifier_le_zero n C hC σ hσ
  refine MeasureTheory.Integrable.mono' (hfi.mul_const (mollifier n C hC σ hσ 0)) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun t : EuclideanSpace ℝ (Fin n) =>
            f t *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpdf.1 t) (mollifier_nonneg n C hC σ hσ _))]
    exact mul_le_mul_of_nonneg_left (hψ0le _) (hpdf.1 t)

/-- **Symmetric convolution form of `gaussSmoothed` (`gaussSmoothed_symm`)**:
`gaussSmoothed n f C hC σ hσ x = ∫ t, f t * ψ_σ(x - t) dt`. -/
public theorem gaussSmoothed_symm (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfm : Measurable f)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussSmoothed n f C hC σ hσ x =
      ∫ t : EuclideanSpace ℝ (Fin n),
        f t *
          mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun t =>
    f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))
  have hg_meas : Measurable g := by
    dsimp only [g]
    fun_prop
  rw [← integral_toLp_sub (x : Fin n → ℝ) g hg_meas.aestronglyMeasurable]
  show
    (∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC σ hσ u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume) =
      ∫ u : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only [g]
  have hsub :
    WithLp.toLp 2
        ((x : Fin n → ℝ) -
          ((WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
            Fin n → ℝ)) =
      u := by
    apply WithLp.ofLp_injective
    ext i
    show (x : Fin n → ℝ) i - ((x : Fin n → ℝ) i - (u : Fin n → ℝ) i) = (u : Fin n → ℝ) i
    ring
  rw [hsub, mul_comm]

/-- For each cell `k`, `cellWeight f δ k * ψ_σ(x - x_k) - ∫_{cell δ k} f(t) ψ_σ(x - t) dt`
is bounded in absolute value by `∫_{cell δ k} f(t) |ψ_σ(x - x_k) - ψ_σ(x - t)| dt`. -/
public theorem abs_cellWeight_mul_sub_setIntegral_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (δ : ℝ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    |cellWeight f δ k *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
          ∫ t in cell δ k,
            f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume| ≤
      ∫ t in cell δ k,
        f t *
          |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have h1 :
    cellWeight f δ k *
        mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) =
      ∫ t in cell δ k,
        f t *
          mollifier n C hC σ hσ
            (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) ∂volume := by
    simp only [cellWeight, MeasureTheory.integral_mul_const]
  have hint1 :
    MeasureTheory.IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin n) =>
        f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))))
      (cell δ k) volume :=
    (hfi.mul_const _).integrableOn
  have hint2 :
    MeasureTheory.IntegrableOn
      (fun t : EuclideanSpace ℝ (Fin n) =>
        f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))
      (cell δ k) volume :=
    (integrable_prior_mul_mollifier_sub n f hfm hpdf C hC σ hσ x).integrableOn
  rw [h1, ← MeasureTheory.integral_sub hint1 hint2]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  refine le_of_eq (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
  show
    |f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
          f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| =
      f t *
        |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|
  rw [← mul_sub, abs_mul, abs_of_nonneg (hpdf.1 t)]

/-- **Pointwise decomposition bound (`gmmApprox_sub_gaussSmoothed_le`)**:
for every `x`, `|gmmApprox … x - gaussSmoothed … x|` is at most the finite sum over
`k ∈ gridFinset n N` of the cell quantization errors plus the residual origin term and
the outside-box tail integral. -/
public theorem gmmApprox_sub_gaussSmoothed_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x| ≤
      (∑ k ∈ gridFinset n N,
          ∫ t in cell δ k,
            f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) +
        (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x +
        ∫ t in (coveredBox n δ N)ᶜ,
          f t *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
  have hint := integrable_prior_mul_mollifier_sub n f hfm hpdf C hC σ hσ x
  have hgs_split :
    gaussSmoothed n f C hC σ hσ x =
      (∑ k ∈ gridFinset n N,
          ∫ t in cell δ k,
            f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) +
        ∫ t in (coveredBox n δ N)ᶜ,
          f t *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
    rw [gaussSmoothed_symm n f hfm C hC σ hσ x, ←
      MeasureTheory.integral_add_compl (measurableSet_coveredBox n δ N) hint, ←
      sum_setIntegral_cell hδ N _ hint]
  have hdiff_eq :
    gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x =
      (∑ k ∈ gridFinset n N,
            (cellWeight f δ k *
                mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
              ∫ t in cell δ k,
                f t *
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume)) +
          (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x -
        ∫ t in (coveredBox n δ N)ᶜ,
          f t *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
    rw [gmmApprox, hgs_split, Finset.sum_sub_distrib]
    ring
  rw [hdiff_eq]
  have hres_nn : 0 ≤ (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x :=
    mul_nonneg (sub_nonneg.mpr (sum_cellWeight_le_one hpdf hδ N)) (mollifier_nonneg n C hC σ hσ x)
  have htail_nn :
    0 ≤
      ∫ t in (coveredBox n δ N)ᶜ,
        f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume :=
    MeasureTheory.setIntegral_nonneg (measurableSet_coveredBox n δ N).compl
      (fun t _ => mul_nonneg (hpdf.1 t) (mollifier_nonneg n C hC σ hσ _))
  have htri1 :
    |(∑ k ∈ gridFinset n N,
              (cellWeight f δ k *
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                ∫ t in cell δ k,
                  f t *
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume)) +
            (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x -
          ∫ t in (coveredBox n δ N)ᶜ,
            f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume| ≤
      |∑ k ∈ gridFinset n N,
            (cellWeight f δ k *
                mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
              ∫ t in cell δ k,
                f t *
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume)| +
        (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x +
        ∫ t in (coveredBox n δ N)ᶜ,
          f t *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
    refine le_trans (abs_sub _ _) ?_
    rw [abs_of_nonneg htail_nn]
    refine add_le_add ?_ (le_refl _)
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_of_nonneg hres_nn]
  refine le_trans htri1 ?_
  refine add_le_add (add_le_add ?_ (le_refl _)) (le_refl _)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact
    Finset.sum_le_sum fun k _ => abs_cellWeight_mul_sub_setIntegral_le n f hfm hpdf C hC σ hσ δ k x

/-! ## Phase 2, Step 3c: cell-by-cell & tail Tonelli assembly (`gmmApprox_quantization_of_modulus_bound`)

We integrate the pointwise decomposition of Step 3b against `(1 + ‖x‖)` over `x`.
Because the finite sum over `k ∈ gridFinset n N` is kept on the outside, each cell's
`(x, t)`-integrand is dominated by a separable product `f(t) * ((1 + ‖x‖) * ψ_σ(x - x_k))`
(`MeasureTheory.Integrable.prod_mul`) plus the symmetric convolution dominator
`f(t) * ((1 + ‖x‖) * ψ_σ(x - t))`. Thus `latticeQ` (`Q_δ`) never enters any
product-measure integrability proof! -/

/-- Any separable product `(x, y) ↦ g x * h y` of integrable functions on `EuclideanSpace ℝ (Fin n)`
is integrable on `volume.prod volume`. -/
public theorem integrable_prod_mul_volume (n : ℕ) {g h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : MeasureTheory.Integrable g volume) (hh : MeasureTheory.Integrable h volume) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => g p.1 * h p.2)
      (volume.prod volume) := by
  refine
    ⟨(hg.1.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_fst).mul
        (hh.1.comp_quasiMeasurePreserving MeasureTheory.Measure.quasiMeasurePreserving_snd),
      ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_prod_le _) ?_
  have hpt :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖g x * h y‖ₑ ∂volume =
        ‖g x‖ₑ * ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖h y‖ₑ ∂volume :=
    fun x => by
    have heq :
      (fun y : EuclideanSpace ℝ (Fin n) => ‖g x * h y‖ₑ) = fun y : EuclideanSpace ℝ (Fin n) =>
        ‖g x‖ₑ * ‖h y‖ₑ := by
      funext y; exact enorm_mul (g x) (h y)
    rw [heq, MeasureTheory.lintegral_const_mul' (‖g x‖ₑ) _ ENNReal.coe_ne_top]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.lintegral_mul_const' _ _ (ne_of_lt hh.2)]
  exact ENNReal.mul_lt_top hg.2 hh.2

/-- Joint integrability of `(x, t) ↦ (1 + ‖x‖) * (f t * ψ_σ(x - t))` on `volume.prod volume`. -/
public theorem integrable_joint_symm_prior (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.1‖) *
          (f p.2 * mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))))
      (volume.prod volume) := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hwψ := integrable_weighted_mollifier n C hC σ hσ
  have hwψ_meas :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) := by
    fun_prop
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) volume := by
    have heq :
      (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) = fun t : EuclideanSpace ℝ (Fin n) =>
        f t + ‖t‖ * f t := by
      funext t; ring
    rw [heq]; exact hfi.add hfmom
  have hΦmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.1‖) *
          (f p.2 *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))) := by
    fun_prop
  have hswap_meas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        f p.1 *
          ((1 + ‖p.2‖) *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))) := by
    fun_prop
  have hswap_int :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        f p.1 *
          ((1 + ‖p.2‖) *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
      (volume.prod volume) := by
    have hKnn :
      ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        0 ≤
          f p.1 *
            ((1 + ‖p.2‖) *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) :=
      fun p =>
      mul_nonneg (hpdf.1 p.1)
        (mul_nonneg (by linarith [norm_nonneg p.2]) (mollifier_nonneg n C hC σ hσ _))
    refine ⟨hswap_meas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hKnn),
      MeasureTheory.lintegral_prod _ (Measurable.ennreal_ofReal hswap_meas).aemeasurable]
    have hinner :
      ∀ t : EuclideanSpace ℝ (Fin n),
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal
              (f t *
                ((1 + ‖x‖) *
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))) ∂volume ≤
          ENNReal.ofReal
              (1 +
                σ *
                  ∫ v : EuclideanSpace ℝ (Fin n),
                    ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) *
            ENNReal.ofReal ((1 + ‖t‖) * f t) := by
      intro t
      have hpt :
        ∀ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal
              (f t *
                ((1 + ‖x‖) *
                  mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))) =
            ENNReal.ofReal (f t) *
              ENNReal.ofReal
                ((1 + ‖x‖) *
                  mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) :=
        fun x => ENNReal.ofReal_mul (hpdf.1 t)
      have hx_meas :
        Measurable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal
              ((1 + ‖x‖) *
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))) :=
        Measurable.ennreal_ofReal (by fun_prop)
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
        MeasureTheory.lintegral_const_mul _ hx_meas, ←
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (integrable_weighted_mollifier_sub n C hC σ hσ t)
          (Filter.Eventually.of_forall fun x =>
            mul_nonneg (by linarith [norm_nonneg x]) (mollifier_nonneg n C hC σ hσ _))]
      -- Bound `∫ x, (1 + ‖x‖) * ψ_σ(x - t) dx ≤ (1 + ‖t‖) * (1 + σ * M_φ)` for general `σ > 0`
      have hshift_t :
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))
          volume :=
        integrable_toLp_shift n (-(t : Fin n → ℝ))
          (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y) hwψ hwψ_meas
      have hle_t :
        ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume ≤
          (1 + ‖t‖) *
            (1 +
              σ *
                ∫ v : EuclideanSpace ℝ (Fin n),
                  ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
        refine
          le_trans
            (MeasureTheory.integral_mono (integrable_weighted_mollifier_sub n C hC σ hσ t)
              (hshift_t.const_mul (1 + ‖t‖)) (fun x => ?_))
            ?_
        · rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (mollifier_nonneg n C hC σ hσ _)
          have hxt : WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)) = x - t := rfl
          have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ + ‖t‖ := by
            rw [hxt]
            calc
              ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
              _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le (x - t) t
          have hexp :
            (1 + ‖t‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖) =
              1 + ‖t‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ +
                ‖t‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))‖ := by
            ring
          rw [hexp]
          linarith [htri, norm_nonneg t,
            mul_nonneg (norm_nonneg t)
              (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))]
        · rw [MeasureTheory.integral_const_mul (1 + ‖t‖),
            integral_shift_neg n (t : Fin n → ℝ)
              (fun y : EuclideanSpace ℝ (Fin n) => (1 + ‖y‖) * mollifier n C hC σ hσ y)
              hwψ.aestronglyMeasurable,
            integral_weighted_mollifier n C hC σ hσ]
      have h1 := ENNReal.ofReal_le_ofReal hle_t
      rw [ENNReal.ofReal_mul (by linarith [norm_nonneg t])] at h1
      calc
        ENNReal.ofReal (f t) *
              ENNReal.ofReal
                (∫ x : EuclideanSpace ℝ (Fin n),
                  (1 + ‖x‖) *
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ≤
            ENNReal.ofReal (f t) *
              (ENNReal.ofReal (1 + ‖t‖) *
                ENNReal.ofReal
                  (1 +
                    σ *
                      ∫ v : EuclideanSpace ℝ (Fin n),
                        ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume)) :=
          mul_le_mul_of_nonneg_left h1 zero_le
        _ =
            ENNReal.ofReal
                (1 +
                  σ *
                    ∫ v : EuclideanSpace ℝ (Fin n),
                      ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) *
              (ENNReal.ofReal (1 + ‖t‖) * ENNReal.ofReal (f t)) :=
          by ring
        _ =
            ENNReal.ofReal
                (1 +
                  σ *
                    ∫ v : EuclideanSpace ℝ (Fin n),
                      ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) *
              ENNReal.ofReal ((1 + ‖t‖) * f t) :=
          by rw [ENNReal.ofReal_mul (by linarith [norm_nonneg t])]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner) ?_
    have hwf_meas :
      Measurable (fun t : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal ((1 + ‖t‖) * f t)) :=
      Measurable.ennreal_ofReal (by fun_prop)
    rw [MeasureTheory.lintegral_const_mul _ hwf_meas, ←
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwf
        (Filter.Eventually.of_forall fun t => mul_nonneg (by linarith [norm_nonneg t]) (hpdf.1 t))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hswapmp :
    MeasureTheory.MeasurePreserving
      (Prod.swap :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap
  refine
    ((hswapmp.integrable_comp hswap_meas.aestronglyMeasurable).mpr hswap_int).congr
      (Filter.Eventually.of_forall fun p => ?_)
  show
    f p.2 *
        ((1 + ‖p.1‖) *
          mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) =
      (1 + ‖p.1‖) *
        (f p.2 * mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))
  ring

/-- For any measurable set `s` (such as `cell δ k` or `(coveredBox n δ N)ᶜ`), the
indicator-restricted symmetric convolution integrand
`(x, t) ↦ (1 + ‖x‖) * (s.indicator f t * ψ_σ(x - t))` is integrable on `volume.prod volume`. -/
public theorem integrable_joint_indicator_symm_prior (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.1‖) *
          (s.indicator f p.2 *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))))
      (volume.prod volume) := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hsf_meas : Measurable (s.indicator f) := hfm.indicator hs
  refine
    MeasureTheory.Integrable.mono' (integrable_joint_symm_prior n f hfm hpdf hfmom C hC σ hσ) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1 + ‖p.1‖) *
              (s.indicator f p.2 *
                mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))))).aestronglyMeasurable
  · filter_upwards with p
    have hsf_nn : 0 ≤ s.indicator f p.2 := Set.indicator_nonneg (fun t _ => hpdf.1 t) p.2
    have hsf_le : s.indicator f p.2 ≤ f p.2 := Set.indicator_le_self' (fun t _ => hpdf.1 t) p.2
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (mul_nonneg (by linarith [norm_nonneg p.1])
          (mul_nonneg hsf_nn (mollifier_nonneg n C hC σ hσ _)))]
    exact
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsf_le (mollifier_nonneg n C hC σ hσ _))
        (by linarith [norm_nonneg p.1])

/-- For each cell `k`, the joint quantization-error integrand
`(x, t) ↦ (1 + ‖x‖) * ((cell δ k).indicator f t * |ψ_σ(x - x_k) - ψ_σ(x - t)|)`
is integrable on `volume.prod volume` (dominated by the separable product
`((1 + ‖x‖) * ψ_σ(x - x_k)) * (cell δ k).indicator f t` plus `integrable_joint_symm_prior`). -/
public theorem integrable_joint_cell_error (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (k : Fin n → ℤ) :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1 + ‖p.1‖) *
          ((cell δ k).indicator f p.2 *
            |mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))|))
      (volume.prod volume) := by
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hcf_meas : Measurable ((cell δ k).indicator f) := hfm.indicator (measurableSet_cell δ k)
  have hsep :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ((1 + ‖p.1‖) *
            mollifier n C hC σ hσ
              (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ)))) *
          (cell δ k).indicator f p.2)
      (volume.prod volume) :=
    integrable_prod_mul_volume n (integrable_weighted_mollifier_sub n C hC σ hσ (gridPoint δ k))
      (hfi.indicator (measurableSet_cell δ k))
  have hsymm :=
    integrable_joint_indicator_symm_prior n f hfm hpdf hfmom C hC σ hσ (measurableSet_cell δ k)
  refine MeasureTheory.Integrable.mono' (hsep.add hsymm) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1 + ‖p.1‖) *
              ((cell δ k).indicator f p.2 *
                |mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2
                        ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))|))).aestronglyMeasurable
  · filter_upwards with p
    simp only [Pi.add_apply]
    have hcf_nn : 0 ≤ (cell δ k).indicator f p.2 := Set.indicator_nonneg (fun t _ => hpdf.1 t) p.2
    have hx_nn : 0 ≤ (1 : ℝ) + ‖p.1‖ := by linarith [norm_nonneg p.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx_nn (mul_nonneg hcf_nn (abs_nonneg _)))]
    have habs :
      |mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
            mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))| ≤
        mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) +
          mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_nonneg (mollifier_nonneg n C hC σ hσ _),
        abs_of_nonneg (mollifier_nonneg n C hC σ hσ _)]
    calc
      (1 + ‖p.1‖) *
            ((cell δ k).indicator f p.2 *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))|) ≤
          (1 + ‖p.1‖) *
            ((cell δ k).indicator f p.2 *
              (mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) +
                mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hcf_nn) hx_nn
      _ =
          ((1 + ‖p.1‖) *
                mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ)))) *
              (cell δ k).indicator f p.2 +
            (1 + ‖p.1‖) *
              ((cell δ k).indicator f p.2 *
                mollifier n C hC σ hσ (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) :=
        by ring

/-- Cell-level Fubini bound: for each `k`, if `weightedModulus n φ_C u ≤ η` whenever
`‖u‖ ≤ δ * √n / σ`, then
`∫ x, (1 + ‖x‖) * ∫ t in cell δ k, f t * |ψ_σ(x - x_k) - ψ_σ(x - t)| dt dx
  ≤ η * ∫ t in cell δ k, (1 + ‖t‖) * f t dt`. -/
public theorem integral_weighted_cell_error_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) {δ : ℝ}
    (hδ : 0 < δ) (k : Fin n → ℤ) {η : ℝ} (_hη : 0 ≤ η)
    (hmod :
      ∀ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ ≤ δ * Real.sqrt (n : ℝ) / σ →
          weightedModulus n (multivariateGaussianPDF n 0 C hC) u ≤ η) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          (∫ t in cell δ k,
            f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ∂volume ≤
      η * ∫ t in cell δ k, (1 + ‖t‖) * f t ∂volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) volume := by
    have heq :
      (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) = fun t : EuclideanSpace ℝ (Fin n) =>
        f t + ‖t‖ * f t := by
      funext t; ring
    rw [heq]; exact hfi.add hfmom
  have hjoint := integrable_joint_cell_error n f hfm hpdf hfmom C hC σ hσ δ k
  -- Rewrite the inner set integral as a full-space indicator integral and pull `(1 + ‖x‖)` inside
  have hrewrite :
    (∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          (∫ t in cell δ k,
            f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ∂volume) =
      ∫ x : EuclideanSpace ℝ (Fin n),
        ∫ t : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((cell δ k).indicator f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|) ∂volume ∂volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only []
    rw [← MeasureTheory.integral_indicator (measurableSet_cell δ k), ←
      MeasureTheory.integral_const_mul (1 + ‖x‖)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ cell δ k
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [hrewrite, MeasureTheory.integral_integral_swap hjoint]
  -- Now the outer integral is over `t` and the inner integral is over `x`
  have hinner_eq :
    ∀ t : EuclideanSpace ℝ (Fin n),
      (∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((cell δ k).indicator f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|) ∂volume) =
        (cell δ k).indicator f t *
          ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume := by
    intro t
    have hmul :
      (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) *
            ((cell δ k).indicator f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|)) =
        fun x : EuclideanSpace ℝ (Fin n) =>
        (cell δ k).indicator f t *
          ((1 + ‖x‖) *
            |mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|) := by
      funext x; ring
    rw [hmul, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner_eq)]
  -- Bound the `t`-integrand pointwise by `(cell δ k).indicator (fun t => η * ((1 + ‖t‖) * f t)) t`
  have hpt_t :
    ∀ t : EuclideanSpace ℝ (Fin n),
      (cell δ k).indicator f t *
          (∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ≤
        (cell δ k).indicator (fun t => η * ((1 + ‖t‖) * f t)) t := by
    intro t
    by_cases ht : t ∈ cell δ k
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      have hshift_le := weighted_mollifier_shift_le n C hC σ hσ hσ1 t (gridPoint δ k)
      have hu_norm :
        ‖(WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((gridPoint δ k : Fin n → ℝ) - (t : Fin n → ℝ))) :
              EuclideanSpace ℝ (Fin n))‖ ≤
          δ * Real.sqrt (n : ℝ) / σ := by
        have h1 :
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • ((gridPoint δ k : Fin n → ℝ) - (t : Fin n → ℝ))) :
              EuclideanSpace ℝ (Fin n)) =
            (σ : ℝ)⁻¹ • (gridPoint δ k - t) :=
          rfl
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ), div_eq_inv_mul]
        exact
          mul_le_mul_of_nonneg_left (norm_gridPoint_sub_le_of_mem_cell hδ ht)
            (le_of_lt (inv_pos.mpr hσ))
      have hmod_le := hmod _ hu_norm
      have hcomb :
        ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume ≤
          (1 + ‖t‖) * η :=
        le_trans hshift_le (mul_le_mul_of_nonneg_left hmod_le (by linarith [norm_nonneg t]))
      calc
        f t *
              (∫ x : EuclideanSpace ℝ (Fin n),
                (1 + ‖x‖) *
                  |mollifier n C hC σ hσ
                        (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                      mollifier n C hC σ hσ
                        (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ≤
            f t * ((1 + ‖t‖) * η) :=
          mul_le_mul_of_nonneg_left hcomb (hpdf.1 t)
        _ = η * ((1 + ‖t‖) * f t) := by ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  have hLHS_t_int :
    MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin n) =>
        (cell δ k).indicator f t *
          ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume)
      volume := by
    exact hjoint.integral_prod_right.congr (Filter.Eventually.of_forall hinner_eq)
  have hRHS_t_int :
    MeasureTheory.Integrable
      ((cell δ k).indicator (fun t : EuclideanSpace ℝ (Fin n) => η * ((1 + ‖t‖) * f t))) volume :=
    (hwf.const_mul η).indicator (measurableSet_cell δ k)
  refine le_trans (MeasureTheory.integral_mono hLHS_t_int hRHS_t_int hpt_t) ?_
  rw [MeasureTheory.integral_indicator (measurableSet_cell δ k), MeasureTheory.integral_const_mul η]

/-- Tail Fubini bound: for `0 < σ ≤ 1`,
`∫ x, (1 + ‖x‖) * ∫ t in (coveredBox n δ N)ᶜ, f t * ψ_σ(x - t) dt dx
  ≤ (1 + M_φ) * ∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t dt`. -/
public theorem integral_weighted_compl_coveredBox_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (δ : ℝ)
    (N : ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          (∫ t in (coveredBox n δ N)ᶜ,
            f t *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ∂volume ≤
      (1 + ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) *
        ∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t ∂volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) volume := by
    have heq :
      (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) = fun t : EuclideanSpace ℝ (Fin n) =>
        f t + ‖t‖ * f t := by
      funext t; ring
    rw [heq]; exact hfi.add hfmom
  have hcompl_meas : MeasurableSet (coveredBox n δ N)ᶜ := (measurableSet_coveredBox n δ N).compl
  have hjoint := integrable_joint_indicator_symm_prior n f hfm hpdf hfmom C hC σ hσ hcompl_meas
  have hrewrite :
    (∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          (∫ t in (coveredBox n δ N)ᶜ,
            f t *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ∂volume) =
      ∫ x : EuclideanSpace ℝ (Fin n),
        ∫ t : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((coveredBox n δ N)ᶜ.indicator f t *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) ∂volume ∂volume := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only []
    rw [← MeasureTheory.integral_indicator hcompl_meas, ←
      MeasureTheory.integral_const_mul (1 + ‖x‖)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ (coveredBox n δ N)ᶜ
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [hrewrite, MeasureTheory.integral_integral_swap hjoint]
  have hinner_eq :
    ∀ t : EuclideanSpace ℝ (Fin n),
      (∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((coveredBox n δ N)ᶜ.indicator f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) ∂volume) =
        (coveredBox n δ N)ᶜ.indicator f t *
          ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume := by
    intro t
    have hmul :
      (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) *
            ((coveredBox n δ N)ᶜ.indicator f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))))) =
        fun x : EuclideanSpace ℝ (Fin n) =>
        (coveredBox n δ N)ᶜ.indicator f t *
          ((1 + ‖x‖) *
            mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) := by
      funext x; ring
    rw [hmul, MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner_eq)]
  set M_φ : ℝ := ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume
  have hpt_t :
    ∀ t : EuclideanSpace ℝ (Fin n),
      (coveredBox n δ N)ᶜ.indicator f t *
          (∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ≤
        (coveredBox n δ N)ᶜ.indicator (fun t => (1 + M_φ) * ((1 + ‖t‖) * f t)) t := by
    intro t
    by_cases ht : t ∈ (coveredBox n δ N)ᶜ
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      have hle := integral_weighted_mollifier_sub_le n C hC σ hσ hσ1 t
      calc
        f t *
              (∫ x : EuclideanSpace ℝ (Fin n),
                (1 + ‖x‖) *
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ≤
            f t * ((1 + ‖t‖) * (1 + M_φ)) :=
          mul_le_mul_of_nonneg_left hle (hpdf.1 t)
        _ = (1 + M_φ) * ((1 + ‖t‖) * f t) := by ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  have hLHS_t_int :
    MeasureTheory.Integrable
      (fun t : EuclideanSpace ℝ (Fin n) =>
        (coveredBox n δ N)ᶜ.indicator f t *
          ∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume)
      volume :=
    hjoint.integral_prod_right.congr (Filter.Eventually.of_forall hinner_eq)
  have hRHS_t_int :
    MeasureTheory.Integrable
      ((coveredBox n δ N)ᶜ.indicator
        (fun t : EuclideanSpace ℝ (Fin n) => (1 + M_φ) * ((1 + ‖t‖) * f t)))
      volume :=
    (hwf.const_mul (1 + M_φ)).indicator hcompl_meas
  refine le_trans (MeasureTheory.integral_mono hLHS_t_int hRHS_t_int hpt_t) ?_
  rw [MeasureTheory.integral_indicator hcompl_meas, MeasureTheory.integral_const_mul (1 + M_φ)]

/-- **Phase 2, Step 3 (`gmmApprox_quantization_of_modulus_bound`)**:
Given `0 ≤ η`, if `weightedModulus n φ_C u ≤ η` whenever `‖u‖ ≤ δ * √n / σ`, and
`0 < σ ≤ 1`, `0 < δ`, `R < N * δ`, then
`∫ x, (1 + ‖x‖) * |gmmApprox … x - gaussSmoothed … x| dx
  ≤ η * (1 + ∫ t, ‖t‖ * f t dt) + 2 * (1 + M_φ) * ∫ t in {y | R < ‖y‖}, (1 + ‖t‖) * f t dt`. -/
public theorem gmmApprox_quantization_of_modulus_bound (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) {δ R : ℝ}
    (hδ : 0 < δ) {N : ℕ} (hRN : R < (N : ℝ) * δ) {η : ℝ} (hη : 0 ≤ η)
    (hmod :
      ∀ u : EuclideanSpace ℝ (Fin n),
        ‖u‖ ≤ δ * Real.sqrt (n : ℝ) / σ →
          weightedModulus n (multivariateGaussianPDF n 0 C hC) u ≤ η) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x| ∂volume ≤
      η * (1 + ∫ t : EuclideanSpace ℝ (Fin n), ‖t‖ * f t ∂volume) +
        2 * (1 + ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) *
          ∫ t in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, (1 + ‖t‖) * f t ∂volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) volume := by
    have heq :
      (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) = fun t : EuclideanSpace ℝ (Fin n) =>
        f t + ‖t‖ * f t := by
      funext t; ring
    rw [heq]; exact hfi.add hfmom
  -- Integrability of each piece of the Step 3b RHS multiplied by `(1 + ‖x‖)`
  have hcell_x_int :
    ∀ k : Fin n → ℤ,
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) *
            (∫ t in cell δ k,
              f t *
                |mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume))
        volume := by
    intro k
    have hjoint := integrable_joint_cell_error n f hfm hpdf hfmom C hC σ hσ δ k
    refine hjoint.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
    show
      (∫ t : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((cell δ k).indicator f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))|) ∂volume) =
        (1 + ‖x‖) *
          (∫ t in cell δ k,
            f t *
              |mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                  mollifier n C hC σ hσ
                    (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume)
    rw [MeasureTheory.integral_const_mul (1 + ‖x‖), ←
      MeasureTheory.integral_indicator (measurableSet_cell δ k)]
    refine
      congrArg ((1 + ‖x‖) * ·)
        (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
    by_cases ht : t ∈ cell δ k
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  have hsum_x_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ k ∈ gridFinset n N,
          (1 + ‖x‖) *
            (∫ t in cell δ k,
              f t *
                |mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume))
      volume :=
    MeasureTheory.integrable_finsetSum (gridFinset n N) (fun k _ => hcell_x_int k)
  have hres_x_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * ((1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x))
      volume := by
    have heq :
      (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * ((1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x)) =
        fun x : EuclideanSpace ℝ (Fin n) =>
        (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * ((1 + ‖x‖) * mollifier n C hC σ hσ x) := by
      funext x; ring
    rw [heq]
    exact (integrable_weighted_mollifier n C hC σ hσ).const_mul _
  have htail_x_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) *
          (∫ t in (coveredBox n δ N)ᶜ,
            f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume))
      volume := by
    have hcompl_meas : MeasurableSet (coveredBox n δ N)ᶜ := (measurableSet_coveredBox n δ N).compl
    have hjoint := integrable_joint_indicator_symm_prior n f hfm hpdf hfmom C hC σ hσ hcompl_meas
    refine hjoint.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
    show
      (∫ t : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            ((coveredBox n δ N)ᶜ.indicator f t *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))) ∂volume) =
        (1 + ‖x‖) *
          (∫ t in (coveredBox n δ N)ᶜ,
            f t * mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume)
    rw [MeasureTheory.integral_const_mul (1 + ‖x‖), ← MeasureTheory.integral_indicator hcompl_meas]
    refine
      congrArg ((1 + ‖x‖) * ·)
        (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_))
    by_cases ht : t ∈ (coveredBox n δ N)ᶜ
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  -- Pointwise bound on `(1 + ‖x‖) * |gmmApprox x - gaussSmoothed x|`
  have hpt_x :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x| ≤
        ((∑ k ∈ gridFinset n N,
              (1 + ‖x‖) *
                (∫ t in cell δ k,
                  f t *
                    |mollifier n C hC σ hσ
                          (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                        mollifier n C hC σ hσ
                          (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume)) +
            (1 + ‖x‖) * ((1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x)) +
          (1 + ‖x‖) *
            (∫ t in (coveredBox n δ N)ᶜ,
              f t *
                mollifier n C hC σ hσ
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) := by
    intro x
    have hstep :=
      mul_le_mul_of_nonneg_left (gmmApprox_sub_gaussSmoothed_le n f hfm hpdf C hC σ hσ hδ N x)
        (by linarith [norm_nonneg x] : 0 ≤ (1 : ℝ) + ‖x‖)
    refine le_trans hstep (le_of_eq ?_)
    rw [mul_add, mul_add, Finset.mul_sum]
  -- Integrability of LHS `(1 + ‖x‖) * |gmmApprox x - gaussSmoothed x|`
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hgmm_meas : Measurable (gmmApprox n f C hC σ hσ δ N) := by
    unfold gmmApprox
    fun_prop
  have hgs_meas : Measurable (gaussSmoothed n f C hC σ hσ) :=
    measurable_gaussSmoothed n f hfm C hC σ hσ
  have hLHS_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x|)
      volume := by
    refine MeasureTheory.Integrable.mono' ((hsum_x_int.add hres_x_int).add htail_x_int) ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) *
                |gmmApprox n f C hC σ hσ δ N x -
                    gaussSmoothed n f C hC σ hσ x|)).aestronglyMeasurable
    · filter_upwards with x
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))]
      exact hpt_x x
  refine
    le_trans
      (MeasureTheory.integral_mono hLHS_int ((hsum_x_int.add hres_x_int).add htail_x_int) hpt_x) ?_
  rw [MeasureTheory.integral_add' (hsum_x_int.add hres_x_int) htail_x_int,
    MeasureTheory.integral_add' hsum_x_int hres_x_int,
    MeasureTheory.integral_finsetSum (gridFinset n N) (fun k _ => hcell_x_int k)]
  -- 1. Bound the sum over cells `k ∈ gridFinset n N`
  have hsum_cells_le :
    (∑ k ∈ gridFinset n N,
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) *
            (∫ t in cell δ k,
              f t *
                |mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                    mollifier n C hC σ hσ
                      (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ∂volume) ≤
      η * (1 + ∫ t : EuclideanSpace ℝ (Fin n), ‖t‖ * f t ∂volume) := by
    calc
      (∑ k ∈ gridFinset n N,
            ∫ x : EuclideanSpace ℝ (Fin n),
              (1 + ‖x‖) *
                (∫ t in cell δ k,
                  f t *
                    |mollifier n C hC σ hσ
                          (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) -
                        mollifier n C hC σ hσ
                          (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ)))| ∂volume) ∂volume) ≤
          ∑ k ∈ gridFinset n N, η * ∫ t in cell δ k, (1 + ‖t‖) * f t ∂volume :=
        Finset.sum_le_sum fun k _ =>
          integral_weighted_cell_error_le n f hfm hpdf hfmom C hC σ hσ hσ1 hδ k hη hmod
      _ = η * ∑ k ∈ gridFinset n N, ∫ t in cell δ k, (1 + ‖t‖) * f t ∂volume := by
        rw [← Finset.mul_sum]
      _ = η * ∫ t in coveredBox n δ N, (1 + ‖t‖) * f t ∂volume := by
        rw [sum_setIntegral_cell hδ N _ hwf]
      _ ≤ η * ∫ t : EuclideanSpace ℝ (Fin n), (1 + ‖t‖) * f t ∂volume := by
        refine mul_le_mul_of_nonneg_left ?_ hη
        exact
          MeasureTheory.setIntegral_le_integral hwf
            (Filter.Eventually.of_forall fun t =>
              mul_nonneg (by linarith [norm_nonneg t]) (hpdf.1 t))
      _ = η * (1 + ∫ t : EuclideanSpace ℝ (Fin n), ‖t‖ * f t ∂volume) := by
        congr 1
        have heq :
          (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) =
            fun t : EuclideanSpace ℝ (Fin n) => f t + ‖t‖ * f t := by
          funext t; ring
        rw [heq, MeasureTheory.integral_add hfi hfmom, hpdf.2]
  -- 2. Bound the residual origin term
  set M_φ : ℝ := ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume
  have hMφ_nn : 0 ≤ M_φ :=
    MeasureTheory.integral_nonneg fun v =>
      mul_nonneg (norm_nonneg v) (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  have hcompl_sub_tail :
    ∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t ∂volume ≤
      ∫ t in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, (1 + ‖t‖) * f t ∂volume := by
    exact
      MeasureTheory.setIntegral_mono_set hwf.integrableOn
        (Filter.Eventually.of_forall fun t => mul_nonneg (by linarith [norm_nonneg t]) (hpdf.1 t))
        (Filter.Eventually.of_forall (compl_coveredBox_subset_norm_gt hδ hRN))
  have hres_le :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          ((1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x) ∂volume ≤
      (1 + M_φ) * ∫ t in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, (1 + ‖t‖) * f t ∂volume := by
    have heq :
      (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * ((1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x)) =
        fun x : EuclideanSpace ℝ (Fin n) =>
        (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * ((1 + ‖x‖) * mollifier n C hC σ hσ x) := by
      funext x; ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (funext_iff.mp heq)),
      MeasureTheory.integral_const_mul, integral_weighted_mollifier n C hC σ hσ,
      one_sub_sum_cellWeight_eq hpdf hδ N]
    have h1 :
      (∫ t in (coveredBox n δ N)ᶜ, f t ∂volume) ≤
        ∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t ∂volume := by
      refine MeasureTheory.setIntegral_mono hfi.integrableOn hwf.integrableOn fun t => ?_
      have hft : 0 ≤ ‖t‖ * f t := mul_nonneg (norm_nonneg t) (hpdf.1 t)
      linarith
    have h2 : 1 + σ * M_φ ≤ 1 + M_φ := by linarith [mul_le_of_le_one_left hMφ_nn hσ1]
    have h1_nn : 0 ≤ ∫ t in (coveredBox n δ N)ᶜ, f t ∂volume :=
      MeasureTheory.setIntegral_nonneg (measurableSet_coveredBox n δ N).compl (fun t _ => hpdf.1 t)
    have hσM_nn : 0 ≤ 1 + σ * M_φ := by
      have : 0 ≤ σ * M_φ := mul_nonneg (le_of_lt hσ) hMφ_nn
      linarith
    calc
      (∫ t in (coveredBox n δ N)ᶜ, f t ∂volume) * (1 + σ * M_φ) ≤
          (∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t ∂volume) * (1 + M_φ) :=
        mul_le_mul h1 h2 hσM_nn
          (MeasureTheory.setIntegral_nonneg (measurableSet_coveredBox n δ N).compl
            (fun t _ => mul_nonneg (by linarith [norm_nonneg t]) (hpdf.1 t)))
      _ = (1 + M_φ) * ∫ t in (coveredBox n δ N)ᶜ, (1 + ‖t‖) * f t ∂volume := mul_comm _ _
      _ ≤ (1 + M_φ) * ∫ t in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, (1 + ‖t‖) * f t ∂volume :=
        mul_le_mul_of_nonneg_left hcompl_sub_tail (by linarith)
  -- 3. Bound the complement tail integral
  have htail_le :
    ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          (∫ t in (coveredBox n δ N)ᶜ,
            f t *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (t : Fin n → ℝ))) ∂volume) ∂volume ≤
      (1 + M_φ) * ∫ t in {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖}, (1 + ‖t‖) * f t ∂volume :=
    le_trans (integral_weighted_compl_coveredBox_le n f hfm hpdf hfmom C hC σ hσ hσ1 δ N)
      (mul_le_mul_of_nonneg_left hcompl_sub_tail (by linarith))
  linarith [hsum_cells_le, hres_le, htail_le]

/-! ## Phase 2, Step 5: `IsPdf (gmmApprox …)` and syntactic bridge to `gmmPDF`

We show that `gmmApprox n f C hC σ hσ δ N` is a probability density function (`IsPdf`),
and that it can be written literally as a `gmmPDF` with `(gridFinset n N).card + 1`
components, common covariance `(σ ^ 2) • C`, mixture weights `w` satisfying
`IsMixtureWeights w`, and locations uniformly bounded by `N * δ * √n`. -/

/-- For any shift `μ`, `x ↦ mollifier n C hC σ hσ (x - μ)` is integrable on `volume`
and integrates to `1`. -/
public theorem integrable_mollifier_sub (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) (μ : Fin n → ℝ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - μ)))
      volume :=
  integrable_toLp_shift n (-μ) (mollifier n C hC σ hσ) (mollifier_integrable n C hC σ hσ)
    (measurable_mollifier n C hC σ hσ)

public theorem integral_mollifier_sub (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (μ : Fin n → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin n),
        mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - μ)) ∂volume =
      1 := by
  rw [integral_shift_neg n μ (mollifier n C hC σ hσ)
      (measurable_mollifier n C hC σ hσ).aestronglyMeasurable,
    integral_mollifier n C hC σ hσ]

/-- **Phase 2, Step 5 (`isPdf_gmmApprox`)**: the finite Gaussian mixture approximation
`gmmApprox n f C hC σ hσ δ N` is a pdf (`IsPdf`) whenever `IsPdf f` and `0 < δ`. -/
public theorem isPdf_gmmApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hpdf : IsPdf f)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) : IsPdf (gmmApprox n f C hC σ hσ δ N) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold gmmApprox
    refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) ?_
    · exact mul_nonneg (cellWeight_nonneg hpdf.1 δ k) (mollifier_nonneg n C hC σ hσ _)
    · exact
        mul_nonneg (sub_nonneg.mpr (sum_cellWeight_le_one hpdf hδ N))
          (mollifier_nonneg n C hC σ hσ x)
  · unfold gmmApprox
    have hcell_int :
      ∀ k : Fin n → ℤ,
        MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin n) =>
            cellWeight f δ k *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))))
          volume :=
      fun k => (integrable_mollifier_sub n C hC σ hσ (gridPoint δ k : Fin n → ℝ)).const_mul _
    have hsum_int :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ∑ k ∈ gridFinset n N,
            cellWeight f δ k *
              mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))))
        volume :=
      MeasureTheory.integrable_finsetSum (gridFinset n N) (fun k _ => hcell_int k)
    have hres_int :
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * mollifier n C hC σ hσ x)
        volume :=
      (mollifier_integrable n C hC σ hσ).const_mul _
    rw [MeasureTheory.integral_add hsum_int hres_int,
      MeasureTheory.integral_finsetSum (gridFinset n N) (fun k _ => hcell_int k),
      MeasureTheory.integral_const_mul, integral_mollifier n C hC σ hσ, mul_one]
    have hsum_eq :
      (∑ k ∈ gridFinset n N,
          ∫ x : EuclideanSpace ℝ (Fin n),
            cellWeight f δ k *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) ∂volume) =
        ∑ k ∈ gridFinset n N, cellWeight f δ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [MeasureTheory.integral_const_mul, integral_mollifier_sub n C hC σ hσ, mul_one]
    rw [hsum_eq, add_sub_cancel]

/-- Scaling a positive definite matrix `C` by `σ ^ 2` (`0 < σ`) preserves `PosDef`. -/
public theorem posDef_sq_smul {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hC : C.PosDef) {σ : ℝ}
    (hσ : 0 < σ) : ((σ ^ 2) • C).PosDef :=
  hC.smul (sq_pos_of_pos hσ)

/-- A shifted mollifier `mollifier n C hC σ hσ (x - μ)` is identically equal to
`multivariateGaussianPDF n μ ((σ ^ 2) • C) (posDef_sq_smul hC hσ) x`. -/
public theorem mollifier_sub_eq_multivariateGaussianPDF (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (μ : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    mollifier n C hC σ hσ (WithLp.toLp 2 ((x : Fin n → ℝ) - μ)) =
      multivariateGaussianPDF n μ ((σ ^ 2) • C) (posDef_sq_smul hC hσ) x := by
  rw [mollifier, multivariateGaussianPDF_eq, multivariateGaussianPDF_eq]
  have hσ2_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hσ2_unit : IsUnit (σ ^ 2) := Ne.isUnit (ne_of_gt hσ2_pos)
  -- 1. Match the normalization constants
  have hdet : ((σ ^ 2) • C).det = (σ ^ n) ^ 2 * C.det := by
    rw [Matrix.det_smul, Fintype.card_fin]
    congr 1
    ring
  have hsqrt : Real.sqrt (((σ ^ 2) • C).det) = σ ^ n * Real.sqrt C.det := by
    rw [hdet, Real.sqrt_mul (sq_nonneg (σ ^ n)), Real.sqrt_sq (le_of_lt (pow_pos hσ n))]
  have hnorm :
    (σ : ℝ)⁻¹ ^ n * ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt C.det)⁻¹ =
      ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (((σ ^ 2) • C).det))⁻¹ := by
    rw [hsqrt, inv_pow, ← mul_inv]
    congr 1
    ring
  -- 2. Match the quadratic forms in the exponent
  have hinv : ((σ ^ 2) • C)⁻¹ = (σ ^ 2)⁻¹ • C⁻¹ := by
    have hCU : IsUnit C.det := Ne.isUnit (ne_of_gt hC.det_pos)
    have hright : ((σ ^ 2) • C) * ((σ ^ 2)⁻¹ • C⁻¹) = 1 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_nonsing_inv C hCU, smul_smul,
        inv_mul_cancel₀ (ne_of_gt hσ2_pos), one_smul]
    exact Matrix.inv_eq_right_inv hright
  have hquad :
    (C⁻¹ *ᵥ
          (((WithLp.toLp 2
                  ((σ : ℝ)⁻¹ •
                    ((WithLp.toLp 2 ((x : Fin n → ℝ) - μ) : EuclideanSpace ℝ (Fin n)) :
                      Fin n → ℝ)) :
                EuclideanSpace ℝ (Fin n)) :
              Fin n → ℝ) -
            0)) ⬝ᵥ
        (((WithLp.toLp 2
                ((σ : ℝ)⁻¹ •
                  ((WithLp.toLp 2 ((x : Fin n → ℝ) - μ) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) :
              EuclideanSpace ℝ (Fin n)) :
            Fin n → ℝ) -
          0) =
      (((σ ^ 2) • C)⁻¹ *ᵥ ((x : Fin n → ℝ) - μ)) ⬝ᵥ ((x : Fin n → ℝ) - μ) := by
    change
      (C⁻¹ *ᵥ (σ⁻¹ • ((x : Fin n → ℝ) - μ) - 0)) ⬝ᵥ (σ⁻¹ • ((x : Fin n → ℝ) - μ) - 0) =
        (((σ ^ 2) • C)⁻¹ *ᵥ ((x : Fin n → ℝ) - μ)) ⬝ᵥ ((x : Fin n → ℝ) - μ)
    rw [sub_zero, hinv, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_smul, sq, mul_inv]
  rw [← mul_assoc, hnorm, hquad]

/-- Every grid point `gridPoint δ k` for `k ∈ gridFinset n N` has norm at most `N * δ * √n`
when `0 < δ`. -/
public theorem norm_gridPoint_le_of_mem_gridFinset {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    {k : Fin n → ℤ} (hk : k ∈ gridFinset n N) :
    ‖gridPoint δ k‖ ≤ (N : ℝ) * δ * Real.sqrt (n : ℝ) := by
  rw [gridFinset, Fintype.mem_piFinset] at hk
  have hcoord : ∀ i : Fin n, ‖(gridPoint δ k : EuclideanSpace ℝ (Fin n)) i‖ ≤ (N : ℝ) * δ := by
    intro i
    have hi := Finset.mem_Ico.mp (hk i)
    change |δ * (k i : ℝ)| ≤ (N : ℝ) * δ
    rw [abs_mul, abs_of_pos hδ, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hδ)
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · exact_mod_cast hi.1
    · exact_mod_cast le_of_lt hi.2
  rw [EuclideanSpace.norm_eq]
  have hsum :
    ∑ i : Fin n, ‖(gridPoint δ k : EuclideanSpace ℝ (Fin n)) i‖ ^ 2 ≤
      ∑ _i : Fin n, ((N : ℝ) * δ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact
      sq_le_sq.mpr
        (by
          rw [abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (le_of_lt hδ))]
          exact hcoord i)
  have hcard : (∑ _i : Fin n, ((N : ℝ) * δ) ^ 2) = (n : ℝ) * ((N : ℝ) * δ) ^ 2 := by
    simp [Finset.sum_const]
  calc
    Real.sqrt (∑ i : Fin n, ‖(gridPoint δ k : EuclideanSpace ℝ (Fin n)) i‖ ^ 2) ≤
        Real.sqrt ((n : ℝ) * ((N : ℝ) * δ) ^ 2) :=
      by
      rw [← hcard]
      exact Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (n : ℝ) * Real.sqrt (((N : ℝ) * δ) ^ 2) := Real.sqrt_mul (Nat.cast_nonneg n) _
    _ = (N : ℝ) * δ * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg N) (le_of_lt hδ)), mul_comm]

/-- **Phase 2, Step 5 (`gmmApprox_eq_gmmPDF`)**: `gmmApprox n f C hC σ hσ δ N` is
syntactically equal to `gmmPDF n ((gridFinset n N).card + 1) ((σ ^ 2) • C) (posDef_sq_smul hC hσ) w μ`
for mixture weights `w` satisfying `IsMixtureWeights w` and locations `μ` bounded in norm
by `N * δ * √n`. -/
public theorem gmmApprox_eq_gmmPDF (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hpdf : IsPdf f)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) :
    ∃ (m : ℕ) (w : Fin m → ℝ) (μ : Fin m → Fin n → ℝ),
      IsMixtureWeights w ∧
        (∀ i : Fin m, ‖WithLp.toLp 2 (μ i)‖ ≤ (N : ℝ) * δ * Real.sqrt (n : ℝ)) ∧
        gmmApprox n f C hC σ hσ δ N = gmmPDF n m ((σ ^ 2) • C) (posDef_sq_smul hC hσ) w μ := by
  classical
  let S := gridFinset n N
  let e : S ≃ Fin S.card := S.equivFin
  let w : Fin (S.card + 1) → ℝ :=
    Fin.snoc (fun i : Fin S.card => cellWeight f δ (e.symm i).1) (1 - ∑ k ∈ S, cellWeight f δ k)
  let μ : Fin (S.card + 1) → Fin n → ℝ :=
    Fin.snoc (fun i : Fin S.card => (gridPoint δ (e.symm i).1 : Fin n → ℝ)) 0
  refine ⟨S.card + 1, w, μ, ?_, ?_, ?_⟩
  · -- `IsMixtureWeights w`
    refine ⟨fun j => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · dsimp only [w]
        rw [Fin.snoc_last]
        exact sub_nonneg.mpr (sum_cellWeight_le_one hpdf hδ N)
      · dsimp only [w]
        rw [Fin.snoc_castSucc]
        exact cellWeight_nonneg hpdf.1 δ _
    · rw [Fin.sum_univ_castSucc]
      dsimp only [w]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      have hsum_e :
        (∑ i : Fin S.card, cellWeight f δ (e.symm i).1) = ∑ k ∈ S, cellWeight f δ k := by
        rw [← e.sum_comp (fun i : Fin S.card => cellWeight f δ (e.symm i).1)]
        simp only [Equiv.symm_apply_apply]
        exact Finset.sum_attach S (fun k => cellWeight f δ k)
      rw [hsum_e, add_sub_cancel]
  · -- Norm bound on locations `μ j`
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · dsimp only [μ]
      rw [Fin.snoc_last,
        show (WithLp.toLp 2 (0 : Fin n → ℝ) : EuclideanSpace ℝ (Fin n)) = 0 from rfl, norm_zero]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (le_of_lt hδ)) (Real.sqrt_nonneg _)
    · dsimp only [μ]
      rw [Fin.snoc_castSucc, WithLp.toLp_ofLp]
      exact norm_gridPoint_le_of_mem_gridFinset hδ (e.symm i).2
  · -- Function equality `gmmApprox = gmmPDF`
    funext x
    unfold gmmApprox gmmPDF
    rw [Fin.sum_univ_castSucc]
    dsimp only [w, μ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    congr 1
    · have hsum_e :
        (∑ i : Fin S.card,
            cellWeight f δ (e.symm i).1 *
              multivariateGaussianPDF n (gridPoint δ (e.symm i).1 : Fin n → ℝ) ((σ ^ 2) • C)
                (posDef_sq_smul hC hσ) x) =
          ∑ k ∈ S,
            cellWeight f δ k *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ))) := by
        rw [← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
        have hattach :=
          Finset.sum_attach S
            (fun k =>
              cellWeight f δ k *
                multivariateGaussianPDF n (gridPoint δ k : Fin n → ℝ) ((σ ^ 2) • C)
                  (posDef_sq_smul hC hσ) x)
        refine hattach.trans ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mollifier_sub_eq_multivariateGaussianPDF]
      exact hsum_e.symm
    · congr 1
      have h0 : x = WithLp.toLp 2 ((x : Fin n → ℝ) - (0 : Fin n → ℝ)) := by
        rw [sub_zero, WithLp.toLp_ofLp]
      conv_lhs => rw [h0]
      exact mollifier_sub_eq_multivariateGaussianPDF n C hC σ hσ 0 x

/-! ## Phase 2, Step 6: the explicit diagonal sequence (`gmmPriorSeq`) and `hw_gmmPriorSeq`

At index `K : ℕ`, we choose:
* `σ_K := 1 / ((K : ℝ) + 1)` (`0 < σ_K ≤ 1`, `σ_K → 0`),
* `δ_K := 1 / ((K : ℝ) + 1) ^ 2` (`0 < δ_K`, `δ_K / σ_K = σ_K → 0`),
* `N_K := (K + 1) ^ 3` (so `N_K * δ_K = K + 1 > K`, ensuring `(coveredBox n δ_K N_K)ᶜ ⊆ {t | (K : ℝ) < ‖t‖}` without `Nat.ceil`).

Combining Step 1 (`weighted_smoothing_integrable`) and Step 3c
(`gmmApprox_quantization_of_modulus_bound`) via the triangle inequality proves that
`gmmPriorSeq` converges to `f` in weighted L¹, discharging the `hw` hypothesis of
`cme_uniform_balls_R`. -/

/-- The explicit diagonal sequence of finite Gaussian mixture priors approximating `f`:
at index `K`, bandwidth `σ_K = 1 / (K + 1)`, lattice spacing `δ_K = 1 / (K + 1)²`, and
integer half-width `N_K = (K + 1)³` (so the covered box radius is `N_K * δ_K = K + 1`). -/
@[expose]
public noncomputable def gmmPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun K =>
  gmmApprox n f C hC ((1 : ℝ) / ((K : ℝ) + 1)) (by positivity) ((1 : ℝ) / ((K : ℝ) + 1) ^ 2)
    ((K + 1) ^ 3)

/-- Every `gmmPriorSeq n f C hC K` is a probability density function (`IsPdf`). -/
public theorem isPdf_gmmPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hpdf : IsPdf f)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (K : ℕ) : IsPdf (gmmPriorSeq n f C hC K) :=
  isPdf_gmmApprox n f hpdf C hC ((1 : ℝ) / ((K : ℝ) + 1)) (by positivity)
    (by positivity : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) ^ 2) ((K + 1) ^ 3)

/-- `(1 + ‖x‖) * gmmApprox n f C hC σ hσ δ N x` is Bochner-integrable. -/
public theorem integrable_weighted_gmmApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (N : ℕ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * gmmApprox n f C hC σ hσ δ N x) volume := by
  have hcell :
    ∀ k : Fin n → ℤ,
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          cellWeight f δ k *
            ((1 + ‖x‖) *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ)))))
        volume :=
    fun k => (integrable_weighted_mollifier_sub n C hC σ hσ (gridPoint δ k)).const_mul _
  have hsum :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ k ∈ gridFinset n N,
          cellWeight f δ k *
            ((1 + ‖x‖) *
              mollifier n C hC σ hσ
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (gridPoint δ k : Fin n → ℝ)))))
      volume :=
    MeasureTheory.integrable_finsetSum (gridFinset n N) (fun k _ => hcell k)
  have hres :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 - ∑ k ∈ gridFinset n N, cellWeight f δ k) * ((1 + ‖x‖) * mollifier n C hC σ hσ x))
      volume :=
    (integrable_weighted_mollifier n C hC σ hσ).const_mul _
  refine (hsum.add hres).congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [Pi.add_apply, gmmApprox]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · ring

/-- `(1 + ‖x‖) * |gmmApprox … x - gaussSmoothed … x|` is Bochner-integrable. -/
public theorem integrable_weighted_abs_gmmApprox_sub_gaussSmoothed (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x|)
      volume := by
  have hgmm_int := integrable_weighted_gmmApprox n f C hC σ hσ δ N
  have hgs_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * gaussSmoothed n f C hC σ hσ x) volume := by
    have hψmeas := measurable_mollifier n C hC σ hσ
    have hgs_meas := measurable_gaussSmoothed n f hfm C hC σ hσ
    have hgs_nn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gaussSmoothed n f C hC σ hσ x :=
      (isPdf_gaussSmoothed n f hpdf hfm C hC σ hσ).1
    refine
      MeasureTheory.Integrable.mono'
        ((integrable_joint_smooth_prior n f hfm hpdf hfmom C hC σ hσ).integral_prod_right) ?_ ?_
    · exact
        ((by fun_prop :
            Measurable fun x : EuclideanSpace ℝ (Fin n) =>
              (1 + ‖x‖) * gaussSmoothed n f C hC σ hσ x)).aestronglyMeasurable
    · filter_upwards with x
      have hx_nn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx_nn (hgs_nn x))]
      show
        (1 + ‖x‖) * gaussSmoothed n f C hC σ hσ x ≤
          ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC σ hσ u *
              ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume
      unfold gaussSmoothed
      rw [← MeasureTheory.integral_const_mul (1 + ‖x‖)]
      refine
        le_of_eq (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by ring))
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hgmm_meas : Measurable (gmmApprox n f C hC σ hσ δ N) := by
    unfold gmmApprox; fun_prop
  have hgs_meas := measurable_gaussSmoothed n f hfm C hC σ hσ
  have hgmm_nn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gmmApprox n f C hC σ hσ δ N x :=
    (isPdf_gmmApprox n f hpdf C hC σ hσ hδ N).1
  have hgs_nn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gaussSmoothed n f C hC σ hσ x :=
    (isPdf_gaussSmoothed n f hpdf hfm C hC σ hσ).1
  refine MeasureTheory.Integrable.mono' (hgmm_int.add hgs_int) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) *
              |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x|)).aestronglyMeasurable
  · filter_upwards with x
    simp only [Pi.add_apply]
    have hx_nn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx_nn (abs_nonneg _))]
    have habs :
      |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x| ≤
        gmmApprox n f C hC σ hσ δ N x + gaussSmoothed n f C hC σ hσ x := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_nonneg (hgmm_nn x), abs_of_nonneg (hgs_nn x)]
    calc
      (1 + ‖x‖) * |gmmApprox n f C hC σ hσ δ N x - gaussSmoothed n f C hC σ hσ x| ≤
          (1 + ‖x‖) * (gmmApprox n f C hC σ hσ δ N x + gaussSmoothed n f C hC σ hσ x) :=
        mul_le_mul_of_nonneg_left habs hx_nn
      _ = (1 + ‖x‖) * gmmApprox n f C hC σ hσ δ N x + (1 + ‖x‖) * gaussSmoothed n f C hC σ hσ x :=
        by rw [mul_add]

/-- `(1 + ‖x‖) * |f x - gmmApprox … x|` is Bochner-integrable. -/
public theorem integrable_weighted_abs_diff_gmmApprox (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gmmApprox n f C hC σ hσ δ N x|)
      volume := by
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) volume := by
    have heq :
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) = fun x : EuclideanSpace ℝ (Fin n) =>
        f x + ‖x‖ * f x := by
      funext x; ring
    rw [heq]; exact hfi.add hfmom
  have hgmm_int := integrable_weighted_gmmApprox n f C hC σ hσ δ N
  have hψmeas := measurable_mollifier n C hC σ hσ
  have hgmm_meas : Measurable (gmmApprox n f C hC σ hσ δ N) := by
    unfold gmmApprox; fun_prop
  have hgmm_nn : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gmmApprox n f C hC σ hσ δ N x :=
    (isPdf_gmmApprox n f hpdf C hC σ hσ hδ N).1
  refine MeasureTheory.Integrable.mono' (hwf.add hgmm_int) ?_ ?_
  · exact
      ((by fun_prop :
          Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * |f x - gmmApprox n f C hC σ hσ δ N x|)).aestronglyMeasurable
  · filter_upwards with x
    simp only [Pi.add_apply]
    have hx_nn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx_nn (abs_nonneg _))]
    have habs : |f x - gmmApprox n f C hC σ hσ δ N x| ≤ f x + gmmApprox n f C hC σ hσ δ N x := by
      refine le_trans (abs_sub _ _) ?_
      rw [abs_of_nonneg (hpdf.1 x), abs_of_nonneg (hgmm_nn x)]
    calc
      (1 + ‖x‖) * |f x - gmmApprox n f C hC σ hσ δ N x| ≤
          (1 + ‖x‖) * (f x + gmmApprox n f C hC σ hσ δ N x) :=
        mul_le_mul_of_nonneg_left habs hx_nn
      _ = (1 + ‖x‖) * f x + (1 + ‖x‖) * gmmApprox n f C hC σ hσ δ N x := by rw [mul_add]

/-- The quantization gap `∫ x, (1 + ‖x‖) * |gmmPriorSeq K x - smoothedPriorSeq K x| dx`
tends to `0` as `K → ∞`. -/
public theorem weighted_quantization_tendsto_gmmPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    Filter.Tendsto
      (fun K : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwf :
    MeasureTheory.Integrable (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) volume := by
    have heq :
      (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) = fun t : EuclideanSpace ℝ (Fin n) =>
        f t + ‖t‖ * f t := by
      funext t; ring
    rw [heq]; exact hfi.add hfmom
  have hwf_nn : ∀ t : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖t‖) * f t := fun t =>
    mul_nonneg (by linarith [norm_nonneg t]) (hpdf.1 t)
  set M_f : ℝ := ∫ t : EuclideanSpace ℝ (Fin n), ‖t‖ * f t ∂volume
  have hMf_nn : 0 ≤ M_f :=
    MeasureTheory.integral_nonneg fun t => mul_nonneg (norm_nonneg t) (hpdf.1 t)
  set M_φ : ℝ := ∫ v : EuclideanSpace ℝ (Fin n), ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume
  have hMφ_nn : 0 ≤ M_φ :=
    MeasureTheory.integral_nonneg fun v =>
      mul_nonneg (norm_nonneg v) (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  -- 1. Continuity of `weightedModulus n φ_C` at `0`
  have hφ_pdf := isPdf_multivariateGaussianPDF n 0 C hC
  have hφ_mom := integrable_norm_mul_gaussianPDF_center n C hC
  have hmod_lim :
    Filter.Tendsto (weightedModulus n (multivariateGaussianPDF n 0 C hC)) (nhds 0) (nhds 0) :=
    weightedModulus_tendsto_integrable (multivariateGaussianPDF n 0 C hC) hφ_pdf.1
      (integrable_of_isPdf hφ_pdf) hφ_mom
  -- 2. Moment-tail limit `∫_{‖t‖ > K} (1 + ‖t‖) * f t → 0`
  have htail_lim :=
    setIntegral_tail_tendsto n (fun t : EuclideanSpace ℝ (Fin n) => (1 + ‖t‖) * f t) hwf hwf_nn
  -- 3. Ratio limit `√n / (K + 1) → 0`
  have hratio_lim :
    Filter.Tendsto (fun K : ℕ => Real.sqrt (n : ℝ) * ((1 : ℝ) / ((K : ℝ) + 1))) Filter.atTop
      (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := Real.sqrt (n : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
  -- Unpack `ε > 0`
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  set η : ℝ := ε / (2 * (1 + M_f))
  have hη_pos : 0 < η := div_pos hε (by linarith [hMf_nn])
  have hmod_ev :
    ∀ᶠ u : EuclideanSpace ℝ (Fin n) in nhds 0,
      dist (weightedModulus n (multivariateGaussianPDF n 0 C hC) u) 0 < η :=
    Metric.tendsto_nhds.mp hmod_lim η hη_pos
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.eventually_nhds_iff.mp hmod_ev
  obtain ⟨K₁, hK₁⟩ :=
    Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hratio_lim (r / 2) (half_pos hr_pos))
  have htail_eps_pos : 0 < ε / (4 * (1 + M_φ)) := div_pos hε (by linarith [hMφ_nn])
  obtain ⟨K₂, hK₂⟩ :=
    Filter.eventually_atTop.mp
      (Metric.tendsto_nhds.mp htail_lim (ε / (4 * (1 + M_φ))) htail_eps_pos)
  refine Filter.eventually_atTop.mpr ⟨max K₁ K₂, fun K hK => ?_⟩
  have hK1 : K₁ ≤ K := le_trans (le_max_left K₁ K₂) hK
  have hK2 : K₂ ≤ K := le_trans (le_max_right K₁ K₂) hK
  -- Diagonal parameter properties at `K`
  set σK : ℝ := (1 : ℝ) / ((K : ℝ) + 1)
  set δK : ℝ := (1 : ℝ) / ((K : ℝ) + 1) ^ 2
  set NK : ℕ := (K + 1) ^ 3
  have hKp1_pos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hσK_pos : 0 < σK := by positivity
  have hσK_le_one : σK ≤ 1 := by
    dsimp only [σK]
    rw [div_le_iff₀ hKp1_pos, one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) K]
  have hδK_pos : 0 < δK := by positivity
  have hRN : (K : ℝ) < (NK : ℝ) * δK := by
    have hprod : (NK : ℝ) * δK = (K : ℝ) + 1 := by
      dsimp only [NK, δK]
      push_cast
      field_simp [ne_of_gt hKp1_pos]
    linarith
  -- Modulus condition for `‖u‖ ≤ δK * √n / σK`
  have hratio_eq : δK * Real.sqrt (n : ℝ) / σK = Real.sqrt (n : ℝ) * ((1 : ℝ) / ((K : ℝ) + 1)) := by
    dsimp only [δK, σK]
    field_simp [ne_of_gt hKp1_pos]
  have hratio_lt : δK * Real.sqrt (n : ℝ) / σK < r := by
    rw [hratio_eq]
    have h1 := hK₁ K hK1
    have hnn : 0 ≤ Real.sqrt (n : ℝ) * ((1 : ℝ) / ((K : ℝ) + 1)) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h1
    linarith
  have hmod_K :
    ∀ u : EuclideanSpace ℝ (Fin n),
      ‖u‖ ≤ δK * Real.sqrt (n : ℝ) / σK →
        weightedModulus n (multivariateGaussianPDF n 0 C hC) u ≤ η := by
    intro u hu
    have hu_lt : dist u 0 < r := by
      rw [dist_zero_right]
      exact lt_of_le_of_lt hu hratio_lt
    have hdist := hr_ball hu_lt
    have hwm_nn : 0 ≤ weightedModulus n (multivariateGaussianPDF n 0 C hC) u :=
      MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hwm_nn] at hdist
    exact le_of_lt hdist
  -- Apply Step 3c (`gmmApprox_quantization_of_modulus_bound`)
  have hquant :=
    gmmApprox_quantization_of_modulus_bound n f hfm hpdf hfmom C hC σK hσK_pos hσK_le_one hδK_pos
      hRN (le_of_lt hη_pos) hmod_K
  -- First piece of `hquant` RHS equals `ε / 2`
  have hterm1 : η * (1 + M_f) = ε / 2 := by
    dsimp only [η]
    have hne : (1 : ℝ) + M_f ≠ 0 := by linarith [hMf_nn]
    field_simp [hne]
  -- Second piece of `hquant` RHS is `< ε / 2`
  have htail_K := hK₂ K hK2
  have htail_nn :
    0 ≤ ∫ t in {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}, (1 + ‖t‖) * f t ∂volume :=
    MeasureTheory.setIntegral_nonneg (measurableSet_norm_gt n K) (fun t _ => hwf_nn t)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg htail_nn] at htail_K
  have hterm2 :
    2 * (1 + M_φ) *
        (∫ t in {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}, (1 + ‖t‖) * f t ∂volume) <
      ε / 2 := by
    calc
      2 * (1 + M_φ) *
            (∫ t in {y : EuclideanSpace ℝ (Fin n) | (K : ℝ) < ‖y‖}, (1 + ‖t‖) * f t ∂volume) <
          2 * (1 + M_φ) * (ε / (4 * (1 + M_φ))) :=
        mul_lt_mul_of_pos_left htail_K (by linarith [hMφ_nn])
      _ = ε / 2 := by
        have hne : (1 : ℝ) + M_φ ≠ 0 := by linarith [hMφ_nn]
        field_simp [hne]
        ring
  have hval_nn :
    0 ≤
      ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| ∂volume :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hval_nn]
  change
    (∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) *
          |gmmApprox n f C hC σK hσK_pos δK NK x - gaussSmoothed n f C hC σK hσK_pos x| ∂volume) <
      ε
  linarith [hquant, hterm1, hterm2]

/-- Weighted-L¹ convergence in real Bochner integral form:
`∫ x, (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ∂volume → 0` as `K → ∞`. -/
public theorem weighted_tendsto_gmmPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    Filter.Tendsto
      (fun K : ℕ =>
        ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ∂volume)
      Filter.atTop (nhds 0) := by
  have hσpos : ∀ K : ℕ, 0 < (1 : ℝ) / ((K : ℝ) + 1) := fun K => div_pos one_pos (by positivity)
  have hσ0 : Filter.Tendsto (fun K : ℕ => (1 : ℝ) / ((K : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmooth :=
    weighted_smoothing_integrable n f hfm hpdf hfmom C hC (fun K => (1 : ℝ) / ((K : ℝ) + 1)) hσpos
      hσ0
  have hquant := weighted_quantization_tendsto_gmmPriorSeq n f hfm hpdf hfmom C hC
  have hsum_lim :
    Filter.Tendsto
      (fun K : ℕ =>
        (∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| ∂volume) +
          (∫ x : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| ∂volume))
      Filter.atTop (nhds 0) := by
    have h := hsmooth.add hquant
    rw [add_zero] at h
    exact h
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hsum_lim ε hε)
  refine Filter.eventually_atTop.mpr ⟨K₀, fun K hK => ?_⟩
  have hK₀K := hK₀ K hK
  have h1_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x|)
      volume :=
    integrable_weighted_abs_diff_gaussSmoothed n f hfm hpdf hfmom C hC ((1 : ℝ) / ((K : ℝ) + 1))
      (hσpos K)
  have h2_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x|)
      volume :=
    integrable_weighted_abs_gmmApprox_sub_gaussSmoothed n f hfm hpdf hfmom C hC
      ((1 : ℝ) / ((K : ℝ) + 1)) (hσpos K) (by positivity : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) ^ 2)
      ((K + 1) ^ 3)
  have hLHS_int :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x|) volume :=
    integrable_weighted_abs_diff_gmmApprox n f hfm hpdf hfmom C hC ((1 : ℝ) / ((K : ℝ) + 1))
      (hσpos K) (by positivity : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) ^ 2) ((K + 1) ^ 3)
  have htri :
    ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ∂volume ≤
      (∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| ∂volume) +
        (∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| ∂volume) := by
    rw [← MeasureTheory.integral_add' h1_int h2_int]
    refine MeasureTheory.integral_mono hLHS_int (h1_int.add h2_int) (fun x => ?_)
    simp only [Pi.add_apply]
    have hx_nn : 0 ≤ (1 : ℝ) + ‖x‖ := by linarith [norm_nonneg x]
    have habs :
      |f x - gmmPriorSeq n f C hC K x| ≤
        |f x - smoothedPriorSeq n f C hC K x| +
          |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| := by
      rw [abs_sub_comm (gmmPriorSeq n f C hC K x) (smoothedPriorSeq n f C hC K x)]
      exact abs_sub_le (f x) (smoothedPriorSeq n f C hC K x) (gmmPriorSeq n f C hC K x)
    calc
      (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ≤
          (1 + ‖x‖) *
            (|f x - smoothedPriorSeq n f C hC K x| +
              |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x|) :=
        mul_le_mul_of_nonneg_left habs hx_nn
      _ =
          (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| +
            (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| :=
        by rw [mul_add]
  have hLHS_nn :
    0 ≤ ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ∂volume :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  have hRHS_nn :
    0 ≤
      (∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| ∂volume) +
        (∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * |gmmPriorSeq n f C hC K x - smoothedPriorSeq n f C hC K x| ∂volume) :=
    add_nonneg
      (MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))
      (MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hRHS_nn] at hK₀K
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hLHS_nn]
  exact lt_of_le_of_lt htri hK₀K

/-- **Phase 2, Step 6 (`hw_gmmPriorSeq`)**: the finite Gaussian mixture prior sequence
`gmmPriorSeq n f C hC` satisfies the weighted-L¹ convergence hypothesis `hw` of
`cme_uniform_balls_R` for any measurable pdf `f` with finite first moment. -/
public theorem hw_gmmPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfm : Measurable f)
    (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    ∀ ε > 0,
      ∃ K₀ : ℕ,
        ∀ K ≥ K₀,
          ∫⁻ h : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal ((1 + ‖h‖) * |f h - gmmPriorSeq n f C hC K h|) ∂volume <
            ENNReal.ofReal ε := by
  intro ε hε
  have hconv := weighted_tendsto_gmmPriorSeq n f hfm hpdf hfmom C hC
  have hKint :
    ∀ K : ℕ,
      MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x|) volume :=
    fun K =>
    integrable_weighted_abs_diff_gmmApprox n f hfm hpdf hfmom C hC ((1 : ℝ) / ((K : ℝ) + 1))
      (by positivity) (by positivity : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) ^ 2) ((K + 1) ^ 3)
  have hwnn :
    ∀ K : ℕ,
      0 ≤ᵐ[volume]
        (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x|) :=
    fun K =>
    Filter.Eventually.of_forall fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  have hbridge :
    ∀ K : ℕ,
      ENNReal.ofReal
          (∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * |f x - gmmPriorSeq n f C hC K x| ∂volume) =
        ∫⁻ h : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal ((1 + ‖h‖) * |f h - gmmPriorSeq n f C hC K h|) ∂volume :=
    fun K => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hKint K) (hwnn K)
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hconv ε hε)
  refine ⟨K₀, fun K hK => ?_⟩
  have hK₀K := hK₀ K hK
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg
      (MeasureTheory.integral_nonneg fun x =>
        mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))] at hK₀K
  rw [← hbridge K]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hK₀K

/-! ## Phase 2, Step 7: main GMM density theorem in weighted L¹ and CME convergence corollary

We package the diagonal construction into the target theorem `gmm_density_weighted_L1`
(every measurable pdf `f` with finite first moment is approximated in weighted L¹ by a
sequence of finite Gaussian mixture pdfs `g K = gmmPDF …`) and compose with
`cme_uniform_balls_R` to obtain `cme_uniform_balls_gmm_prior_general`: locally uniform
convergence of the conditional mean estimates `cmeR … (gmmPriorSeq … K) → cmeR … f` on
every closed ball in `ℝ^m`, for arbitrary dimensions `m, n` and observation matrix `A`. -/

/-- **Theorem (GMM density in weighted L¹, `gmm_density_weighted_L1`)**:
Let `f : EuclideanSpace ℝ (Fin n) → ℝ` be a measurable probability density function
(`IsPdf f`) with finite first moment `Integrable (fun h => ‖h‖ * f h) volume`, and let
`C` be any positive definite matrix (e.g., `C = 1` for isotropic Gaussians). Then there
exists a sequence `g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ` (namely `gmmPriorSeq n f C hC`)
such that:
1. every `g K` is a pdf (`IsPdf (g K)`);
2. every `g K` is a **finite Gaussian mixture** (`gmmPDF`) with common covariance
   `((1 / (K + 1)) ^ 2) • C`, nonnegative mixture weights summing to `1`
   (`IsMixtureWeights w`), and locations bounded by `(K + 1) * √n`;
3. `g` converges to `f` in weighted L¹ (the exact `hw` hypothesis of `cme_uniform_balls_R`):
   `∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀,
     ∫⁻ h, ENNReal.ofReal ((1 + ‖h‖) * |f h - g K h|) ∂volume < ENNReal.ofReal ε`. -/
public theorem gmm_density_weighted_L1
    -- Let n be a natural number.
    (n : ℕ)
    -- Let f be a function from ℝ^n to ℝ.
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let f be measurable.
    (hfm : Measurable f)
    -- Let f be a PDF.
    (hpdf : IsPdf f)
    -- Let f have finite first moment.
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * f h) volume)
    -- Let C be a matrix in ℝ^{n × n}.
    (C : Matrix (Fin n) (Fin n) ℝ)
    -- Let C be positive definite.
    (hC : C.PosDef) :
    -- Then there exists a sequence of GMMs which converges to f in the weighted L¹ sense:
    ∃ g : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      -- gK is a sequence of GMMs
      (∀ K : ℕ, IsPdf (g K)) ∧
        (∀ K : ℕ,
          ∃ (m : ℕ) (w : Fin m → ℝ) (μ : Fin m → Fin n → ℝ), -- we have m weights and m means
            IsMixtureWeights w ∧
              (∀ i : Fin m, ‖WithLp.toLp 2 (μ i)‖ ≤ ((K : ℝ) + 1) * Real.sqrt (n : ℝ)) ∧
              g K =
                gmmPDF n m (((1 : ℝ) / ((K : ℝ) + 1)) ^ 2 • C)
                  (posDef_sq_smul hC (by positivity : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1))) w μ) ∧
        -- convergence of the sequence of GMMs
        (∀ ε > 0,
          ∃ K₀ : ℕ,
            ∀ K ≥ K₀,
              ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |f h - g K h|) ∂volume <
                ENNReal.ofReal ε) := by
  refine
    ⟨gmmPriorSeq n f C hC, isPdf_gmmPriorSeq n f hpdf C hC, ?_,
      hw_gmmPriorSeq n f hfm hpdf hfmom C hC⟩
  intro K
  have hσK : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) := by positivity
  have hδK : (0 : ℝ) < (1 : ℝ) / ((K : ℝ) + 1) ^ 2 := by positivity
  obtain ⟨m, w, μ, hw, hμ, heq⟩ :=
    gmmApprox_eq_gmmPDF n f hpdf C hC ((1 : ℝ) / ((K : ℝ) + 1)) hσK hδK ((K + 1) ^ 3)
  refine ⟨m, w, μ, hw, fun i => ?_, heq⟩
  have hKp1_pos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hprod :
    (((K + 1) ^ 3 : ℕ) : ℝ) * ((1 : ℝ) / ((K : ℝ) + 1) ^ 2) * Real.sqrt (n : ℝ) =
      ((K : ℝ) + 1) * Real.sqrt (n : ℝ) := by
    push_cast
    field_simp [ne_of_gt hKp1_pos]
  linarith [hμ i, hprod]

/-- **Phase 2, Step 7 (`cme_uniform_balls_gmm_prior_general`)**:
For any measurable pdf prior `f` with finite first moment, the conditional mean estimates
computed from the finite Gaussian mixture priors `gmmPriorSeq n f C hC K` converge to the
true CME `cmeR m n S hS A f` locally uniformly — uniformly on every closed ball of radius
`r > 0` in `ℝ^m`, for arbitrary dimensions `m, n` and arbitrary observation matrix `A`
(no invertibility or rank condition). -/
public theorem cme_uniform_balls_gmm_prior_general (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun K : ℕ =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A f y - cmeR m n S hS A (gmmPriorSeq n f C hC K) y‖)
      atTop (nhds 0) :=
  cme_uniform_balls_R m n S hS A f hpdf hfmom (gmmPriorSeq n f C hC)
    (isPdf_gmmPriorSeq n f hpdf C hC) (hw_gmmPriorSeq n f hfm hpdf hfmom C hC) r hr
