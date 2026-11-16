module

public import Main

/-!
# Phase 0 of `plan.md`: Gaussian mixture priors for `cme_uniform_balls_R`

A finite Gaussian mixture with weights `w` (nonnegative, summing to one), locations `μ`,
and common positive definite covariance `Cov` is `gmmPDF n k Cov hC w μ`. This file
proves:

* `isPdf_gmmPDF`: a finite Gaussian mixture is a pdf (`IsPdf`);
* `integrable_norm_mul_gmmPDF`: a finite Gaussian mixture has a finite first moment, so
  the `hfmom` hypothesis of `cme_uniform_balls_R` is automatic for GMM priors;
* `cme_convergence_of_gmm_prior`: for a GMM prior, the *constant* sequence of priors
  satisfies the weighted-L¹ convergence hypothesis of `cme_uniform_balls_R` (the
  difference of the priors is identically zero), hence the conditional mean estimates
  converge to the true CME locally uniformly (uniformly on every closed ball in `ℝ^m`).

This discharges the Phase 0 deliverable of `plan.md`: the weighted-L¹ hypothesis of
`cme_uniform_balls_R` is satisfiable by GMM priors whenever the true prior is itself a
GMM — the operative setting of the Koller–Fesl–Turan–Utschick 2022 estimator. Phases 1
and 2 of `plan.md` (approximating a general finite-first-moment pdf prior by GMMs) are
future work.
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
public noncomputable def mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (_hσ : 0 < σ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => (σ : ℝ)⁻¹ ^ n *
    multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ)))

/-- The Gaussian-smoothed prior: the (continuum) mixture
`x ↦ ∫ ψ_σ(u) · f (x − u) du`. -/
public noncomputable def gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (_hσ : 0 < σ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∫ u : EuclideanSpace ℝ (Fin n),
    mollifier n C hC σ _hσ u * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume

/-- Transport for scalar-multiple identity matrices. -/
theorem toEuclideanLin_smul_one (n : ℕ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (r • (1 : Matrix (Fin n) (Fin n) ℝ)) x
      = WithLp.toLp 2 (r • (x : Fin n → ℝ)) := by
  apply WithLp.ofLp_injective
  show (r • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (x : Fin n → ℝ) = r • (x : Fin n → ℝ)
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem mollifier_nonneg (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ mollifier n C hC σ hσ x := by
  simp only [mollifier]
  exact mul_nonneg (le_of_lt (pow_pos (inv_pos.mpr hσ) n))
    (le_of_lt (multivariateGaussianPDF_pos n 0 C hC _))

/-- Mass of the mollifier: `∫ ψ_σ = 1` (change of variables `x ↦ σ⁻¹ • x` via
`integral_subst`). -/
theorem integral_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    ∫ x : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ x ∂volume = 1 := by
  classical
  simp only [mollifier]
  have hBdet : 0 < ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_pos (inv_pos.mpr hσ) n
  have hsub := integral_subst n 0 ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) hBdet
    (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n 0 C hC x)
    (measurable_multivariateGaussianPDF n 0 C hC).aemeasurable
  rw [integral_gaussianPDF n 0 C hC, smul_eq_mul, Matrix.det_smul, Matrix.det_one,
    Fintype.card_fin, mul_one] at hsub
  simp only [zero_add] at hsub
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
    rw [toEuclideanLin_smul_one])] at hsub
  have hinner : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ))) ∂volume
      = (σ : ℝ) ^ n := by
    have h2 : (σ : ℝ) ^ n * 1
        = (σ : ℝ) ^ n * ((σ : ℝ)⁻¹ ^ n * ∫ x : EuclideanSpace ℝ (Fin n),
            multivariateGaussianPDF n 0 C hC
              (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (x : Fin n → ℝ))) ∂volume) := by
      rw [← hsub]
    rw [mul_one, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), one_mul] at h2
    exact h2.symm
  rw [integral_const_mul, hinner, inv_pow, inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hσ))]

/-- `∫ ψ_σ(u) · H u du = ∫ φ_C(v) · H (σ v) dv`: the transport used for the dominated
convergence in the smoothing theorem (change of variables `u ↦ σ v` via
`integral_subst`). -/
theorem integral_mollifier_mul (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) (H : EuclideanSpace ℝ (Fin n) → ℝ)
    (hH : AEMeasurable H volume) :
    ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ u * H u ∂volume
      = ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            H (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) ∂volume := by
  classical
  simp only [mollifier, mul_assoc, MeasureTheory.integral_const_mul]
  have hpdfS : AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))) volume :=
    ((measurable_multivariateGaussianPDF n 0 C hC).comp
      (by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).aemeasurable
  have hFmeas : AEMeasurable
      (fun u : EuclideanSpace ℝ (Fin n) =>
        (σ : ℝ)⁻¹ ^ n * multivariateGaussianPDF n 0 C hC
            (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) * H u) volume :=
    (hpdfS.const_mul ((σ : ℝ)⁻¹ ^ n)).mul hH
  have hBdet : 0 < ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_pos hσ n
  have htr : ∀ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC
        (WithLp.toLp 2 ((σ : ℝ)⁻¹ •
          ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))
            v : Fin n → ℝ)))
      = multivariateGaussianPDF n 0 C hC v := by
    intro v
    congr 1
    rw [toEuclideanLin_smul_one, WithLp.ofLp_toLp, ← mul_smul,
      inv_mul_cancel₀ (ne_of_gt hσ), one_smul]
  have hsub := integral_subst n 0 ((σ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) hBdet
    (fun u : EuclideanSpace ℝ (Fin n) =>
      (σ : ℝ)⁻¹ ^ n * multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) * H u) hFmeas
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hsub
  simp only [zero_add, htr, smul_eq_mul, mul_assoc] at hsub
  simp only [MeasureTheory.integral_const_mul] at hsub
  rw [hsub, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), one_mul]
  have hpt : ∀ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC v * H ((toEuclideanLin (σ • 1)) v)
        = multivariateGaussianPDF n 0 C hC v *
            H (WithLp.toLp 2 ((σ : ℝ) • (v : Fin n → ℝ))) := by
    intro v
    rw [toEuclideanLin_smul_one]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => hpt v)

/-- Bochner integrability is invariant under the map `h ↦ toLp 2 (c - h)` (the
composition of the reflection and a translation, both `volume`-preserving). -/
theorem integrable_toLp_sub {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [SecondCountableTopology F] (n : ℕ)
    (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.Integrable g volume) (hgmeas : Measurable g) :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        g (WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ)))) volume := by
  classical
  have hLdet : |(LinearMap.det
      (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))))| = 1 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  have hLne : (LinearMap.det
      (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)))) ≠ 0 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
    exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)
  have hLabs : |(LinearMap.det
      (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))))| = 1 := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
  have hTneg : Measurable
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) := by
    have heq : (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ)))
        = fun h : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (0 : Fin n → ℝ) - WithLp.toLp 2 (h : Fin n → ℝ) := by
      funext h
      rw [← zero_sub, WithLp.toLp_sub]
    rw [heq]
    exact Measurable.sub measurable_const measurable_id
  have hTnegmap : MeasureTheory.Measure.map
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) volume = volume := by
    rw [show (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ)))
        = Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
      from by
        funext h
        apply WithLp.ofLp_injective
        show (-(h : Fin n → ℝ) : Fin n → ℝ) =
          ((-1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (h : Fin n → ℝ)
        rw [Matrix.smul_mulVec, Matrix.one_mulVec, neg_one_smul],
      MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne,
      abs_inv, hLabs, inv_one, ENNReal.ofReal_one, one_smul]
  have hTmeas : Measurable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ))) := by
    have heq : (fun h : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ)))
        = fun h : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (c : Fin n → ℝ) - WithLp.toLp 2 (h : Fin n → ℝ) := by
      funext h
      rw [WithLp.toLp_sub]
    rw [heq]
    exact Measurable.sub measurable_const measurable_id
  have hTmeasOut : Measurable
      (fun z : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) := by
    have heq : (fun z : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ)))
        = fun z : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (c : Fin n → ℝ) + WithLp.toLp 2 (z : Fin n → ℝ) := by
      funext z
      rw [WithLp.toLp_add]
    rw [heq]
    exact Measurable.add measurable_const measurable_id
  have hTmap : MeasureTheory.Measure.map
      (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ)))
      volume = volume := by
    have hcomp : (fun h : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((c : Fin n → ℝ) - (h : Fin n → ℝ)))
      = (fun z : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ))) ∘
        (fun h : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (-(h : Fin n → ℝ))) := by
      funext h
      congr 1
    have heqO : (fun z : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((c : Fin n → ℝ) + (z : Fin n → ℝ)))
        = fun x : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c : Fin n → ℝ) + x := by
      funext z
      rw [WithLp.toLp_add, WithLp.ofLp_toLp]
    rw [hcomp, ← MeasureTheory.Measure.map_map hTmeasOut hTneg, hTnegmap, heqO,
      MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  refine ⟨(hgmeas.comp hTmeas).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm, ← lintegral_map hgmeas.enorm hTmeas,
    hTmap]
  exact hg.2
