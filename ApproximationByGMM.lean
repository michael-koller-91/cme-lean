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
