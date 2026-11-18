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
    exact (((by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin n) => ‖y‖)).isOpen_preimage _
      isOpen_Ioi).measurableSet
  have hind : ∀ k : ℕ, ∫ x in {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}, g x ∂volume
      = ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x ∂volume :=
    fun k => (MeasureTheory.integral_indicator (s := {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖})
      (hmeas k)).symm
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k => (hind k).symm) ?_
  have hbound : ∀ k : ℕ, ∀ᵐ x ∂volume,
      ‖{y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x‖ ≤ g x := by
    intro k
    filter_upwards with x
    rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}) with hx | hx
    · simp only [Set.indicator_of_mem hx]
      simp [abs_of_nonneg (hgnonneg x)]
    · simp only [Set.indicator_of_notMem hx]
      simp
      exact hgnonneg x
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun k : ℕ => {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x)
        Filter.atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
    filter_upwards with x
    have hev : (fun k : ℕ => {y : EuclideanSpace ℝ (Fin n) | (k : ℝ) < ‖y‖}.indicator g x)
        =ᶠ[Filter.atTop] fun _ => (0 : ℝ) := by
      obtain ⟨k₀, h⟩ := exists_nat_gt ‖x‖
      filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
      have hmem : ¬((k : ℝ) < ‖x‖) :=
        not_lt.mpr (le_trans (le_of_lt h) (Nat.cast_le.mpr hk))
      simp [hmem]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence g
    (f := fun _ => (0 : ℝ)) (fun k => hg.1.indicator (hmeas k)) hg hbound hlim
  rw [integral_zero] at hdct
  exact hdct

/-- Helper: the outside of a closed ball as a set-of-norm predicate is measurable. -/
theorem measurableSet_norm_gt (n : ℕ) (r : ℝ) :
    MeasurableSet {y : EuclideanSpace ℝ (Fin n) | r < ‖y‖} := by
  have h : {y : EuclideanSpace ℝ (Fin n) | r < ‖y‖} =
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r)ᶜ := by
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, not_le, Set.mem_setOf_eq,
      Set.mem_compl_iff]
  rw [h]
  exact Metric.isClosed_closedBall.measurableSet.compl

set_option maxHeartbeats 2000000 in
set_option diagnostics true in
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
    Filter.Tendsto (fun k : ℕ => ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u k : Fin n → ℝ))) - f x| ∂volume)
      Filter.atTop (nhds 0) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hwfint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      volume := by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
        = fun x : EuclideanSpace ℝ (Fin n) => f x + ‖x‖ * f x := by
      funext x; ring
    rw [heq]; exact hfi.add hfmom
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  -- the moment-tail lemma applied to `w * f`
  have htail := setIntegral_tail_tendsto n (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
    hwfint hwnonneg
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
    exact Filter.eventually_atTop.mpr ⟨N, fun k hk =>
      hN (k + k₀) (Nat.le_trans hk (Nat.le_add_right k k₀))⟩
  -- main claim for the shifted sequence
  have hmain : Filter.Tendsto (fun k : ℕ => ∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
        ∂volume) Filter.atTop (nhds 0) := by
    classical
    have hfm : Measurable f := hf.measurable
    -- the norm triangle for the shifted vector
    have htri : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖ + ‖u (k + k₀)‖ := by
      intro k x
      have heq : x = WithLp.toLp 2 (((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) +
          (u (k + k₀) : Fin n → ℝ)) := by
        apply WithLp.ofLp_injective
        show (x : Fin n → ℝ) =
          ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) + (u (k + k₀) : Fin n → ℝ)
        rw [sub_add_cancel]
      rw [show ‖x‖ = ‖WithLp.toLp 2 (((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)) +
          (u (k + k₀) : Fin n → ℝ))‖ from congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) heq,
        WithLp.toLp_add]
      exact norm_add_le (a := WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))
        (b := WithLp.toLp 2 ((u (k + k₀) : Fin n → ℝ)))
    -- the weighted bound `w(x) ≤ (1 + ‖u‖) * (1 + ‖x − u‖)`
    have hbnd : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|
          ≤ (1 + ‖u (k + k₀)‖) *
            (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) := by
      intro k x
      rw [abs_of_nonneg (hf0 _)]
      have hnorm : (1 + ‖x‖) ≤ (1 + ‖u (k + k₀)‖) *
          (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) := by
        have hprod : 0 ≤ ‖u (k + k₀)‖ *
            ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖ :=
          mul_nonneg (norm_nonneg (u (k + k₀)))
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))
        nlinarith [htri k x, hprod]
      exact mul_le_mul_of_nonneg_right hnorm (hf0 _)
    -- integrability of the shifted weighted `f` (transported from `hwfint`)
    have hshiftint : ∀ k : ℕ, MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖u (k + k₀)‖) * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))) volume := by
      intro k
      have h1 := integrable_toLp_shift n (-(u (k + k₀) : Fin n → ℝ))
        (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖u (k + k₀)‖) * ((1 + ‖z‖) * f z))
        (hwfint.const_mul (1 + ‖u (k + k₀)‖)) (by fun_prop)
      refine h1.congr' ?_ ?_
      · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖u (k + k₀)‖) * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))))).aestronglyMeasurable
      · filter_upwards with x
        show ‖(fun z : EuclideanSpace ℝ (Fin n) =>
                (1 + ‖u (k + k₀)‖) * ((1 + ‖z‖) * f z))
              (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ))))‖
          = ‖(1 + ‖u (k + k₀)‖) * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖) *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))‖
        rw [sub_eq_add_neg]
    -- integrability of the full modulus integrand
    have hintg : ∀ k : ℕ, MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
        volume := by
      intro k
      refine MeasureTheory.Integrable.mono ((hshiftint k).add hwfint) ?_ ?_
      · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)
            ).aestronglyMeasurable
      · filter_upwards with x
        have habs : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
            ≤ |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|),
          abs_of_nonneg (add_nonneg
            (mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
              (mul_nonneg (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) -
                (u (k + k₀) : Fin n → ℝ)))]) (hf0 _))) (hwnonneg x))]
        have hstep1 : (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
            ≤ (1 + ‖x‖) * (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|
              + |f x|) := mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
        have hstep2 : (1 + ‖x‖) *
            (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x|)
            ≤ (1 + ‖u (k + k₀)‖) * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) -
              (u (k + k₀) : Fin n → ℝ))‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) -
              (u (k + k₀) : Fin n → ℝ)))) + (1 + ‖x‖) * f x := by
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
    have hK₁' : ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖},
        (1 + ‖x‖) * f x ∂volume < δ := by
      have h0 : 0 ≤ ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖},
          (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.setIntegral_nonneg (measurableSet_norm_gt n (K₁ : ℝ))
          (fun x _ => hwnonneg x)
      have h := hK₁
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at h
    -- a bound for `|f|` on the ball of radius `(K₁ : ℝ) + 2`
    obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ((K₁ : ℝ) + 2)
      ).exists_bound_of_continuousOn (hf.abs.continuousOn)
    obtain ⟨B, hB0, hBmax⟩ : ∃ B, 0 ≤ B ∧ ∀ z : EuclideanSpace ℝ (Fin n),
        ‖z‖ ≤ (K₁ : ℝ) + 2 → |f z| ≤ B := by
      refine ⟨max B₀ 0, le_max_right _ _, fun z hz => ?_⟩
      have hz' : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((K₁ : ℝ) + 2) :=
        Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
      have hzn := hB₀ z hz'
      simp only [Real.norm_eq_abs, abs_abs] at hzn
      linarith [hzn, le_max_left B₀ 0]
    have hcoreBall : {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} =
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ((K₁ : ℝ) + 1) := by
      ext y
      simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]
    have hmeasCore : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := by
      rw [hcoreBall]
      exact Metric.isClosed_closedBall.measurableSet
    -- the core DCT
    have hdom : ∀ (k : ℕ) (x : EuclideanSpace ℝ (Fin n)),
        |{y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x|
          ≤ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
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
        have habs : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
            ≤ |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)]
        have h5 : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| ≤ B :=
          hBmax _ hz'
        have h6 : |f x| ≤ B := hBmax x (by linarith [hcore])
        have h7a : (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|
            ≤ (1 + ((K₁ : ℝ) + 1)) * B := by
          refine le_trans (mul_le_mul_of_nonneg_left h5 (by linarith [norm_nonneg x])) ?_
          exact mul_le_mul_of_nonneg_right (by linarith [hcore]) (by linarith [hB0])
        have h7b : (1 + ‖x‖) * |f x| ≤ (1 + ((K₁ : ℝ) + 1)) * B := by
          refine le_trans (mul_le_mul_of_nonneg_left h6 (by linarith [norm_nonneg x])) ?_
          exact mul_le_mul_of_nonneg_right (by linarith [hcore]) (by linarith [hB0])
        refine le_trans (mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])) ?_
        rw [mul_add]
        have h7c : (1 + ((K₁ : ℝ) + 1)) * (2 * B)
            = (1 + ((K₁ : ℝ) + 1)) * B + (1 + ((K₁ : ℝ) + 1)) * B := by ring
        linarith [h7a, h7b, h7c]
      · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} :=
          not_le.mpr hcore
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    have hlim : ∀ᵐ x ∂volume, Filter.Tendsto (fun k : ℕ =>
        {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x)
        Filter.atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
      filter_upwards with x
      rcases le_or_gt ‖x‖ ((K₁ : ℝ) + 1) with hcore | hcore
      · have hmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} := hcore
        simp only [Set.indicator_of_mem hmem]
        have hG : Continuous (fun v : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (v : Fin n → ℝ))) - f x|) := by
          fun_prop
        have h1 := Filter.Tendsto.comp (hG.tendsto (0 : EuclideanSpace ℝ (Fin n))) hu'
        have hcong : ∀ k : ℕ, ((fun v : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (v : Fin n → ℝ))) - f x|) ∘
              (fun k : ℕ => u (k + k₀))) k
            = (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| :=
          fun k => rfl
        simpa using Filter.Tendsto.congr hcong h1
      · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1} :=
          not_le.mpr hcore
        simp only [Set.indicator_of_notMem hmem]
        exact tendsto_const_nhds
    have hboundint : MeasureTheory.Integrable
        ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B))) volume := by
      refine ⟨(measurable_const.indicator hmeasCore).aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      have h2 : (fun x : EuclideanSpace ℝ (Fin n) => ‖{y : EuclideanSpace ℝ (Fin n) |
          ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)) x‖ₑ)
          = {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
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
    have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
      ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
        (fun _ => (1 + ((K₁ : ℝ) + 1)) * (2 * B)))
      (f := fun _ => (0 : ℝ))
      (fun k => (((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)).indicator
          hmeasCore).aestronglyMeasurable)
      hboundint
      (fun k => Filter.Eventually.of_forall fun x => hdom k x) hlim
    rw [integral_zero] at hdct
    have hdct' : Filter.Tendsto (fun k : ℕ => ∫ x in {y : EuclideanSpace ℝ (Fin n) |
        ‖y‖ ≤ (K₁ : ℝ) + 1}, (1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume)
        Filter.atTop (𝓝 0) := by
      refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun k => ?_) hdct
      exact MeasureTheory.integral_indicator
        (s := {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) hmeasCore
    -- the tail bound `T1 < 2δ` via the transport of the shifted indicator
    -- the tail bound `T1 < 2δ` via the transport of the shifted indicator
    have hψ₂meas : Measurable ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
        (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)) :=
      ((by fun_prop : Measurable fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)).indicator
        (measurableSet_norm_gt n (K₁ : ℝ))
    have hψ₂int : MeasureTheory.Integrable
        ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
          (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)) volume := by
      refine MeasureTheory.Integrable.mono hwfint ?_ ?_
      · exact hψ₂meas.aestronglyMeasurable
      · filter_upwards with x
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}) with hmem | hmem
        · simp only [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_of_nonneg (hwnonneg x)]
          exact le_refl _
        · simp only [Set.indicator_of_notMem hmem, Real.norm_eq_abs, abs_zero]
          exact abs_nonneg _
    have hT1intall : ∀ k : ℕ, MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x) volume := by
      intro k
      refine MeasureTheory.Integrable.mono (hshiftint k) ?_ ?_
      · exact (((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)).indicator
            (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
      · filter_upwards with x
        have hχpos : 0 ≤ (1 + ‖u (k + k₀)‖) * ((1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) -
            (u (k + k₀) : Fin n → ℝ))‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) -
            (u (k + k₀) : Fin n → ℝ)))) :=
          mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
            (mul_nonneg (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) -
              (u (k + k₀) : Fin n → ℝ)))]) (hf0 _))
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem,
            abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|),
            abs_of_nonneg hχpos, ← mul_assoc]
          exact hbnd k x
        · rw [Set.indicator_of_notMem hmem, abs_zero, abs_of_nonneg hχpos]
          exact hχpos
    have hT1 : ∀ k : ℕ, ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x ∂volume
      < 2 * δ := by
      intro k
      have hψ₂shift : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
            (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
              (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) volume := by
        have h2 := integrable_toLp_shift n (-(u (k + k₀) : Fin n → ℝ))
          ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
            (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)) hψ₂int hψ₂meas
        refine h2.congr' ?_ ?_
        · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))))).aestronglyMeasurable
        · filter_upwards with x
          show ‖{y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ))))‖
            = ‖{y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))‖
          rw [sub_eq_add_neg]
      have hT1int := hT1intall k
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x
          ≤ (1 + ‖u (k + k₀)‖) * ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) := by
        intro x
        rcases le_or_gt ‖x‖ ((K₁ : ℝ) + 1) with hout | hin
        · have hmem : x ∉ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} :=
            not_lt.mpr hout
          rw [Set.indicator_of_notMem hmem]
          have hpos : 0 ≤ (1 + ‖u (k + k₀)‖) *
              ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) := by
            rcases em ((WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) ∈
              {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}) with hm | hm
            · rw [Set.indicator_of_mem hm]
              exact mul_nonneg (by linarith [norm_nonneg (u (k + k₀))])
                (mul_nonneg (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) -
                  (u (k + k₀) : Fin n → ℝ)))]) (hf0 _))
            · rw [Set.indicator_of_notMem hm]
              exact mul_nonneg (by linarith [norm_nonneg (u (k + k₀))]) (le_refl 0)
          exact hpos
        · have hmem : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} := hin
          have hzmem : (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) ∈
              {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖} := by
            show (K₁ : ℝ) < ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))‖
            linarith [htri k x, hu1 k, hin]
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hzmem, ← mul_assoc]
          exact hbnd k x
      have hchain : ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x ∂volume
          ≤ ∫ x : EuclideanSpace ℝ (Fin n),
              (1 + ‖u (k + k₀)‖) * ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
                (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                  (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))) ∂volume :=
        MeasureTheory.integral_mono hT1int (hψ₂shift.const_mul (1 + ‖u (k + k₀)‖)) hpt
      rw [MeasureTheory.integral_const_mul (1 + ‖u (k + k₀)‖)] at hchain
      have htransport : ∫ x : EuclideanSpace ℝ (Fin n),
            {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
              (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)
                (WithLp.toLp 2 ((x : Fin n → ℝ) + (-(u (k + k₀) : Fin n → ℝ)))) ∂volume
          = ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume := by
        rw [integral_toLp_trans_right n (-(u (k + k₀) : Fin n → ℝ))
          ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
            (fun z : EuclideanSpace ℝ (Fin n) => (1 + ‖z‖) * f z)) hψ₂meas.aestronglyMeasurable,
          integral_indicator (measurableSet_norm_gt n (K₁ : ℝ))]
      simp only [sub_eq_add_neg] at hchain
      rw [htransport] at hchain
      refine lt_of_le_of_lt hchain ?_
      have hint : 0 ≤ ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖},
          (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.setIntegral_nonneg (measurableSet_norm_gt n (K₁ : ℝ))
          (fun x _ => hwnonneg x)
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right
          (show (1 + ‖u (k + k₀)‖ : ℝ) ≤ 2 by linarith [norm_nonneg (u (k + k₀)), hu1 k]) hint)
        (mul_lt_mul_of_pos_left hK₁' (show (0 : ℝ) < 2 by norm_num))
    -- the `f`-tail bound `T2 < δ`
    have hT2 : ∫ x : EuclideanSpace ℝ (Fin n),
        {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume < δ := by
      have hT2int : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x) volume := by
        refine MeasureTheory.Integrable.mono hwfint ?_ ?_
        · exact (((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
            (1 + ‖x‖) * f x)).indicator (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
        · filter_upwards with x
          simp only [Real.norm_eq_abs]
          rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
          · rw [Set.indicator_of_mem hmem, abs_of_nonneg (hwnonneg x)]
          · rw [Set.indicator_of_notMem hmem, abs_zero]
            exact abs_nonneg _
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x
          ≤ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
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
      have hint2 : ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume
        = ∫ x in {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) < ‖y‖}, (1 + ‖x‖) * f x ∂volume :=
        MeasureTheory.integral_indicator (measurableSet_norm_gt n (K₁ : ℝ))
      exact lt_of_le_of_lt (MeasureTheory.integral_mono hT2int hψ₂int hpt)
        (lt_of_le_of_lt (le_of_eq hint2) hK₁')
    -- assemble
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hdct' δ hδpos)
    refine Filter.eventually_atTop.mpr ⟨N₁, fun k hk => ?_⟩
    have hA : ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume
        < δ := by
      have h0 : 0 ≤ ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
        MeasureTheory.setIntegral_nonneg hmeasCore (fun x _ => by positivity)
      have h := hN₁ k hk
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg h0] at h
    have hAint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x) volume := by
      refine MeasureTheory.Integrable.mono (hintg k) ?_ ?_
      · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x)).aestronglyMeasurable
      · filter_upwards with x
        have hχpos : 0 ≤ (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| := by positivity
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem, abs_of_nonneg hχpos]
        · rw [Set.indicator_of_notMem hmem, abs_zero]
          exact abs_nonneg _
    have hT2int : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
          (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x) volume := by
      refine MeasureTheory.Integrable.mono hwfint ?_ ?_
      · exact (((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * f x)).indicator (measurableSet_norm_gt n ((K₁ : ℝ) + 1))).aestronglyMeasurable
      · filter_upwards with x
        simp only [Real.norm_eq_abs]
        rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
        · rw [Set.indicator_of_mem hmem, abs_of_nonneg (hwnonneg x)]
        · rw [Set.indicator_of_notMem hmem, abs_zero]
          exact abs_nonneg _
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
          ≤ ({y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)) x
            + ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|)) x
            + ({y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
              (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)) x := by
      intro x
      rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}) with hmem | hmem
      · have hmem' : ‖x‖ ≤ (K₁ : ℝ) + 1 := by
          simpa only [Set.mem_setOf_eq] using hmem
        have hmem2 : x ∉ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} :=
          not_lt.mpr hmem'
        have hT1rw : {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x = 0 := by
          rw [Set.indicator_of_notMem hmem2]
        have hT2rw : {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x = 0 := by
          rw [Set.indicator_of_notMem hmem2]
        simp only [Set.indicator_of_mem hmem, hT1rw, hT2rw]
        linarith [abs_nonneg ((1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|)]
      · have hmem' : ¬(‖x‖ ≤ (K₁ : ℝ) + 1) := by
          simpa only [Set.mem_setOf_eq] using hmem
        have hmem2 : x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖} :=
          not_le.mp hmem'
        have hT1rw : {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x
            = (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| := by
          rw [Set.indicator_of_mem hmem2]
        have hT2rw : {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x = (1 + ‖x‖) * f x := by
          rw [Set.indicator_of_mem hmem2]
        rw [Set.indicator_of_notMem hmem, hT1rw, hT2rw]
        have habs : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
            ≤ |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        have hstep1 : (1 + ‖x‖) *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|
            ≤ (1 + ‖x‖) * (|f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|
              + |f x|) := mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
        rw [mul_add, abs_of_nonneg (hf0 x)] at hstep1
        linarith [hstep1]
    have hgnonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
      MeasureTheory.integral_nonneg (fun x => by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hgnonneg]
    have h1 := MeasureTheory.integral_mono (hintg k)
      ((hAint.add (hT1intall k)).add hT2int) hpoint
    refine lt_of_le_of_lt h1 ?_
    rw [MeasureTheory.integral_add' (hAint.add (hT1intall k)) hT2int,
      MeasureTheory.integral_add' hAint (hT1intall k)]
    have hT2pos : ∀ x : EuclideanSpace ℝ (Fin n),
        0 ≤ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
          (fun x' : EuclideanSpace ℝ (Fin n) => (1 + ‖x'‖) * f x') x := by
      intro x
      rcases em (x ∈ {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}) with hmem | hmem
      · rw [Set.indicator_of_mem hmem]
        exact mul_nonneg (by linarith [norm_nonneg x]) (hf0 x)
      · rw [Set.indicator_of_notMem hmem]
    have hT2le : ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x ∂volume
        + ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x ∂volume
        ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x ∂volume
        + ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ)))|) x ∂volume
        + ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | (K₁ : ℝ) + 1 < ‖y‖}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) x ∂volume :=
      le_add_of_nonneg_right (MeasureTheory.integral_nonneg hT2pos)
    have hAeq : ∫ x : EuclideanSpace ℝ (Fin n),
          {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1}.indicator
            (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x|) x ∂volume
      = ∫ x in {y : EuclideanSpace ℝ (Fin n) | ‖y‖ ≤ (K₁ : ℝ) + 1},
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u (k + k₀) : Fin n → ℝ))) - f x| ∂volume :=
      MeasureTheory.integral_indicator hmeasCore
    linarith [hT2le, hA, hAeq, hT1 k, hT2, hδε]
  exact (Filter.tendsto_add_atTop_iff_nat k₀).mp hmain

/-- Translation invariance of Bochner integrals, in the `y − c` form (cf.
`integral_toLp_trans_right`). -/
theorem integral_shift_neg {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [SecondCountableTopology F] (n : ℕ)
    (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)) ∂volume =
      ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)))
      = fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + (-c))) from by
      funext y; rw [sub_eq_add_neg]]
  exact integral_toLp_trans_right n (-c) g hg

/-- Translation invariance of Lebesgue integrals, in the `y − c` form. -/
theorem lintegral_shift_neg (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)) ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) - c)))
      = fun y : EuclideanSpace ℝ (Fin n) => g (WithLp.toLp 2 ((y : Fin n → ℝ) + (-c))) from by
      funext y; rw [sub_eq_add_neg]]
  exact lintegral_toLp_trans_right n (-c) g hg

/-- Lebesgue mass of the mollifier: `∫⁻ ψ_σ = 1`. -/
theorem lintegral_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    ∫⁻ u : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (mollifier n C hC σ hσ u) ∂volume = 1 := by
  classical
  -- the pointwise ofReal-split, typed (the ∫⁻ keeps the opaque mollifier)
  have hpt : ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC σ hσ u)
        = ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          ENNReal.ofReal (multivariateGaussianPDF n 0 C hC
            (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))) := by
    intro u
    simp only [mollifier]
    exact ENNReal.ofReal_mul (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n)
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- the scaling transport: ∫⁻ (ofReal ∘ φ_C ∘ (·/σ)) ∂volume = (σ^n) • ∫⁻ (ofReal ∘ φ_C)
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hTapp : ∀ u : EuclideanSpace ℝ (Fin n),
      T u = WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)) :=
    fun u => toEuclideanLin_smul_one n ((σ : ℝ)⁻¹) u
  have hFmeas' : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC z)) :=
    Measurable.ennreal_ofReal (measurable_multivariateGaussianPDF n 0 C hC)
  have hLdet : (LinearMap.det T) = (σ : ℝ)⁻¹ ^ n := by
    show (LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
      ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)))) = (σ : ℝ)⁻¹ ^ n
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
  have hLne : (LinearMap.det T) ≠ 0 := by
    rw [hLdet]
    exact pow_ne_zero n (ne_of_gt (inv_pos.mpr hσ))
  have hLabs : ENNReal.ofReal |(LinearMap.det T)⁻¹| = ENNReal.ofReal (σ ^ n) := by
    rw [hLdet, inv_pow, inv_inv, abs_of_pos (pow_pos hσ n)]
  have hptr : (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (a : Fin n → ℝ)))))
    = fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) := by
    funext a; rw [hTapp]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall (funext_iff.mp hptr))]
  have hFmeas : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a))) :=
    hFmeas'.comp (by fun_prop : Measurable T)
  have htrans : ∫⁻ a : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) ∂volume
    = ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) ∂(Measure.map T volume) :=
    (MeasureTheory.lintegral_map hFmeas' (by fun_prop : Measurable T)).symm
  have hφint : MeasureTheory.Integrable (multivariateGaussianPDF n 0 C hC) volume :=
    integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC)
  have hφnn : 0 ≤ᵐ[volume] multivariateGaussianPDF n 0 C hC :=
    Filter.Eventually.of_forall fun x => le_of_lt (multivariateGaussianPDF_pos n 0 C hC x)
  have hφlint : ∫⁻ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) ∂volume = 1 := by
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
  have hd : mollifier n C hC σ hσ u = (σ : ℝ)⁻¹ ^ n *
      multivariateGaussianPDF n 0 C hC (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) := rfl
  rw [hd, mollifier]
  have h0 : ((0 : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = 0 := rfl
  rw [h0, smul_zero]
  refine le_trans (mul_le_mul_of_nonneg_left (multivariateGaussianPDF_le_const n 0 C hC _)
    (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n)
  rw [multivariateGaussianPDF_eq n 0 C hC]
  simp

/-- The mollifier is integrable (measurable, with Lebesgue mass one). -/
theorem mollifier_integrable (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ)
    (hσ : 0 < σ) : MeasureTheory.Integrable (mollifier n C hC σ hσ) volume := by
  have hψmeas : Measurable (mollifier n C hC σ hσ) := by
    show Measurable (fun u : EuclideanSpace ℝ (Fin n) => (σ : ℝ)⁻¹ ^ n *
      multivariateGaussianPDF n 0 C hC
        (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
    exact ((measurable_multivariateGaussianPDF n 0 C hC).comp
      (by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul ((σ : ℝ)⁻¹ ^ n)
  have hnn : 0 ≤ᵐ[volume] mollifier n C hC σ hσ :=
    Filter.Eventually.of_forall fun u => mollifier_nonneg n C hC σ hσ u
  refine ⟨hψmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn, lintegral_mollifier n C hC σ hσ]
  exact ENNReal.one_lt_top

/-- The first moment of the mollifier in Lebesgue form:
`∫⁻ ψ_σ(u) * ‖u‖ₑ = ofReal (σ * M_φ)` where `M_φ = ∫ ‖v‖ * φ_C v ∂volume`, proved by the same
linear-change-of-variables transport as `lintegral_mollifier`. -/
theorem lintegral_mollifier_mul_norm (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) :
    ∫⁻ u : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC σ hσ u) * ENNReal.ofReal ‖u‖ ∂volume
      = ENNReal.ofReal (σ * ∫ v : EuclideanSpace ℝ (Fin n),
          ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
  classical
  -- the pointwise ofReal-split, typed (the ∫⁻ keeps the opaque mollifier)
  have hpt : ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC σ hσ u) * ENNReal.ofReal ‖u‖
      = ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
        (ENNReal.ofReal (multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))) * ENNReal.ofReal ‖u‖) := by
    intro u
    simp only [mollifier]
    rw [ENNReal.ofReal_mul (pow_nonneg (le_of_lt (inv_pos.mpr hσ)) n), mul_assoc]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- the scaling transport
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))
  have hTapp : ∀ u : EuclideanSpace ℝ (Fin n),
      T u = WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)) :=
    fun u => toEuclideanLin_smul_one n ((σ : ℝ)⁻¹) u
  have hnormT : ∀ u : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal ‖u‖ = ENNReal.ofReal σ * ENNReal.ofReal ‖T u‖ := by
    intro u
    rw [← ENNReal.ofReal_mul (le_of_lt hσ)]
    congr 1
    rw [hTapp u,
      show (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))) = (σ : ℝ)⁻¹ • u from rfl,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ),
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hσ), one_mul]
  have hptr : (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
        (ENNReal.ofReal (multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (a : Fin n → ℝ)))) * ENNReal.ofReal ‖a‖))
    = fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
          (ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) *
            ENNReal.ofReal ‖T a‖) := by
    funext a
    rw [← hTapp, hnormT a]
    ring
  rw [lintegral_congr_ae (Filter.Eventually.of_forall (funext_iff.mp hptr))]
  have hGmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC z) * ENNReal.ofReal ‖z‖) :=
    (Measurable.ennreal_ofReal (measurable_multivariateGaussianPDF n 0 C hC)).mul
      (Measurable.ennreal_ofReal continuous_norm.measurable)
  have hGTmeas : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) * ENNReal.ofReal ‖T a‖) :=
    hGmeas.comp (by fun_prop : Measurable T)
  rw [lintegral_const_mul (ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n)) hGTmeas]
  -- the transport of ∫⁻ G̃ (T a) to ∫⁻ G̃ y
  have htrans : ∫⁻ a : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC (T a)) * ENNReal.ofReal ‖T a‖ ∂volume
    = ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) * ENNReal.ofReal ‖y‖
          ∂(Measure.map T volume) :=
    (MeasureTheory.lintegral_map hGmeas (by fun_prop : Measurable T)).symm
  have hLdet : (LinearMap.det T) = (σ : ℝ)⁻¹ ^ n := by
    show (LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n)
      ((σ : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)))) = (σ : ℝ)⁻¹ ^ n
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin, Matrix.det_smul,
      Matrix.det_one, Fintype.card_fin, mul_one]
  have hLne : (LinearMap.det T) ≠ 0 := by
    rw [hLdet]
    exact pow_ne_zero n (ne_of_gt (inv_pos.mpr hσ))
  have hLabs : ENNReal.ofReal |(LinearMap.det T)⁻¹| = ENNReal.ofReal (σ ^ n) := by
    rw [hLdet, inv_pow, inv_inv, abs_of_pos (pow_pos hσ n)]
  have hMoφint : MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ * multivariateGaussianPDF n 0 C hC v) volume :=
    integrable_norm_mul_gaussianPDF_center n C hC
  have hMoφnn : 0 ≤ᵐ[volume] (fun v : EuclideanSpace ℝ (Fin n) =>
      ‖v‖ * multivariateGaussianPDF n 0 C hC v) :=
    Filter.Eventually.of_forall fun v => mul_nonneg (norm_nonneg v)
      (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  have hGval : ∫⁻ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (multivariateGaussianPDF n 0 C hC y) * ENNReal.ofReal ‖y‖ ∂volume
    = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ * multivariateGaussianPDF n 0 C hC y ∂volume) := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [mul_comm, ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hMoφint hMoφnn]
  rw [htrans, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLabs,
    lintegral_smul_measure, hGval, smul_eq_mul]
  -- goal: (sₑ · σ⁻ⁿₑ) * (σⁿₑ · Mₑ) = ofReal (σ * M)
  have hMnn : 0 ≤ ∫ v : EuclideanSpace ℝ (Fin n),
      ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume :=
    MeasureTheory.integral_nonneg fun v => mul_nonneg (norm_nonneg v)
      (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
  have hcancel : ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) * ENNReal.ofReal (σ ^ n) = 1 := by
    rw [inv_pow, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr (pow_pos hσ n))),
      inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hσ)), ENNReal.ofReal_one]
  rw [ENNReal.ofReal_mul (le_of_lt hσ)]
  have hfin : ENNReal.ofReal σ * ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n) *
      (ENNReal.ofReal (σ ^ n) * ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ * multivariateGaussianPDF n 0 C hC y))
    = ENNReal.ofReal σ * ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ * multivariateGaussianPDF n 0 C hC y) := by
    rw [mul_assoc,
      ← mul_assoc (ENNReal.ofReal ((σ : ℝ)⁻¹ ^ n)) (ENNReal.ofReal (σ ^ n))
        (ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n),
          ‖y‖ * multivariateGaussianPDF n 0 C hC y)),
      hcancel, one_mul]
  rw [hfin]

/-- The Gaussian-smoothed prior is a pdf (nonnegative with mass 1). -/
public theorem isPdf_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hpdf : IsPdf f)
    (hf : Continuous f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    IsPdf (gaussSmoothed n f C hC σ hσ) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  have hψmeas' : Measurable (mollifier n C hC σ hσ) := by
    show Measurable (fun u : EuclideanSpace ℝ (Fin n) => (σ : ℝ)⁻¹ ^ n *
      multivariateGaussianPDF n 0 C hC
        (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
    exact ((measurable_multivariateGaussianPDF n 0 C hC).comp
      (by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul ((σ : ℝ)⁻¹ ^ n)
  have hgnonneg : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ ∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC σ hσ u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume :=
    fun x => MeasureTheory.integral_nonneg
      (fun u => mul_nonneg (mollifier_nonneg n C hC σ hσ u) (hf0 _))
  refine ⟨?_, ?_⟩
  · exact hgnonneg
  · -- the mass via Fubini over the pair (x, u)
    have hflint : ∫⁻ x : EuclideanSpace ℝ (Fin n), ‖f x‖ₑ ∂volume = 1 := by
      have hpt : ∀ x : EuclideanSpace ℝ (Fin n), ‖f x‖ₑ = ENNReal.ofReal (f x) :=
        fun x => Real.enorm_eq_ofReal (hf0 x)
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt),
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi
          (Filter.Eventually.of_forall hf0), hpdf.2]
      exact ENNReal.ofReal_one
    have hshift : ∀ u : EuclideanSpace ℝ (Fin n),
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ ∂volume = 1 := fun u => by
      rw [lintegral_shift_neg n (u : Fin n → ℝ) (fun x => ‖f x‖ₑ) hfm.enorm]
      exact hflint
    -- the joint integrand on the pair (x, u)
    have hΦmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC σ hσ p.1 *
          f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) :=
      ((hψmeas'.comp (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => p.1)).mul
        (hfm.comp (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
    -- joint integrability: Tonelli with the pair's FIRST coordinate carrying ψ,
    -- so the inner ∫⁻_x sees ψ as a constant and is transportable
    have hΦint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC σ hσ p.1 *
          f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))
        (volume.prod volume) := by
      refine ⟨?_, ?_⟩
      · exact ((hψmeas'.comp (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) => p.1)).mul
          (hfm.comp (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))).aestronglyMeasurable
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (MeasureTheory.lintegral_prod_le _) ?_
      -- the inner ∫⁻ transport: the ∫⁻_y integrand becomes the ψ·‖f‖ₑ split form
      have hpt : ∀ x y : EuclideanSpace ℝ (Fin n),
          ‖(fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              mollifier n C hC σ hσ q.1 *
                f (WithLp.toLp 2 ((q.2 : Fin n → ℝ) - (q.1 : Fin n → ℝ)))) (x, y)‖ₑ
          = ENNReal.ofReal (mollifier n C hC σ hσ x) *
              ENNReal.ofReal (f (WithLp.toLp 2
                ((y : Fin n → ℝ) - (x : Fin n → ℝ)))) := by
        intro x y
        rw [Real.enorm_eq_ofReal (mul_nonneg (mollifier_nonneg n C hC σ hσ x)
          (hf0 (WithLp.toLp 2 ((y : Fin n → ℝ) - (x : Fin n → ℝ))))),
          ENNReal.ofReal_mul (mollifier_nonneg n C hC σ hσ x)]
      rw [lintegral_congr_ae (Filter.Eventually.of_forall fun x => by
        exact lintegral_congr_ae (Filter.Eventually.of_forall (hpt x)))]
      -- the inner ∫⁻: ofReal (ψ a) · ofReal (f(·−a)) = ofReal (ψ a) · ‖f‖ₑ-form,
      --   then the transportable shift
      have hinner : ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC σ hσ a) *
              ENNReal.ofReal (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))) ∂volume
          = ENNReal.ofReal (mollifier n C hC σ hσ a) := by
        intro a
        have hmeas' : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
            ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) := by
          have heq : (fun b : EuclideanSpace ℝ (Fin n) =>
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)
            = (fun x => ‖f x‖ₑ) ∘ fun b : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) := rfl
          rw [heq]
          exact hfm.enorm.comp (by fun_prop)
        have hfpt : ∀ b : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC σ hσ a) *
              ENNReal.ofReal (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))
            = ENNReal.ofReal (mollifier n C hC σ hσ a) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ := by
          intro b
          rw [(Real.enorm_eq_ofReal (hf0 _)).symm]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hfpt),
          MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC σ hσ a))
            hmeas', hshift a, mul_one]
      rw [lintegral_congr_ae (Filter.Eventually.of_forall hinner), lintegral_mollifier]
      exact ENNReal.one_lt_top
    -- the mass: ∫_x gaussSmoothed x dx = ∫_u ψ(u)·(∫_x f(x−u) dx) du = ∫_u ψ(u) du = 1
    have hAint' : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC σ hσ p.2 *
          f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) (volume.prod volume) := by
      have hmp : MeasureTheory.MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
          (volume.prod volume) (volume.prod volume) :=
        MeasureTheory.Measure.measurePreserving_swap
      exact (hmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint
    have hshiftmass : ∀ u : EuclideanSpace ℝ (Fin n), ∫ x : EuclideanSpace ℝ (Fin n),
        f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume = 1 := by
      intro u
      rw [integral_shift_neg n (u : Fin n → ℝ) f hfi.1]
      exact hpdf.2
    show ∫ x : EuclideanSpace ℝ (Fin n),
        ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC σ hσ u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume ∂volume = 1
    rw [← MeasureTheory.integral_prod (f := fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => mollifier n C hC σ hσ p.2 *
        f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) hAint',
      ← MeasureTheory.integral_prod_swap (f := fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC σ hσ p.2 *
          f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))))]
    -- the swapped-pair congr: the projs reduce (z.swap.2 = z.1, z.swap.1 = z.2),
    -- turning the integrand into the Φ form with ψ on the FIRST coordinate
    have hcongr : ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        mollifier n C hC σ hσ z.swap.2 *
          f (WithLp.toLp 2 ((z.swap.1 : Fin n → ℝ) - (z.swap.2 : Fin n → ℝ)))
        = mollifier n C hC σ hσ z.1 *
          f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) := by
      intro z
      simp [Prod.swap]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      MeasureTheory.integral_prod
        (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC σ hσ p.1 *
            f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))
        (μ := volume) (ν := volume) hΦint,
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [MeasureTheory.integral_const_mul (mollifier n C hC σ hσ x), hshiftmass x,
          mul_one]),
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
public theorem weightedModulus_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (u : EuclideanSpace ℝ (Fin n)) :
    weightedModulus n f u
      ≤ (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  show ∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume
    ≤ (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖)
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  have heqw : (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      = fun x : EuclideanSpace ℝ (Fin n) => f x + ‖x‖ * f x := by
    funext x; ring
  have hwfint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      volume := by
    rw [heqw]; exact hfi.add hfmom
  have hmass : ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume
      = 1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume := by
    rw [heqw, MeasureTheory.integral_add hfi hfmom, hpdf.2]
  -- the shifted weighted mass, as an integral of the translated integrand
  have hfuadd : (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
      = fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) +
            ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖) *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) := by
    funext x
    have heqx : (WithLp.toLp 2 ((u : Fin n → ℝ) +
        ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) = x := by
      rw [add_sub_cancel, WithLp.toLp_ofLp]
    rw [show (1 + ‖x‖) = 1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) +
        ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ from
      congrArg (fun w : EuclideanSpace ℝ (Fin n) => 1 + ‖w‖) heqx.symm]
  have hfuM : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z) := by
    fun_prop
  have hfuin : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z) volume := by
    refine MeasureTheory.Integrable.mono' (hwfint.mul_const (1 + ‖u‖)) ?_ ?_
    · exact hfuM.aestronglyMeasurable
    · filter_upwards with z
      show ‖(1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z‖
        ≤ (1 + ‖z‖) * f z * (1 + ‖u‖)
      have hadd : (WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))) = u + z := rfl
      rw [hadd, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
        linarith [norm_nonneg (u + z)]) (hf0 z))]
      have htri : 1 + ‖u + z‖ ≤ (1 + ‖z‖) * (1 + ‖u‖) := by
        have h := norm_add_le u z
        have hexp : (1 + ‖z‖) * (1 + ‖u‖) = 1 + ‖u‖ + ‖z‖ + ‖z‖ * ‖u‖ := by ring
        rw [hexp]
        linarith [h, mul_nonneg (norm_nonneg z) (norm_nonneg u), norm_nonneg u,
          norm_nonneg z]
      calc (1 + ‖u + z‖) * f z
          ≤ (1 + ‖z‖) * (1 + ‖u‖) * f z :=
            mul_le_mul_of_nonneg_right htri (hf0 z)
        _ = (1 + ‖z‖) * f z * (1 + ‖u‖) := by ring
  have hshift1 : ∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume
      = ∫ y : EuclideanSpace ℝ (Fin n),
          (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (y : Fin n → ℝ))‖) * f y ∂volume := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      fun x => congrFun hfuadd x),
      integral_shift_neg n (u : Fin n → ℝ)
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z)
        hfuM.aestronglyMeasurable]
  have hb1 : ∫ y : EuclideanSpace ℝ (Fin n),
      (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (y : Fin n → ℝ))‖) * f y ∂volume
      ≤ (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hR : ∫ y : EuclideanSpace ℝ (Fin n), (1 + ‖y‖) * f y * (1 + ‖u‖) ∂volume
        = (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
      rw [MeasureTheory.integral_mul_const (1 + ‖u‖), hmass, mul_comm]
    refine le_trans (MeasureTheory.integral_mono hfuin
      (hwfint.mul_const (1 + ‖u‖))
      (fun z => by
        show (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z
          ≤ (1 + ‖z‖) * f z * (1 + ‖u‖)
        have hadd : (WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))) = u + z := rfl
        rw [hadd]
        have htri : 1 + ‖u + z‖ ≤ (1 + ‖z‖) * (1 + ‖u‖) := by
          have h := norm_add_le u z
          have hexp : (1 + ‖z‖) * (1 + ‖u‖) = 1 + ‖u‖ + ‖z‖ + ‖z‖ * ‖u‖ := by ring
          rw [hexp]
          linarith [h, mul_nonneg (norm_nonneg z) (norm_nonneg u), norm_nonneg u,
            norm_nonneg z]
        calc (1 + ‖u + z‖) * f z
            ≤ (1 + ‖z‖) * (1 + ‖u‖) * f z := mul_le_mul_of_nonneg_right htri (hf0 z)
          _ = (1 + ‖z‖) * f z * (1 + ‖u‖) := by ring)) (le_of_eq hR)
  -- |f (x−u) − f x| ≤ f (x−u) + f x, so the modulus splits
  have hsplit : ∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume
      ≤ ∫ x : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume
        + ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume := by
    have hA : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) volume := by
      rw [hfuadd]
      exact integrable_toLp_shift n (-(u : Fin n → ℝ))
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖WithLp.toLp 2 ((u : Fin n → ℝ) + (z : Fin n → ℝ))‖) * f z)
        hfuin hfuM
    have hintAB : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))
          + (1 + ‖x‖) * f x) volume := hA.add hwfint
    have hLint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) volume := by
      refine MeasureTheory.Integrable.mono hintAB ?_ ?_
      · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)
            ).aestronglyMeasurable
      · filter_upwards with x
        have habs : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|
            ≤ |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))| + |f x| :=
          abs_sub _ _
        rw [abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 x)] at habs
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|),
          abs_of_nonneg (add_nonneg
            (mul_nonneg (by linarith [norm_nonneg x]) (hf0 _))
            (hwnonneg x))]
        exact le_trans (mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x]))
          (le_of_eq (mul_add _ _ _))
    refine le_trans (MeasureTheory.integral_mono hLint hintAB (fun x => by
      have habs : |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|
          ≤ |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))| + |f x| :=
        abs_sub _ _
      rw [abs_of_nonneg (hf0 _), abs_of_nonneg (hf0 x)] at habs
      have hstep1 : (1 + ‖x‖) *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|
          ≤ (1 + ‖x‖) * (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) + f x) :=
        mul_le_mul_of_nonneg_left habs (by linarith [norm_nonneg x])
      exact le_trans hstep1 (le_of_eq (mul_add _ _ _)))) (le_of_eq (MeasureTheory.integral_add' hA hwfint))
  refine le_trans hsplit ?_
  rw [hshift1, hmass]
  refine le_trans (add_le_add hb1 (le_refl _)) ?_
  have hring : (1 + ‖u‖) * (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)
      + (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)
      = (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖u‖) := by
    ring
  exact le_of_eq hring

/-- The weighted translation modulus is a.e.-measurable (it is the `x`-marginal integral of
the measurable joint function `(u, x) ↦ (1 + ‖x‖) * |f (x − u) − f x|`). -/
public theorem aemeasurable_weightedModulus (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) :
    AEMeasurable (weightedModulus n f) volume := by
  have hKmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := by
    fun_prop
  exact (hKmeas.stronglyMeasurable.integral_prod_right').aemeasurable

/-- Measurability of the mollifier. -/
public theorem measurable_mollifier (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℝ) (hσ : 0 < σ) : Measurable (mollifier n C hC σ hσ) := by
  show Measurable (fun u : EuclideanSpace ℝ (Fin n) => (σ : ℝ)⁻¹ ^ n *
    multivariateGaussianPDF n 0 C hC
      (WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ))))
  exact ((measurable_multivariateGaussianPDF n 0 C hC).comp
    (by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 ((σ : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul ((σ : ℝ)⁻¹ ^ n)

/-- Measurability of the ψ-weighted joint difference integrand (ψ on the first
coordinate). -/
public theorem measurable_joint_first (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
  have hψmeas := measurable_mollifier n C hC s hs
  fun_prop

/-- **Step A of the smoothing theorem**: the pointwise smoothing identity
`|f x − gaussSmoothed x| ≤ ∫ ψ_σ(u) |f (x − u) − f x| du`, via `∫ ψ_σ = 1`, the
subtraction identity and `|∫ g| ≤ ∫ |g|`; per-x integrability of the two subtracted
integrand factors follows from the reflection `u ↦ −u` (measure-preserving) and the
peak domination `ψ_σ(u) ≤ ψ_σ(0)`. -/
public theorem stepA_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    |f x - gaussSmoothed n f C hC s hs x|
    ≤ ∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC s hs u *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume := by
  classical
  have hnegmp : MeasureTheory.MeasurePreserving (fun u : EuclideanSpace ℝ (Fin n) => -u)
      volume volume := Measure.measurePreserving_neg _
  have hψint := mollifier_integrable n C hC s hs
  have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u :=
    fun u => mollifier_nonneg n C hC s hs u
  have hψ0le : ∀ u : EuclideanSpace ℝ (Fin n),
      mollifier n C hC s hs u ≤ mollifier n C hC s hs 0 := mollifier_le_zero n C hC s hs
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  have hψmeas := measurable_mollifier n C hC s hs
  have h2 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC s hs u * f x) volume := hψint.mul_const (f x)
  have hshifted : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ)))) volume :=
    integrable_toLp_shift n (x : Fin n → ℝ) f hfi hfm
  have hcomp : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
      (fun z : EuclideanSpace ℝ (Fin n) =>
        f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ)))) (-u)) volume :=
    (hnegmp.integrable_comp hshifted.1).mpr hshifted
  have h3 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC s hs u *
        f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) volume := by
    have hcomp' : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
        f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) volume := by
      refine hcomp.congr' ?_ ?_
      · exact ((by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
      · filter_upwards with u
        show ‖f (WithLp.toLp 2 (((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) +
            (x : Fin n → ℝ)))‖
          = ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
        congr 1
        simp only [WithLp.ofLp_neg]
        rw [add_comm, ← sub_eq_add_neg]
    refine MeasureTheory.Integrable.mono' (hcomp'.mul_const (mollifier n C hC s hs 0)) ?_ ?_
    · exact ((by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
    · filter_upwards with u
      show ‖mollifier n C hC s hs u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
        ≤ f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) * mollifier n C hC s hs 0
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψpos u), abs_of_nonneg (hf0 _)]
      exact le_trans (mul_le_mul_of_nonneg_right (hψ0le u) (hf0 _))
        (le_of_eq (mul_comm _ _))
  have h1 : f x = ∫ u : EuclideanSpace ℝ (Fin n),
      mollifier n C hC s hs u * f x ∂volume := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      fun u => mul_comm (mollifier n C hC s hs u) (f x)),
      MeasureTheory.integral_const_mul (f x), integral_mollifier n C hC s hs, mul_one]
  have hsub : f x - gaussSmoothed n f C hC s hs x
      = ∫ u : EuclideanSpace ℝ (Fin n),
          mollifier n C hC s hs u *
            (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume := by
    conv_lhs => rw [h1]
    have hgs : gaussSmoothed n f C hC s hs x = ∫ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC s hs u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume := rfl
    rw [hgs, ← MeasureTheory.integral_sub h2 h3]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show mollifier n C hC s hs u * f x -
          mollifier n C hC s hs u *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))
      = mollifier n C hC s hs u *
          (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
    rw [mul_sub]
  rw [hsub]
  refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
    rw [abs_mul, abs_of_nonneg (hψpos u),
      abs_sub_comm (f x) (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))])]

/-- **Step B of the smoothing theorem**: joint integrability of the ψ-weighted
difference integrand, ψ on the first coordinate (the `(T)`-lemma's Tonelli
orientation), via the ∫⁻ Tonelli bound with the mollifier's first moment. -/
public theorem integrable_joint_first (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
        (volume.prod volume) := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u :=
    fun u => mollifier_nonneg n C hC s hs u
  have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => Real.enorm_eq_ofReal (hf0 y)),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi
        (Filter.Eventually.of_forall hf0), hpdf.2, ENNReal.ofReal_one]
  have hMoe : ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume
      = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
  -- (ψ on the first coordinate, the `(T)`-lemma's Tonelli orientation)
  have hψmeas := measurable_mollifier n C hC s hs
  have hΦmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
    fun_prop
  have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
    le_trans (by norm_num : (0:ENNReal) ≤ ENNReal.ofReal 0)
      (ENNReal.ofReal_le_ofReal hx)
  have hψe : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
    Measurable.ennreal_ofReal (by fun_prop : Measurable fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1)
  have hwe : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (1 + ‖p.2‖)) :=
    Measurable.ennreal_ofReal (by fun_prop : Measurable fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖p.2‖)
  have hfa : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) :=
    hfm.enorm.comp (by fun_prop : Measurable fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))
  have hfb : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ‖f p.2‖ₑ) :=
    hfm.enorm.comp (by fun_prop : Measurable fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2)
  have hP1meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs p.1) *
        (ENNReal.ofReal (1 + ‖p.2‖) *
          ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)) :=
    hψe.mul (hwe.mul hfa)
  have hP2meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs p.1) *
        (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) :=
    hψe.mul (hwe.mul hfb)
  have hΦnn : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      0 ≤ mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := fun p =>
    mul_nonneg (hψpos p.1) (mul_nonneg (by linarith [norm_nonneg p.2]) (abs_nonneg _))
  -- the ∫⁻ pointwise split
  have hpt : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
      ≤ ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
        + ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
    intro p
    have hw0 : 0 ≤ (1:ℝ) + ‖p.2‖ := by linarith [norm_nonneg p.2]
    have hab : |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|
        ≤ |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))| + |f p.2| :=
      abs_sub _ _
    have hstep : ENNReal.ofReal ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)
        ≤ ENNReal.ofReal (1 + ‖p.2‖) *
          (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ) := by
      rw [ENNReal.ofReal_mul hw0]
      refine mul_le_mul_of_nonneg_left ?_ (hofnn _ hw0)
      refine le_trans (ENNReal.ofReal_le_ofReal hab) ?_
      rw [Real.enorm_eq_ofReal_abs (f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) -
          (p.1 : Fin n → ℝ)))), Real.enorm_eq_ofReal_abs (f p.2),
        ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    rw [ENNReal.ofReal_mul (hψpos p.1)]
    calc ENNReal.ofReal (mollifier n C hC s hs p.1) *
        ENNReal.ofReal ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)
        ≤ ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) *
              (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ +
                ‖f p.2‖ₑ)) :=
          mul_le_mul_of_nonneg_left hstep (hofnn _ (hψpos p.1))
    _ = ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
        + ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
      rw [mul_add]
      ring
  -- the weighted-marginal identity
  have hMoval : ∫⁻ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume
    = 1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hpt2 : ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
      intro y
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul,
        ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2),
      lintegral_add_left hfm.enorm _, hflint, hMoe]
  have hbnd : ∫⁻ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume < ⊤ := by
    rw [hMoval]
    exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
  -- the ψ-weighted shifted enorm marginal (piece 1)
  have hinner1 : ∀ a : EuclideanSpace ℝ (Fin n),
      ∫⁻ b : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖b‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ∂volume
        ≤ (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
    intro a
    have hbmeas : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (1 + ‖b‖) *
          ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
      (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖b‖)).mul
        (hfm.enorm.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))
    have hGmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) :=
      (Measurable.ennreal_ofReal (by fun_prop : Measurable fun z :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖z‖)).mul hfm.enorm
    have hptw : ∀ b : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) *
          (ENNReal.ofReal (1 + ‖b‖) *
            ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)
        ≤ ENNReal.ofReal (mollifier n C hC s hs a) *
          (ENNReal.ofReal (1 + ‖a‖) *
            (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) -
              (a : Fin n → ℝ))‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) := by
      intro b
      have hba : WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) = b - a := rfl
      have htri : ‖b‖ ≤ ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ + ‖a‖ := by
        rw [hba]
        calc ‖b‖ = ‖(b - a) + a‖ := by rw [sub_add_cancel]
          _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le (b - a) a
      have hle : (1:ℝ) + ‖b‖
          ≤ (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) := by
        have hexp : (1 + ‖a‖) *
              (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)
            = 1 + ‖a‖ + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖
              + ‖a‖ * ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ := by ring
        rw [hexp]
        linarith [htri, norm_nonneg a,
          mul_nonneg (norm_nonneg a)
            (norm_nonneg (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))]
      have henn : ∀ r : ℝ, 0 ≤ ‖r‖ₑ := fun r =>
        le_trans (hofnn _ (abs_nonneg r)) (le_of_eq (Real.enorm_eq_ofReal_abs r).symm)
      refine mul_le_mul_of_nonneg_left ?_ (hofnn _ (hψpos a))
      rw [← mul_assoc (ENNReal.ofReal (1 + ‖a‖)) (ENNReal.ofReal (1 +
            ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖))
          ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ,
        ← ENNReal.ofReal_mul (by linarith [norm_nonneg a] : 0 ≤ (1:ℝ) + ‖a‖)]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle)
        (henn (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
    have hbmeas2 : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (1 + ‖a‖) *
          (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) -
            (a : Fin n → ℝ))‖) *
            ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) :=
      (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖a‖)).mul
        ((Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
          EuclideanSpace ℝ (Fin n) => (1:ℝ) +
            ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)).mul
          (hfm.enorm.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
    have hshiftbmeas : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
          ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
      hGmeas.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))
    refine le_trans (MeasureTheory.lintegral_mono hptw) ?_
    rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas2,
      MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖a‖)) hshiftbmeas,
      lintegral_shift_neg n (a : Fin n → ℝ)
        (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) hGmeas,
      hMoval]
    have hring : ENNReal.ofReal (mollifier n C hC s hs a) *
        (ENNReal.ofReal (1 + ‖a‖) *
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
      = (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
        (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by ring
    rw [hring]
  have hψea : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs a)) :=
    Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
      EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
  have hsplit : ∫⁻ a : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume
    = 1 + ENNReal.ofReal (s * ∫ v : EuclideanSpace ℝ (Fin n),
        ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
    have hpt4 : ∀ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)
        = ENNReal.ofReal (mollifier n C hC s hs a)
          + ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
      intro a
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add,
        ENNReal.ofReal_one, mul_one]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4),
      lintegral_add_left hψea _,
      lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
  have hlint1 : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs p.1) *
        (ENNReal.ofReal (1 + ‖p.2‖) *
          ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
        ∂(volume.prod volume) < ⊤ := by
    rw [MeasureTheory.lintegral_prod
      (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) *
            ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ))
      hP1meas.aemeasurable]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner1) ?_
    have hpullmeas : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
      (hψea).mul (Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖a‖))
    rw [MeasureTheory.lintegral_const_mul
      (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))
      hpullmeas, hsplit]
    exact ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
      ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
  -- piece 2: the ψ-weighted unshifted enorm marginal
  have hbmeas0 : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) :=
    (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
      EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖b‖)).mul hfm.enorm
  have hinner2 : ∀ a : EuclideanSpace ℝ (Fin n),
      ∫⁻ b : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) ∂volume
        ≤ (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          ENNReal.ofReal (mollifier n C hC s hs a) := by
    intro a
    rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas0,
      hMoval]
    exact le_of_eq (mul_comm (ENNReal.ofReal (mollifier n C hC s hs a))
      (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
  have hlint2 : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs p.1) *
        (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) ∂(volume.prod volume) < ⊤ := by
    rw [MeasureTheory.lintegral_prod
      (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs p.1) *
          (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) hP2meas.aemeasurable]
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner2) ?_
    rw [MeasureTheory.lintegral_const_mul
      (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hψea,
      lintegral_mollifier n C hC s hs, mul_one]
    exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
  have hlint : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
        ∂(volume.prod volume) < ⊤ := by
    refine lt_of_le_of_lt (le_trans (MeasureTheory.lintegral_mono hpt)
      (le_of_eq (lintegral_add_left hP1meas _))) ?_
    exact (ENNReal.add_lt_top).mpr ⟨hlint1, hlint2⟩
  refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn)]
  exact hlint

/-- **Step B of the smoothing theorem**: joint integrability of the ψ-weighted
difference integrand in the x-first orientation, by the measure-preserving swap. -/
public theorem integrable_joint_second (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
          |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
        (volume.prod volume) := by
  have hfm : Measurable f := hf.measurable
  have hψmeas := measurable_mollifier n C hC s hs
  have hswapmp : MeasureTheory.MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (volume.prod volume) (volume.prod volume) :=
    MeasureTheory.Measure.measurePreserving_swap
  have hΦmeas := measurable_joint_first n f hfm C hC s hs
  have hΦint := integrable_joint_first n f hf hpdf hfmom C hC s hs
  refine ((hswapmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint).congr' ?_ ?_
  · exact ((by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n) => (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
        |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
          ).aestronglyMeasurable
  · filter_upwards with p
    show ‖mollifier n C hC s hs (p.swap).1 * ((1 + ‖(p.swap).2‖) *
        |f (WithLp.toLp 2 (((p.swap).2 : Fin n → ℝ) - ((p.swap).1 : Fin n → ℝ)))
          - f (p.swap).2|)‖
      = ‖(1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
        |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|)‖
    simp only [Prod.swap, Real.norm_eq_abs, abs_mul]
    ring

/-- **Weighted integrability of the smoothed prior**: the joint function
`(u, x) ↦ ψ_σ(u) · (1 + ‖x‖) · f (x − u)` is integrable on the product, via the
∫⁻ Tonelli bound: `w(x) ≤ (1 + ‖u‖) (1 + ‖x − u‖)`, the `x − u`-shift, and the
mollifier's first moment `∫⁻ ψ_σ(u) (1 + ‖u‖) = 1 + ofReal (σ · M_φ)`. -/
public theorem integrable_joint_smooth_prior (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
          f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
        (volume.prod volume) := by
  classical
  have hψmeas := measurable_mollifier n C hC s hs
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hfm : Measurable f := hf.measurable
  have hwnonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖x‖) * f x := fun x =>
    mul_nonneg (add_nonneg zero_le_one (norm_nonneg x)) (hf0 x)
  have heqw : (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      = fun x : EuclideanSpace ℝ (Fin n) => f x + ‖x‖ * f x := by
    funext x; ring
  have hwfint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      volume := by
    rw [heqw]; exact hfi.add hfmom
  have hwnn : 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x) :=
    Filter.Eventually.of_forall hwnonneg
  have hmass : ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * f x ∂volume
      = 1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume := by
    rw [heqw, MeasureTheory.integral_add hfi hfmom, hpdf.2]
  -- the ∫⁻ marginal identity of the weighted `f`
  have hMoval : ∫⁻ y : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume
    = 1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
      rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y =>
          Real.enorm_eq_ofReal (hf0 y)),
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi
          (Filter.Eventually.of_forall hf0), hpdf.2, ENNReal.ofReal_one]
    have hMoe : ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume
        = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
      rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => by
        rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
        ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
          (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
    have hpt2 : ∀ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
      intro y
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul,
        ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2),
      lintegral_add_left hfm.enorm _, hflint, hMoe]
  -- the mollifier's first moment
  have hψmea : ∫⁻ a : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume
    = 1 + ENNReal.ofReal (s * ∫ v : EuclideanSpace ℝ (Fin n),
        ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
    have hψea : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (mollifier n C hC s hs a)) :=
      Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
        EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
    have hpt4 : ∀ a : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)
        = ENNReal.ofReal (mollifier n C hC s hs a)
          + ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
      intro a
      rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add,
        ENNReal.ofReal_one, mul_one]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4),
      lintegral_add_left hψea _,
      lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
  -- the ∫⁻ Tonelli bound for the ψ-first joint function
  have hΦmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))))) := by
    fun_prop
  have hKnn : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      0 ≤ mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))) := fun p =>
    mul_nonneg (mollifier_nonneg n C hC s hs p.1)
      (mul_nonneg (by linarith [norm_nonneg p.2]) (hf0 _))
  refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hKnn)]
  have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
    le_trans (by norm_num : (0:ENNReal) ≤ ENNReal.ofReal 0) (ENNReal.ofReal_le_ofReal hx)
  have hψe : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
    Measurable.ennreal_ofReal (by fun_prop : Measurable fun p :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1)
  have hinner : ∀ u : EuclideanSpace ℝ (Fin n),
      ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs u * ((1 + ‖x‖) *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))) ∂volume
        ≤ (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs u) * ENNReal.ofReal (1 + ‖u‖)) := by
    intro u
    have hu : 0 ≤ (1:ℝ) + ‖u‖ := by linarith [norm_nonneg u]
    have hpsi : 0 ≤ mollifier n C hC s hs u := mollifier_nonneg n C hC s hs u
    have hxmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
          ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ) :=
      (Measurable.ennreal_ofReal (by fun_prop : Measurable fun x :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) +
          ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖)).mul
        (hfm.enorm.comp (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
    refine le_trans (MeasureTheory.lintegral_mono
      (f := fun (x : EuclideanSpace ℝ (Fin n)) =>
        ENNReal.ofReal (mollifier n C hC s hs u * ((1 + ‖x‖) *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))))
      (g := fun (x : EuclideanSpace ℝ (Fin n)) =>
        ENNReal.ofReal (mollifier n C hC s hs u) *
          (ENNReal.ofReal (1 + ‖u‖) * (ENNReal.ofReal (1 +
            ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
            ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ)))
      (fun x => ?_)) ?_
    · -- pointwise
      have hba : WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)) = x - u := rfl
      have htri : ‖x‖ ≤ ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖ + ‖u‖ := by
        rw [hba]
        calc ‖x‖ = ‖(x - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le (x - u) u
      have hle : (1:ℝ) + ‖x‖
          ≤ (1 + ‖u‖) * (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) := by
        have hexp : (1 + ‖u‖) *
              (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖)
            = 1 + ‖u‖ + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖
              + ‖u‖ * ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖ := by ring
        rw [hexp]
        linarith [htri, norm_nonneg u,
          mul_nonneg (norm_nonneg u)
            (norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))]
      have hfxnn : 0 ≤ f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) := hf0 _
      have hwnx : 0 ≤ (1:ℝ) + ‖x‖ := by linarith [norm_nonneg x]
      have hkey : ENNReal.ofReal ((1:ℝ) + ‖x‖) *
          ENNReal.ofReal (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
        ≤ ENNReal.ofReal (1 + ‖u‖) *
          (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
            ENNReal.ofReal (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))) := by
        rw [← ENNReal.ofReal_mul (by linarith [norm_nonneg (WithLp.toLp 2 ((x : Fin n → ℝ) -
            (u : Fin n → ℝ)))]: 0 ≤ (1:ℝ) + ‖WithLp.toLp 2 ((x : Fin n → ℝ) -
            (u : Fin n → ℝ))‖),
          ← ENNReal.ofReal_mul (by linarith [norm_nonneg u] : 0 ≤ (1:ℝ) + ‖u‖),
          ← ENNReal.ofReal_mul hwnx]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hle hfxnn
      simp only []
      have hsplit : ENNReal.ofReal (mollifier n C hC s hs u *
          ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))))
        = ENNReal.ofReal (mollifier n C hC s hs u) *
          ENNReal.ofReal ((1 + ‖x‖) * f (WithLp.toLp 2 ((x : Fin n → ℝ) -
            (u : Fin n → ℝ)))) := ENNReal.ofReal_mul hpsi
      rw [hsplit, ENNReal.ofReal_mul (by linarith [norm_nonneg x] : 0 ≤ (1:ℝ) + ‖x‖),
        Real.enorm_eq_ofReal hfxnn]
      exact mul_le_mul_of_nonneg_left hkey (hofnn _ hpsi)
    · -- the two const-pulls and the `x − u`-shift
      have hxfn : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖u‖) *
            (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))‖) *
              ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖ₑ)) :=
        (Measurable.ennreal_ofReal (by fun_prop : Measurable fun x :
          EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖u‖)).mul hxmeas
      rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs u)) hxfn,
        MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖u‖)) hxmeas,
        lintegral_shift_neg n (u : Fin n → ℝ)
          (fun z : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ)
          ((Measurable.ennreal_ofReal (by fun_prop : Measurable fun z :
            EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖z‖)).mul hfm.enorm),
        hMoval]
      have hring : ENNReal.ofReal (mollifier n C hC s hs u) *
          (ENNReal.ofReal (1 + ‖u‖) *
            (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
        = (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
          (ENNReal.ofReal (mollifier n C hC s hs u) * ENNReal.ofReal (1 + ‖u‖)) := by
        ring
      exact le_of_eq hring
  rw [MeasureTheory.lintegral_prod
    (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
        f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))))
      ) ((Measurable.ennreal_ofReal hΦmeas).aemeasurable)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner) ?_
  have hpullmeas : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
    (Measurable.ennreal_ofReal hψmeas).mul
      (Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
        EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖a‖))
  rw [MeasureTheory.lintegral_const_mul
    (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))
    hpullmeas, hψmea]
  exact ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
    ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)

set_option maxHeartbeats 4000000 in
/-- **Smoothing theorem**: for a continuous pdf `f` with finite first moment, the weighted L¹
distance between `f` and its Gaussian smoothing tends to `0` along every positive sequence
`σ k → 0`. This produces the `hw`-hypothesis of `cme_uniform_balls_R` for the Gaussian-smoothed
priors `fhK K = gaussSmoothed … (1/(K+1))`. -/
public theorem weighted_smoothing_tendsto_seq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef)
    (σ : ℕ → ℝ) (hσ : ∀ k, 0 < σ k) (hσ0 : Filter.Tendsto σ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k : ℕ => ∫ x : EuclideanSpace ℝ (Fin n),
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
  have hwmseq : ∀ (u : ℕ → EuclideanSpace ℝ (Fin n)),
      Filter.Tendsto u Filter.atTop (nhds 0) →
      Filter.Tendsto (fun k : ℕ => weightedModulus n f (u k)) Filter.atTop (nhds 0) :=
    fun u hu => weighted_modulus_tendsto_seq n f hf hpdf hfmom u hu
  have hwmAe := aemeasurable_weightedModulus n f hfm
  -- the Lebesgue-mass basics for `f`
  have hflint : ∫⁻ y : EuclideanSpace ℝ (Fin n), ‖f y‖ₑ ∂volume = 1 := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => Real.enorm_eq_ofReal (hf0 y)),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi
        (Filter.Eventually.of_forall hf0), hpdf.2, ENNReal.ofReal_one]
  have hMoe : ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ‖y‖ * ‖f y‖ₑ ∂volume
      = ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun y => by
      rw [Real.enorm_eq_ofReal (hf0 y), ← ENNReal.ofReal_mul (norm_nonneg y)]),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfmom
        (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg y) (hf0 y))]
  -- the per-σ chain
  have hchain : ∀ (s : ℝ) (hs : 0 < s),
      ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume
      ≤ ∫ v : EuclideanSpace ℝ (Fin n),
          multivariateGaussianPDF n 0 C hC v *
            weightedModulus n f (WithLp.toLp 2 ((s : ℝ) • (v : Fin n → ℝ))) ∂volume := by
    intro s hs
    classical
    have hψmeas : Measurable (mollifier n C hC s hs) := by
      show Measurable (fun u : EuclideanSpace ℝ (Fin n) => (s : ℝ)⁻¹ ^ n *
        multivariateGaussianPDF n 0 C hC
          (WithLp.toLp 2 ((s : ℝ)⁻¹ • (u : Fin n → ℝ))))
      exact ((measurable_multivariateGaussianPDF n 0 C hC).comp
        (by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((s : ℝ)⁻¹ • (u : Fin n → ℝ)))).const_mul ((s : ℝ)⁻¹ ^ n)
    have hψint := mollifier_integrable n C hC s hs
    have hψpos : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ mollifier n C hC s hs u :=
      fun u => mollifier_nonneg n C hC s hs u
    have hψ0le : ∀ u : EuclideanSpace ℝ (Fin n),
        mollifier n C hC s hs u ≤ mollifier n C hC s hs 0 := mollifier_le_zero n C hC s hs
    have hgsi : MeasureTheory.Integrable (gaussSmoothed n f C hC s hs) volume :=
      integrable_of_isPdf (isPdf_gaussSmoothed n f hpdf hf C hC s hs)
    -- measurability of the smoothing: the x-marginal integral of the joint function
    have hGxmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.2 *
          f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) := by
      fun_prop
    have hgsmeas : Measurable (gaussSmoothed n f C hC s hs) :=
      (hGxmeas.stronglyMeasurable.integral_prod_right').measurable
    -- the reflection is measure-preserving
    have hnegmp : MeasureTheory.MeasurePreserving (fun u : EuclideanSpace ℝ (Fin n) => -u)
        volume volume := Measure.measurePreserving_neg _
    -- Step A: the pointwise smoothing identity, via `∫ ψ = 1` and `|∫ g| ≤ ∫ |g|`
    have hstepA : ∀ x : EuclideanSpace ℝ (Fin n),
        |f x - gaussSmoothed n f C hC s hs x|
        ≤ ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x| ∂volume := by
      intro x
      have h2 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs u * f x) volume := hψint.mul_const (f x)
      have hshifted : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
          f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ)))) volume :=
        integrable_toLp_shift n (x : Fin n → ℝ) f hfi hfm
      have hcomp : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
          (fun z : EuclideanSpace ℝ (Fin n) =>
            f (WithLp.toLp 2 ((z : Fin n → ℝ) + (x : Fin n → ℝ)))) (-u)) volume :=
        (hnegmp.integrable_comp hshifted.1).mpr hshifted
      have h3 : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
          mollifier n C hC s hs u *
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) volume := by
        have hcomp' : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin n) =>
            f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) volume := by
          refine hcomp.congr' ?_ ?_
          · exact ((by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
          · filter_upwards with u
            show ‖f (WithLp.toLp 2 (((-u : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) +
                (x : Fin n → ℝ)))‖
              = ‖f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
            congr 1
            simp only [WithLp.ofLp_neg]
            rw [add_comm, ← sub_eq_add_neg]
        refine MeasureTheory.Integrable.mono' (hcomp'.mul_const (mollifier n C hC s hs 0)) ?_ ?_
        · exact ((by fun_prop : Measurable fun u : EuclideanSpace ℝ (Fin n) =>
            mollifier n C hC s hs u *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))).aestronglyMeasurable
        · filter_upwards with u
          show ‖mollifier n C hC s hs u *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))‖
            ≤ f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) * mollifier n C hC s hs 0
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψpos u), abs_of_nonneg (hf0 _)]
          exact le_trans (mul_le_mul_of_nonneg_right (hψ0le u) (hf0 _))
            (le_of_eq (mul_comm _ _))
      have h1 : f x = ∫ u : EuclideanSpace ℝ (Fin n),
          mollifier n C hC s hs u * f x ∂volume := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
          fun u => mul_comm (mollifier n C hC s hs u) (f x)),
          MeasureTheory.integral_const_mul (f x), integral_mollifier n C hC s hs, mul_one]
      have hsub : f x - gaussSmoothed n f C hC s hs x
          = ∫ u : EuclideanSpace ℝ (Fin n),
              mollifier n C hC s hs u *
                (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume := by
        conv_lhs => rw [h1]
        have hgs : gaussSmoothed n f C hC s hs x = ∫ u : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u *
              f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) ∂volume := rfl
        rw [hgs, ← MeasureTheory.integral_sub h2 h3]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show mollifier n C hC s hs u * f x -
              mollifier n C hC s hs u *
                f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))
          = mollifier n C hC s hs u *
              (f x - f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))
        rw [mul_sub]
      rw [hsub]
      refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
        rw [abs_mul, abs_of_nonneg (hψpos u),
          abs_sub_comm (f x) (f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))))])]
    -- Step B: the joint integrability of the ψ-weighted integrand, via the ∫⁻ Tonelli bound
    -- (ψ on the first coordinate, the `(T)`-lemma's Tonelli orientation)
    have hΦmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)) := by
      fun_prop
    have hΦint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
          |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
        (volume.prod volume) := by
      classical
      have hofnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ ENNReal.ofReal x := fun x hx =>
        le_trans (by norm_num : (0:ENNReal) ≤ ENNReal.ofReal 0)
          (ENNReal.ofReal_le_ofReal hx)
      have hψe : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (mollifier n C hC s hs p.1)) :=
        Measurable.ennreal_ofReal (by fun_prop : Measurable fun p :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs p.1)
      have hwe : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖p.2‖)) :=
        Measurable.ennreal_ofReal (by fun_prop : Measurable fun p :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖p.2‖)
      have hfa : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ) :=
        hfm.enorm.comp (by fun_prop : Measurable fun p :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))
      have hfb : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ‖f p.2‖ₑ) :=
        hfm.enorm.comp (by fun_prop : Measurable fun p :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2)
      have hP1meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) *
              ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)) :=
        hψe.mul (hwe.mul hfa)
      have hP2meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) :=
        hψe.mul (hwe.mul hfb)
      have hΦnn : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          0 ≤ mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
            |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|) := fun p =>
        mul_nonneg (hψpos p.1) (mul_nonneg (by linarith [norm_nonneg p.2]) (abs_nonneg _))
      -- the ∫⁻ pointwise split
      have hpt : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
            |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
          ≤ ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
            + ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
        intro p
        have hw0 : 0 ≤ (1:ℝ) + ‖p.2‖ := by linarith [norm_nonneg p.2]
        have hab : |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|
            ≤ |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))| + |f p.2| :=
          abs_sub _ _
        have hstep : ENNReal.ofReal ((1 + ‖p.2‖) *
              |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)
            ≤ ENNReal.ofReal (1 + ‖p.2‖) *
              (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ + ‖f p.2‖ₑ) := by
          rw [ENNReal.ofReal_mul hw0]
          refine mul_le_mul_of_nonneg_left ?_ (hofnn _ hw0)
          refine le_trans (ENNReal.ofReal_le_ofReal hab) ?_
          rw [Real.enorm_eq_ofReal_abs (f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) -
              (p.1 : Fin n → ℝ)))), Real.enorm_eq_ofReal_abs (f p.2),
            ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        rw [ENNReal.ofReal_mul (hψpos p.1)]
        calc ENNReal.ofReal (mollifier n C hC s hs p.1) *
            ENNReal.ofReal ((1 + ‖p.2‖) *
              |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|)
            ≤ ENNReal.ofReal (mollifier n C hC s hs p.1) *
                (ENNReal.ofReal (1 + ‖p.2‖) *
                  (‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ +
                    ‖f p.2‖ₑ)) :=
              mul_le_mul_of_nonneg_left hstep (hofnn _ (hψpos p.1))
        _ = ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
            + ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) := by
          rw [mul_add]
          ring
      -- the weighted-marginal identity
      have hMoval : ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume
        = 1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) := by
        have hpt2 : ∀ y : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ = ‖f y‖ₑ + ENNReal.ofReal ‖y‖ * ‖f y‖ₑ := by
          intro y
          rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg y), add_mul,
            ENNReal.ofReal_one, one_mul]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt2),
          lintegral_add_left hfm.enorm _, hflint, hMoe]
      have hbnd : ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (1 + ‖y‖) * ‖f y‖ₑ ∂volume < ⊤ := by
        rw [hMoval]
        exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
      -- the ψ-weighted shifted enorm marginal (piece 1)
      have hinner1 : ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖b‖) *
                  ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) ∂volume
            ≤ (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
              (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by
        intro a
        have hbmeas : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖b‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
          (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
            EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖b‖)).mul
            (hfm.enorm.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))
        have hGmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) :=
          (Measurable.ennreal_ofReal (by fun_prop : Measurable fun z :
            EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖z‖)).mul hfm.enorm
        have hptw : ∀ b : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs a) *
              (ENNReal.ofReal (1 + ‖b‖) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)
            ≤ ENNReal.ofReal (mollifier n C hC s hs a) *
              (ENNReal.ofReal (1 + ‖a‖) *
                (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) -
                  (a : Fin n → ℝ))‖) *
                  ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) := by
          intro b
          have hba : WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)) = b - a := rfl
          have htri : ‖b‖ ≤ ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ + ‖a‖ := by
            rw [hba]
            calc ‖b‖ = ‖(b - a) + a‖ := by rw [sub_add_cancel]
              _ ≤ ‖b - a‖ + ‖a‖ := norm_add_le (b - a) a
          have hle : (1:ℝ) + ‖b‖
              ≤ (1 + ‖a‖) * (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) := by
            have hexp : (1 + ‖a‖) *
                  (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)
                = 1 + ‖a‖ + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖
                  + ‖a‖ * ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖ := by ring
            rw [hexp]
            linarith [htri, norm_nonneg a,
              mul_nonneg (norm_nonneg a)
                (norm_nonneg (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))))]
          have henn : ∀ r : ℝ, 0 ≤ ‖r‖ₑ := fun r =>
            le_trans (hofnn _ (abs_nonneg r)) (le_of_eq (Real.enorm_eq_ofReal_abs r).symm)
          refine mul_le_mul_of_nonneg_left ?_ (hofnn _ (hψpos a))
          rw [← mul_assoc (ENNReal.ofReal (1 + ‖a‖)) (ENNReal.ofReal (1 +
                ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖))
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ,
            ← ENNReal.ofReal_mul (by linarith [norm_nonneg a] : 0 ≤ (1:ℝ) + ‖a‖)]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle)
            (henn (f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
        have hbmeas2 : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖a‖) *
              (ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) -
                (a : Fin n → ℝ))‖) *
                ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ)) :=
          (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
            EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖a‖)).mul
            ((Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
              EuclideanSpace ℝ (Fin n) => (1:ℝ) +
                ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖)).mul
              (hfm.enorm.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
                WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))))
        have hshiftbmeas : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (1 + ‖WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ))‖) *
              ‖f (WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))‖ₑ) :=
          hGmeas.comp (by fun_prop : Measurable fun b : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 ((b : Fin n → ℝ) - (a : Fin n → ℝ)))
        refine le_trans (MeasureTheory.lintegral_mono hptw) ?_
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas2,
          MeasureTheory.lintegral_const_mul (ENNReal.ofReal (1 + ‖a‖)) hshiftbmeas,
          lintegral_shift_neg n (a : Fin n → ℝ)
            (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (1 + ‖z‖) * ‖f z‖ₑ) hGmeas,
          hMoval]
        have hring : ENNReal.ofReal (mollifier n C hC s hs a) *
            (ENNReal.ofReal (1 + ‖a‖) *
              (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
          = (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
            (ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) := by ring
        rw [hring]
      have hψea : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (mollifier n C hC s hs a)) :=
        Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
          EuclideanSpace ℝ (Fin n) => mollifier n C hC s hs a)
      have hsplit : ∫⁻ a : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖) ∂volume
        = 1 + ENNReal.ofReal (s * ∫ v : EuclideanSpace ℝ (Fin n),
            ‖v‖ * multivariateGaussianPDF n 0 C hC v ∂volume) := by
        have hpt4 : ∀ a : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)
            = ENNReal.ofReal (mollifier n C hC s hs a)
              + ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal ‖a‖ := by
          intro a
          rw [ENNReal.ofReal_add (by norm_num) (norm_nonneg a), mul_add,
            ENNReal.ofReal_one, mul_one]
        rw [lintegral_congr_ae (Filter.Eventually.of_forall hpt4),
          lintegral_add_left hψea _,
          lintegral_mollifier n C hC s hs, lintegral_mollifier_mul_norm n C hC s hs]
      have hlint1 : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) *
              ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ)
            ∂(volume.prod volume) < ⊤ := by
        rw [MeasureTheory.lintegral_prod
          (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) *
                ‖f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ)))‖ₑ))
          hP1meas.aemeasurable]
        refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner1) ?_
        have hpullmeas : Measurable (fun a : EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs a) * ENNReal.ofReal (1 + ‖a‖)) :=
          (hψea).mul (Measurable.ennreal_ofReal (by fun_prop : Measurable fun a :
            EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖a‖))
        rw [MeasureTheory.lintegral_const_mul
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume))
          hpullmeas, hsplit]
        exact ENNReal.mul_lt_top ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
          ((ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩)
      -- piece 2: the ψ-weighted unshifted enorm marginal
      have hbmeas0 : Measurable (fun b : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) :=
        (Measurable.ennreal_ofReal (by fun_prop : Measurable fun b :
          EuclideanSpace ℝ (Fin n) => (1:ℝ) + ‖b‖)).mul hfm.enorm
      have hinner2 : ∀ a : EuclideanSpace ℝ (Fin n),
          ∫⁻ b : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal (mollifier n C hC s hs a) *
                (ENNReal.ofReal (1 + ‖b‖) * ‖f b‖ₑ) ∂volume
            ≤ (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) *
              ENNReal.ofReal (mollifier n C hC s hs a) := by
        intro a
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (mollifier n C hC s hs a)) hbmeas0,
          hMoval]
        exact le_of_eq (mul_comm (ENNReal.ofReal (mollifier n C hC s hs a))
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)))
      have hlint2 : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs p.1) *
            (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ) ∂(volume.prod volume) < ⊤ := by
        rw [MeasureTheory.lintegral_prod
          (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            ENNReal.ofReal (mollifier n C hC s hs p.1) *
              (ENNReal.ofReal (1 + ‖p.2‖) * ‖f p.2‖ₑ)) hP2meas.aemeasurable]
        refine lt_of_le_of_lt (MeasureTheory.lintegral_mono hinner2) ?_
        rw [MeasureTheory.lintegral_const_mul
          (1 + ENNReal.ofReal (∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) hψea,
          lintegral_mollifier n C hC s hs, mul_one]
        exact (ENNReal.add_lt_top).mpr ⟨ENNReal.one_lt_top, by simp⟩
      have hlint : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
            |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
            ∂(volume.prod volume) < ⊤ := by
        refine lt_of_le_of_lt (le_trans (MeasureTheory.lintegral_mono hpt)
          (le_of_eq (lintegral_add_left hP1meas _))) ?_
        exact (ENNReal.add_lt_top).mpr ⟨hlint1, hlint2⟩
      refine ⟨hΦmeas.aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn)]
      exact hlint
    -- Step B: the Fubini chain
    have hswapmp : MeasureTheory.MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        (volume.prod volume) (volume.prod volume) :=
      MeasureTheory.Measure.measurePreserving_swap
    have hFxint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n) => (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
          |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
        (volume.prod volume) := by
      refine ((hswapmp.integrable_comp hΦmeas.aestronglyMeasurable).mpr hΦint).congr' ?_ ?_
      · exact ((by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin n) => (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
            |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              ).aestronglyMeasurable
      · filter_upwards with p
        show ‖mollifier n C hC s hs (p.swap).1 * ((1 + ‖(p.swap).2‖) *
            |f (WithLp.toLp 2 (((p.swap).2 : Fin n → ℝ) - ((p.swap).1 : Fin n → ℝ)))
              - f (p.swap).2|)‖
          = ‖(1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
            |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|)‖
        simp only [Prod.swap, Real.norm_eq_abs, abs_mul]
        ring
    have hRint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin n),
          (1 + ‖x‖) * (mollifier n C hC s hs y *
            |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume) volume :=
      hFxint.integral_prod_left
    have hA : ∀ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|
        ≤ ∫ y : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) * (mollifier n C hC s hs y *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume := by
      intro x
      refine le_trans (mul_le_mul_of_nonneg_left (hstepA x) (by linarith [norm_nonneg x])) ?_
      exact le_of_eq ((MeasureTheory.integral_const_mul (1 + ‖x‖) (fun u =>
        mollifier n C hC s hs u *
          |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)).symm)
    have hLint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|) volume := by
      refine MeasureTheory.Integrable.mono' hRint ?_ ?_
      · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
          (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)).aestronglyMeasurable
      · filter_upwards with x
        show ‖(1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|‖
          ≤ ∫ y : EuclideanSpace ℝ (Fin n),
              (1 + ‖x‖) * (mollifier n C hC s hs y *
                |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (y : Fin n → ℝ))) - f x|) ∂volume
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg x])
          (abs_nonneg _))]
        exact hA x
    have hB1 : ∫ x : EuclideanSpace ℝ (Fin n),
        (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x| ∂volume
      ≤ ∫ u : EuclideanSpace ℝ (Fin n),
          ∫ x : EuclideanSpace ℝ (Fin n),
            mollifier n C hC s hs u * ((1 + ‖x‖) *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume := by
      refine le_trans (MeasureTheory.integral_mono hLint hRint hA) ?_
      calc ∫ x : EuclideanSpace ℝ (Fin n),
          ∫ u : EuclideanSpace ℝ (Fin n),
            (1 + ‖x‖) * (mollifier n C hC s hs u *
              |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|) ∂volume ∂volume
          ≤ ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.1‖) * (mollifier n C hC s hs z.2 *
                |f (WithLp.toLp 2 ((z.1 : Fin n → ℝ) - (z.2 : Fin n → ℝ))) - f z.1|)
                ∂(volume.prod volume) := by
            rw [← MeasureTheory.integral_prod
              (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume) hFxint]
        _ = ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              (1 + ‖z.swap.1‖) * (mollifier n C hC s hs z.swap.2 *
                |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) - f z.swap.1|)
                ∂(volume.prod volume) := by
            rw [← MeasureTheory.integral_prod_swap
              (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                (1 + ‖p.1‖) * (mollifier n C hC s hs p.2 *
                  |f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ))) - f p.1|))
              (μ := volume) (ν := volume)]
        _ = ∫ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              mollifier n C hC s hs z.1 * ((1 + ‖z.2‖) *
                |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) - f z.2|)
                ∂(volume.prod volume) := by
            have hswapcongr : ∀ z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
                (1 + ‖z.swap.1‖) * (mollifier n C hC s hs z.swap.2 *
                  |f (WithLp.toLp 2 (z.swap.1.ofLp - z.swap.2.ofLp)) - f z.swap.1|)
                = mollifier n C hC s hs z.1 * ((1 + ‖z.2‖) *
                  |f (WithLp.toLp 2 ((z.2 : Fin n → ℝ) - (z.1 : Fin n → ℝ))) - f z.2|) := by
              intro z
              simp only [Prod.swap]
              ring
            exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hswapcongr)
        _ = ∫ u : EuclideanSpace ℝ (Fin n),
              ∫ x : EuclideanSpace ℝ (Fin n),
                mollifier n C hC s hs u * ((1 + ‖x‖) *
                  |f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ))) - f x|)
                  ∂volume ∂volume := by
            rw [MeasureTheory.integral_prod
              (f := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
                mollifier n C hC s hs p.1 * ((1 + ‖p.2‖) *
                  |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) - (p.1 : Fin n → ℝ))) - f p.2|))
              (μ := volume) (ν := volume) hΦint]
    refine le_trans (le_trans hB1
      (le_of_eq (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
        simp only [weightedModulus]
        rw [MeasureTheory.integral_const_mul (mollifier n C hC s hs u)]))))
      (le_of_eq (integral_mollifier_mul n C hC s hs (weightedModulus n f) hwmAe))
  -- Step C: the dominated convergence on the shifted sequence `σ (· + k₀)`
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp
    (Metric.tendsto_nhds.mp hσ0 1 one_pos)
  have hσ1 : ∀ k : ℕ, (σ (k + k₀) : ℝ) ≤ 1 := by
    intro k
    have h := hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h
    exact le_of_lt h
  have hσ' : Filter.Tendsto (fun k : ℕ => σ (k + k₀)) Filter.atTop (nhds 0) := by
    refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ0 δ hδ)
    exact Filter.eventually_atTop.mpr ⟨N, fun k hk =>
      hN (k + k₀) (Nat.le_trans hk (Nat.le_add_right k k₀))⟩
  have hdct : Filter.Tendsto (fun k : ℕ => ∫ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC v *
        weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))) Filter.atTop
      (nhds 0) := by
    have hbdint : MeasureTheory.Integrable (fun v : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC v *
          ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖))) volume := by
      have hφCint : MeasureTheory.Integrable (multivariateGaussianPDF n 0 C hC) volume :=
        integrable_of_isPdf (isPdf_multivariateGaussianPDF n 0 C hC)
      have h1 : MeasureTheory.Integrable (fun v : EuclideanSpace ℝ (Fin n) =>
          multivariateGaussianPDF n 0 C hC v *
            ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2)) volume :=
        hφCint.mul_const _
      have h2 : MeasureTheory.Integrable (fun v : EuclideanSpace ℝ (Fin n) =>
          (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
            (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) volume :=
        (integrable_norm_mul_gaussianPDF_center n C hC).mul_const _
      have heq : (fun v : EuclideanSpace ℝ (Fin n) =>
            multivariateGaussianPDF n 0 C hC v *
              ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
          = (fun v : EuclideanSpace ℝ (Fin n) =>
              multivariateGaussianPDF n 0 C hC v *
                ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * 2))
            + (fun v : EuclideanSpace ℝ (Fin n) =>
              (‖v‖ * multivariateGaussianPDF n 0 C hC v) *
                (1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume)) := by
        funext v
        simp only [Pi.add_apply]
        ring
      rw [heq]
      exact h1.add h2
    have hwmSm : StronglyMeasurable (weightedModulus n f) := by
      have hKmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (1 + ‖p.2‖) * |f (WithLp.toLp 2 ((p.2 : Fin n → ℝ) -
            (p.1 : Fin n → ℝ))) - f p.2|) := by
        fun_prop
      exact hKmeas.stronglyMeasurable.integral_prod_right'
    have hFmeas : ∀ k : ℕ, AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC v *
          weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))) volume :=
      fun k => ((measurable_multivariateGaussianPDF n 0 C hC).stronglyMeasurable.mul
        (hwmSm.comp_measurable (by fun_prop : Measurable fun v : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))).aestronglyMeasurable
    have hbound : ∀ k : ℕ, ∀ᵐ (v : EuclideanSpace ℝ (Fin n)) ∂volume,
        ‖multivariateGaussianPDF n 0 C hC v *
          weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))‖
        ≤ multivariateGaussianPDF n 0 C hC v *
          ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)) :=
      fun k => Filter.Eventually.of_forall (fun v => by
        have hwmnn : 0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) :=
          show 0 ≤ ∫ x : EuclideanSpace ℝ (Fin n),
              (1 + ‖x‖) * |f (WithLp.toLp 2 ((x : Fin n → ℝ) -
                (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)) : Fin n → ℝ))) - f x| ∂volume
            from MeasureTheory.integral_nonneg fun x => mul_nonneg
              (by linarith [norm_nonneg x]) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (multivariateGaussianPDF_pos n 0 C hC v),
          abs_of_nonneg hwmnn]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
        refine le_trans (weightedModulus_le n f hf hpdf hfmom
          (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))) ?_
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [hMnn])
        have hnorm : ‖WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))‖
            = (σ (k + k₀) : ℝ) * ‖v‖ := by
          rw [show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))
              = (σ (k + k₀) : ℝ) • v from rfl, norm_smul]
          congr 1
          rw [Real.norm_eq_abs, abs_of_pos (hσ _)]
        rw [hnorm]
        linarith [mul_le_mul_of_nonneg_right (hσ1 k) (norm_nonneg v)])
    have hlim : ∀ᵐ v : EuclideanSpace ℝ (Fin n), Filter.Tendsto (fun k : ℕ =>
        multivariateGaussianPDF n 0 C hC v *
          weightedModulus n f (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))))
        Filter.atTop (nhds 0) := by
      filter_upwards with v
      have hv0 : Filter.Tendsto (fun k : ℕ =>
          WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ))) Filter.atTop (nhds 0) := by
        refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
        rcases eq_or_ne v 0 with hv | hv
        · refine Filter.Eventually.of_forall fun k => ?_
          rw [hv, show ((0 : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = 0 from rfl, smul_zero,
            show (WithLp.toLp 2 (0 : Fin n → ℝ)) = (0 : EuclideanSpace ℝ (Fin n)) from rfl,
            dist_self]
          exact hδ
        · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hσ' (δ / ‖v‖)
            (div_pos hδ (norm_pos_iff.2 hv)))
          refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
          have h1 := hN k hk
          rw [Real.dist_eq, sub_zero, abs_of_pos (hσ _)] at h1
          rw [dist_zero_right,
            show (WithLp.toLp 2 ((σ (k + k₀) : ℝ) • (v : Fin n → ℝ)))
              = (σ (k + k₀) : ℝ) • v from rfl, norm_smul, Real.norm_eq_abs,
            abs_of_pos (hσ _)]
          calc (σ (k + k₀) : ℝ) * ‖v‖ < (δ / ‖v‖) * ‖v‖ :=
            mul_lt_mul_of_pos_right h1 (norm_pos_iff.2 hv)
            _ = δ := by rw [div_mul_cancel₀ _ (ne_of_gt (norm_pos_iff.2 hv))]
      have hwm0 := hwmseq _ hv0
      have := (tendsto_const_nhds (x := multivariateGaussianPDF n 0 C hC v)).mul hwm0
      simpa using this
    have hdct' := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun v : EuclideanSpace ℝ (Fin n) =>
        multivariateGaussianPDF n 0 C hC v *
          ((1 + ∫ y : EuclideanSpace ℝ (Fin n), ‖y‖ * f y ∂volume) * (2 + ‖v‖)))
      (f := fun _ => (0 : ℝ)) hFmeas hbdint hbound hlim
    rw [integral_zero] at hdct'
    exact hdct'
  have hmain : Filter.Tendsto (fun k : ℕ => ∫ v : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n 0 C hC v *
        weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ)))) Filter.atTop
      (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat k₀).mp hdct
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hmain ε hε)
  refine Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
  have hNk := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (MeasureTheory.integral_nonneg (fun v : EuclideanSpace ℝ (Fin n) => mul_nonneg
      (le_of_lt (multivariateGaussianPDF_pos n 0 C hC v))
      (show 0 ≤ weightedModulus n f (WithLp.toLp 2 ((σ k : ℝ) • (v : Fin n → ℝ)))
        from MeasureTheory.integral_nonneg fun x => mul_nonneg
          (by linarith [norm_nonneg x]) (abs_nonneg _))))] at hNk
  have h0 : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f x - gaussSmoothed n f C hC (σ k) (hσ k) x| ∂volume :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (by linarith [norm_nonneg x])
      (abs_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h0]
  exact lt_of_le_of_lt (hchain (σ k) (hσ k)) hNk

/-! ### The smoothed-prior sequence satisfies the `hw` hypothesis -/

/-- Measurability of the Gaussian-smoothed prior: the `x`-marginal integral of the
joint `(x, u) ↦ ψ_σ(u) · f (x − u)`. -/
public theorem measurable_gaussSmoothed (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (σ : ℝ) (hσ : 0 < σ) :
    Measurable (gaussSmoothed n f C hC σ hσ) := by
  have hψmeas : Measurable (mollifier n C hC σ hσ) := measurable_mollifier n C hC σ hσ
  have hGxmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      mollifier n C hC σ hσ p.2 *
        f (WithLp.toLp 2 ((p.1 : Fin n → ℝ) - (p.2 : Fin n → ℝ)))) := by
    fun_prop
  exact (hGxmeas.stronglyMeasurable.integral_prod_right').measurable

/-- The smoothed-prior sequence: `K ↦ gaussSmoothed … (1/(K+1))`, with `1/(K+1) → 0`. -/
public noncomputable def smoothedPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
  fun K => gaussSmoothed n f C hC ((1:ℝ)/((K:ℝ) + 1)) (by positivity)

/-- **Weighted integrability of the smoothed-prior gap**: `(1 + ‖x‖) · |f x − gaussSmoothed x|`
is integrable, by domination with `(1 + ‖x‖) · f x + ∫ ψ_σ(u) · (1 + ‖x‖) · f (x − u) du`
(the second piece is the `x`-marginal of the ψ-first joint function). -/
public theorem integrable_weighted_abs_diff_gaussSmoothed (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|) volume := by
  classical
  have hf0 : 0 ≤ f := hpdf.1
  have hfi : MeasureTheory.Integrable f volume := integrable_of_isPdf hpdf
  have hψmeas : Measurable (mollifier n C hC s hs) := measurable_mollifier n C hC s hs
  have hgsmm : Measurable (gaussSmoothed n f C hC s hs) :=
    measurable_gaussSmoothed n f hf C hC s hs
  have hx : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ (1:ℝ) + ‖x‖ := fun x =>
    by linarith [norm_nonneg x]
  have hgsmpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ gaussSmoothed n f C hC s hs x := fun x =>
    MeasureTheory.integral_nonneg fun u =>
      mul_nonneg (mollifier_nonneg n C hC s hs u) (hf0 _)
  -- piece 1: `(1 + ‖x‖) · f x`
  have hg1 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * f x) volume := by
    have heq : (fun x : EuclideanSpace ℝ (Fin n) => (1 + ‖x‖) * f x)
      = fun x : EuclideanSpace ℝ (Fin n) => f x + ‖x‖ * f x := by
      funext x; ring
    rw [heq]; exact hfi.add hfmom
  -- piece 2: `(1 + ‖x‖) · gaussSmoothed x`, via the ψ-first joint's `x`-marginal
  have hg2 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * gaussSmoothed n f C hC s hs x) volume := by
    refine MeasureTheory.Integrable.mono'
      ((integrable_joint_smooth_prior n f hf hpdf hfmom C hC s hs).integral_prod_right) ?_ ?_
    · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
        (1 + ‖x‖) * gaussSmoothed n f C hC s hs x)).aestronglyMeasurable
    · filter_upwards with x
      show ‖(1 + ‖x‖) * gaussSmoothed n f C hC s hs x‖
        ≤ ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u * ((1 + ‖x‖) *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume
      have hsplit : ∫ u : EuclideanSpace ℝ (Fin n), mollifier n C hC s hs u * ((1 + ‖x‖) *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume
        = ∫ u : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) * (mollifier n C hC s hs u *
          f (WithLp.toLp 2 ((x : Fin n → ℝ) - (u : Fin n → ℝ)))) ∂volume :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hx x), abs_of_nonneg (hgsmpos x),
        hsplit, MeasureTheory.integral_const_mul (1 + ‖x‖)]
      exact mul_le_mul_of_nonneg_left (le_refl _) (hx x)
  -- the domination
  refine MeasureTheory.Integrable.mono' (hg1.add hg2) ?_ ?_
  · exact ((by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|)).aestronglyMeasurable
  · filter_upwards with x
    show ‖(1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|‖
      ≤ (1 + ‖x‖) * f x + (1 + ‖x‖) * gaussSmoothed n f C hC s hs x
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hx x)]
    calc (1 + ‖x‖) * |f x - gaussSmoothed n f C hC s hs x|
        ≤ (1 + ‖x‖) * (|f x| + |gaussSmoothed n f C hC s hs x|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) (hx x)
      _ = (1 + ‖x‖) * (f x + gaussSmoothed n f C hC s hs x) := by
          rw [abs_of_nonneg (hf0 x), abs_of_nonneg (hgsmpos x)]
      _ = (1 + ‖x‖) * f x + (1 + ‖x‖) * gaussSmoothed n f C hC s hs x := by
          rw [mul_add]

/-- **The `hw` hypothesis for the smoothed-prior sequence**: the ∫⁻ form of the weighted-L¹
convergence `∫ (1 + ‖x‖) |f x − gaussSmoothed … (1/(K+1)) x| → 0` along `K → ∞`. -/
public theorem hw_smoothedPriorSeq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) :
    ∀ ε > 0,
      ∃ K₀ : ℕ,
        ∀ K ≥ K₀,
          ∫⁻ h : EuclideanSpace ℝ (Fin n),
              ENNReal.ofReal ((1 + ‖h‖) *
                |f h - smoothedPriorSeq n f C hC K h|) ∂volume
            < ENNReal.ofReal ε := by
  intro ε hε
  classical
  have hσpos : ∀ K : ℕ, 0 < (1:ℝ)/((K:ℝ) + 1) := fun K =>
    div_pos one_pos (by positivity)
  have hσ0 : Filter.Tendsto (fun K : ℕ => (1:ℝ)/((K:ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := weighted_smoothing_tendsto_seq n f hf hpdf hfmom C hC
    (fun K => (1:ℝ)/((K:ℝ) + 1)) hσpos hσ0
  -- per-K integrability and the ∫⁻ ↔ ∫ bridge
  have hKint : ∀ K : ℕ, MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x|) volume := fun K =>
    integrable_weighted_abs_diff_gaussSmoothed n f hf hpdf hfmom C hC
      ((1:ℝ)/((K:ℝ) + 1)) (hσpos K)
  have hwnn : ∀ K : ℕ, 0 ≤ᵐ[volume] (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x|) := fun K =>
    Filter.Eventually.of_forall fun x => mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _)
  have hbridge : ∀ K : ℕ, ENNReal.ofReal (∫ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) * |f x - smoothedPriorSeq n f C hC K x| ∂volume)
    = ∫⁻ h : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal ((1 + ‖h‖) * |f h - smoothedPriorSeq n f C hC K h|) ∂volume := fun K =>
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hKint K) (hwnn K)
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp
    (Metric.tendsto_nhds.mp hconv ε hε)
  refine ⟨K₀, fun K hK => ?_⟩
  have hK₀K := hK₀ K hK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (MeasureTheory.integral_nonneg fun x =>
    mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))] at hK₀K
  rw [← hbridge K]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hK₀K

/-- **Phase 1**: the conditional mean estimates computed from the Gaussian-smoothed priors
`smoothedPriorSeq … K` converge to the CME of the true prior `f` locally uniformly —
uniformly on every closed ball of radius `r > 0` in `ℝ^m`, for arbitrary dimensions `m, n`
and observation matrix `A`. This is `cme_uniform_balls_R` with the smoothed-prior sequence,
whose `hw` hypothesis is `hw_smoothedPriorSeq`. -/
public theorem cme_uniform_balls_smoothed_prior (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosDef) (A : Matrix (Fin m) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hpdf : IsPdf f)
    (hfmom : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * f x) volume)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosDef) (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun K : ℕ =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A f y -
            cmeR m n S hS A (smoothedPriorSeq n f C hC K) y‖)
      atTop (nhds 0) := by
  have hσpos : ∀ K : ℕ, 0 < (1:ℝ)/((K:ℝ) + 1) := fun K =>
    div_pos one_pos (by positivity)
  exact cme_uniform_balls_R m n S hS A f hpdf hfmom (smoothedPriorSeq n f C hC)
    (fun K => isPdf_gaussSmoothed n f hpdf hf C hC ((1:ℝ)/((K:ℝ) + 1)) (hσpos K))
    (hw_smoothedPriorSeq n f hf hpdf hfmom C hC) r hr
