module

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped Matrix

noncomputable def multivariateGaussianPDF (n : ℕ) (mean : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ) (_ : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let d := x - mean
  let quadForm := (mulVec (Cov⁻¹) d) ⬝ᵥ d
  let normalization := ( (2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (Cov.det) )⁻¹
  normalization * Real.exp (- (quadForm / 2))

/-- `(Aᵀ)⁻¹ = (A⁻¹)ᵀ` for a matrix with unit determinant, used to give the transposed matrix of
the change of variables `h ↦ y - A h` a unit. -/
theorem transpose_nonsing_inv
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det)
    :
    (Aᵀ)⁻¹ = (A⁻¹)ᵀ := by
  have hTT : Aᵀ * (A⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul (M := A⁻¹) (N := A), Matrix.nonsing_inv_mul A hA, Matrix.transpose_one]
  rw [Matrix.inv_eq_right_inv hTT]

/-- The covariance matrix `Σ̃ = A⁻¹ S A⁻ᵀ` of the Gaussian obtained from the change of
variables `h ↦ y - A h` is positive definite (Step 1 of
`plan_integral_norm_gaussian_bounded.md`: "first construct `hΣ̃`"). -/
theorem sigmaTilde_posDef
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det)
    :
    (A⁻¹ * S * A⁻¹ᵀ).PosDef := by
  have hATU : IsUnit Aᵀ := Matrix.isUnit_iff_isUnit_det Aᵀ |>.mpr (by rw [Matrix.det_transpose]; exact hA)
  have hTU : IsUnit ((A⁻¹)ᵀ) := by
    rw [← transpose_nonsing_inv A hA]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hATU
  have hstar : star ((A⁻¹)ᵀ) = A⁻¹ := by
    ext i j
    simp
  have hMid : star ((A⁻¹)ᵀ) * S * (A⁻¹)ᵀ = A⁻¹ * S * (A⁻¹)ᵀ := by
    rw [hstar]
  rw [← hMid, Matrix.posDef_iff_posSemidef_and_mulVec_injective]
  refine ⟨(Matrix.IsUnit.posSemidef_star_left_conjugate_iff hTU).mpr hS.posSemidef, ?_⟩
  have hcancelT : Aᵀ * (A⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul (M := A⁻¹) (N := A), Matrix.nonsing_inv_mul A hA, Matrix.transpose_one]
  have hAT : Function.Injective ((A⁻¹)ᵀ).mulVec := by
    intro x y hxy
    have h' := congrArg (fun t => (Aᵀ *ᵥ t)) hxy
    simp only [Matrix.mulVec_mulVec, hcancelT, Matrix.one_mulVec] at h'
    exact h'
  have hAS : Function.Injective S.mulVec := hS.mulVec_injective
  have hAinv : Function.Injective A⁻¹.mulVec := by
    have hNN : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
    intro x y hxy
    have h' := congrArg (fun t => (A *ᵥ t)) hxy
    simp only [Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec] at h'
    exact h'
  intro v w hvw
  simp only [← Matrix.mulVec_mulVec] at hvw
  exact hAT (hAS (hAinv hvw))

/-- Auxiliary quadratic-form identity for the change of variables: with `Σ̃ = A⁻¹ S A⁻ᵀ`
and `Σ̃⁻¹ = Aᵀ S⁻¹ A`, the quadratic form of the shifted variable `h ↦ h - A⁻¹ w` equals the
quadratic form of the original variable `w ↦ w - A u` (Step 1 of
`plan_integral_norm_gaussian_bounded.md`; cf. the exponent computation in `appendix_1.tex`). -/
theorem quadForm_eq
    {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hSdet : IsUnit S.det)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det)
    (u w : Fin n → ℝ) :
    (((A⁻¹ * S * (A⁻¹)ᵀ)⁻¹ *ᵥ (u - A⁻¹ *ᵥ w)) ⬝ᵥ (u - A⁻¹ *ᵥ w))
      = ((S⁻¹ *ᵥ (w - A *ᵥ u)) ⬝ᵥ (w - A *ᵥ u)) := by
  have hAA : A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = S * (A⁻¹)ᵀ := by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
  have h1 : Aᵀ * S⁻¹ * A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = 1 := by
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    calc
      Aᵀ * S⁻¹ * A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = Aᵀ * S⁻¹ * (A * ((A⁻¹ * S) * (A⁻¹)ᵀ)) := Matrix.mul_assoc _ _ _
      _ = Aᵀ * S⁻¹ * (S * (A⁻¹)ᵀ) := by rw [hAA]
      _ = (Aᵀ * S⁻¹) * (S * (A⁻¹)ᵀ) := rfl
      _ = Aᵀ * (S⁻¹ * (S * (A⁻¹)ᵀ)) := Matrix.mul_assoc _ _ _
      _ = Aᵀ * ((S⁻¹ * S) * (A⁻¹)ᵀ) := by rw [← Matrix.mul_assoc S⁻¹]
      _ = Aᵀ * (1 * (A⁻¹)ᵀ) := by rw [h2]
      _ = Aᵀ * (A⁻¹)ᵀ := by rw [Matrix.one_mul]
      _ = (A⁻¹ * A)ᵀ := by rw [← Matrix.transpose_mul (M := A⁻¹) (N := A)]
      _ = 1 := by rw [Matrix.nonsing_inv_mul A hA, Matrix.transpose_one]
  rw [Matrix.inv_eq_left_inv h1]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  rw [← neg_sub, Matrix.mulVec_neg, neg_dotProduct_neg]

/-- Step 1 of `plan_integral_norm_gaussian_bounded.md` (density identification): the weighted
Gaussian density `c * f_S (y - A h)` with `c = 1 / √det(A⁻¹ A⁻ᵀ)` is exactly the Gaussian PDF
with mean `A⁻¹ y` and covariance `Σ̃ = A⁻¹ S A⁻ᵀ` — the computation in `appendix_1.tex`
(Lemma `bound_norm`): the exponent satisfies
`(y - A h)ᵀ S⁻¹ (y - A h) = (h - A⁻¹ y)ᵀ (Aᵀ S⁻¹ A) (h - A⁻¹ y)` and `det(A⁻¹ A⁻ᵀ) = (det A)⁻²`. -/
theorem density_id
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det)
    (y : EuclideanSpace ℝ (Fin n))
    (hSig : (A⁻¹ * S * A⁻¹ᵀ).PosDef)
    (h : EuclideanSpace ℝ (Fin n))
    :
    (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det ))
      * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
      = multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig h
  := by
  have hSdetPos : 0 < S.det := hS.det_pos
  have hSU : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetPos)
  have hd1 : (A⁻¹).det = (A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv]; norm_num
  have hSigdet : ((A⁻¹ * S * (A⁻¹)ᵀ).det) = S.det / (A.det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd1,
      mul_comm ((A.det)⁻¹) S.det, mul_assoc S.det ((A.det)⁻¹) ((A.det)⁻¹),
      div_eq_mul_inv, ← inv_pow (A.det) 2, pow_two ((A.det)⁻¹)]
  have hAdet2 : ((A⁻¹ * (A⁻¹)ᵀ).det) = ((A⁻¹).det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two ((A⁻¹).det)]
  have hAdetc : (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det)) = abs A.det := by
    rw [hAdet2, hd1, inv_pow (A.det) 2, Real.sqrt_inv, Real.sqrt_sq_eq_abs, one_div, inv_inv]
  have hKey : (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det)) * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (S.det))⁻¹)
      = (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt ((A⁻¹ * S * (A⁻¹)ᵀ).det))⁻¹) := by
    have hAp : A.det ≠ 0 := isUnit_iff_ne_zero.mp hA
    have hSdne : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetPos)
    have hZne : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
    have hAbsne : abs A.det ≠ 0 := abs_ne_zero.mpr hAp
    rw [hAdetc, hSigdet, Real.sqrt_div (le_of_lt hSdetPos), Real.sqrt_sq_eq_abs]
    field_simp [hZne, hSdne, hAbsne]
  simp only [multivariateGaussianPDF, sub_zero]
  rw [quadForm_eq S hSU A hA]
  rw [← mul_assoc (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det))
    (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹), hKey]

/-- Sub-step 2a of `plan_integral_norm_gaussian_bounded.md` (Step 2): the standard Gaussian
density `(2π)^(-card ι / 2) · exp(-‖x‖²/2)` integrates to `1` over `EuclideanSpace ℝ ι`.
This makes `volume.withDensity` of it a probability measure (needed for
`Measure.ext_of_charFun` in sub-step 2c) and is the `c = 0` case of Mathlib's Gaussian
Fourier integral `GaussianFourier.integral_rexp_neg_mul_sq_norm` with `b = 1/2`. -/
theorem stdGaussianDensity_integral_one
    {ι : Type*}
    [Fintype ι]
    :
    ∫ x : EuclideanSpace ℝ ι,
      (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) = 1 := by
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  have hf : ∀ x : EuclideanSpace ℝ ι,
      Real.exp (-‖x‖ ^ 2 / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by congr 1; ring
  have h0 : ∫ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / 2) ∂volume
      = (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
    simp only [hf]
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ ι) hb]
    rw [finrank_euclideanSpace]
    rw [show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring]
  have hne : (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) ≠ 0 := by positivity
  rw [integral_const_mul, h0, neg_div, Real.rpow_neg, inv_mul_cancel₀ hne]
  positivity

/-- Sub-step 2b of `plan_integral_norm_gaussian_bounded.md` (Step 2): the characteristic
function of `volume.withDensity` of the standard Gaussian density is `exp(-‖t‖²/2)`,
i.e. it coincides with `charFun_stdGaussian` from Mathlib. Combined with 2a (the density
measure is a probability measure) this feeds `Measure.ext_of_charFun` in sub-step 2c. -/
theorem charFun_stdGaussianDensity
    {ι : Type*}
    [Fintype ι]
    (t : EuclideanSpace ℝ ι)
    :
    charFun (volume.withDensity (fun x => ENNReal.ofReal
      ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)))) t
      = Complex.exp (-‖t‖ ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) ≠ 0 := by positivity
  have hpos : ∀ x : EuclideanSpace ℝ ι,
      0 ≤ (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by positivity
  have hpoint : ∀ x : EuclideanSpace ℝ ι,
      (ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2))).toReal
        • Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)
      = (Complex.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)))
        * (Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2))
          * Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    intro x
    rw [ENNReal.toReal_ofReal (hpos x), Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  have hint : ∀ x : EuclideanSpace ℝ ι,
      Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2))
        * Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)
      = Complex.exp (-(Complex.ofReal (1 / 2)) * Complex.ofReal ‖x‖ ^ 2
          + Complex.I * Complex.ofReal (inner ℝ t x)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, real_inner_comm t x, mul_comm (Complex.ofReal (inner ℝ t x)) Complex.I]
  rw [charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  simp only [hpoint, hint]
  rw [integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I t,
    finrank_euclideanSpace,
    ← Complex.ofReal_div,
    show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring,
    show (((Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)) = Complex.ofReal ((Fintype.card ι : ℝ) / 2) from by push_cast; rfl,
    ← Complex.ofReal_cpow h2pi.le ((Fintype.card ι : ℝ) / 2),
    neg_div,
    Real.rpow_neg h2pi.le ((Fintype.card ι : ℝ) / 2),
    ← mul_assoc,
    ← Complex.ofReal_mul,
    inv_mul_cancel₀ hne,
    Complex.ofReal_one, one_mul,
    Complex.I_sq, neg_one_mul,
    show ((4 : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 2 from by norm_num]

/-- Sub-step 2c of `plan_integral_norm_gaussian_bounded.md` (Step 2): the standard Gaussian
measure `stdGaussian` equals `volume.withDensity` of the standard Gaussian density.
Via `Measure.ext_of_charFun` it suffices to compare characteristic functions, using
`charFun_stdGaussian` (Mathlib) and `charFun_stdGaussianDensity` (sub-step 2b); the
`IsFiniteMeasure` instance on the density side is derived from sub-step 2a
(`isFiniteMeasure_withDensity` needs `∫⁻ x, ENNReal.ofReal f ∂volume ≠ ∞`, which follows
from `∫ x, f x = 1` via `ofReal_integral_eq_lintegral_ofReal`). -/
theorem stdGaussian_eq_withDensity
    {ι : Type*}
    [Fintype ι]
    :
    stdGaussian (EuclideanSpace ℝ ι) = volume.withDensity (fun x => ENNReal.ofReal
      ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2))) := by
  have hexp : ∀ x : EuclideanSpace ℝ ι,
      Real.exp (-(1 / 2) * ‖x‖ ^ 2) = Real.exp (-‖x‖ ^ 2 / 2) := fun x => by congr 1; ring
  have hint : ∫ x : EuclideanSpace ℝ ι,
      (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) = 1 := by
    simp only [hexp]
    exact stdGaussianDensity_integral_one
  have hfin : Integrable (fun x : EuclideanSpace ℝ ι =>
      (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) volume :=
    Integrable.of_integral_ne_zero (by rw [hint]; norm_num)
  have hlint : ∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal
      ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfin
      (Eventually.of_forall fun x => by positivity)]
    rw [hint, ENNReal.ofReal_one]
  have hmeas : IsFiniteMeasure (volume.withDensity (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal
      ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)))) :=
    isFiniteMeasure_withDensity (by rw [hlint]; simp)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_stdGaussianDensity]

theorem integral_norm_gaussian_bounded
  (n : ℕ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.PosDef)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A.det)
  (y : EuclideanSpace ℝ (Fin n))
  :
  MeasureTheory.Integrable (fun (h : EuclideanSpace ℝ (Fin n)) =>
    ‖h‖
    * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
    * (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det ))) volume
  := by
  sorry
