module

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
