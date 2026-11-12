module

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

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


/-- Linear change of variables for integrals over `EuclideanSpace ℝ (Fin n)`: for a matrix
`B` with positive determinant, pulling the integrand back along `x ↦ μ + B x` scales the
integral by `B.det` (Step 3 of `plan_integral_norm_gaussian_bounded.md`: the substitution
`x ↦ μ + √Σ x` in the Fourier integral of the Gaussian density). -/
theorem integral_subst {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [OpensMeasurableSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [SecondCountableTopology F]
    (n : ℕ) (μ : EuclideanSpace ℝ (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ) (hBdet : 0 < B.det)
    (f : EuclideanSpace ℝ (Fin n) → F) (hf : AEMeasurable f volume) :
    ∫ x, f x ∂volume
      = (B.det : ℝ) • ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume := by
  have hLdet : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hLne : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) ≠ 0 := by
    rw [hLdet]; exact ne_of_gt hBdet
  have hmapL : Measure.map (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) volume
      = ENNReal.ofReal (B.det)⁻¹ • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLdet, abs_of_pos (inv_pos.mpr hBdet)]
  have hmeasg : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x := by fun_prop
  have hmapg : Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume
      = ENNReal.ofReal (B.det)⁻¹ • volume := by
    rw [show (fun x : EuclideanSpace ℝ (Fin n) =>
        μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
      = (μ + ·) ∘ (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) from rfl,
      ← Measure.map_map (by fun_prop : Measurable (μ + ·))
        (by fun_prop : Measurable (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B)),
      hmapL, Measure.map_smul _ (by fun_prop), MeasureTheory.map_add_left_eq_self volume μ]
  have hac : Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume ≪ volume := by
    rw [hmapg]; exact Measure.smul_absolutelyContinuous
  have hf' : AEStronglyMeasurable f (Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume) :=
    (hf.mono_ac hac).aestronglyMeasurable
  have H : ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume
      = (B.det)⁻¹ • ∫ x, f x ∂volume := by
    calc ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume
        = ∫ y, f y ∂(Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
            μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume) :=
          (integral_map (hmeasg.aemeasurable) hf').symm
      _ = ∫ y, f y ∂(ENNReal.ofReal (B.det)⁻¹ • volume) := by rw [hmapg]
      _ = (ENNReal.ofReal (B.det)⁻¹).toReal • ∫ y, f y ∂volume := integral_smul_measure _ _
      _ = (B.det)⁻¹ • ∫ y, f y ∂volume := by
          rw [ENNReal.toReal_ofReal (by positivity)]
  rw [H, smul_smul, mul_inv_cancel₀ (ne_of_gt hBdet), one_smul]


/-- The quadratic form of `√Σ`: with `B = CFC.sqrt S` the positive square root of a positive
definite matrix `S`, the quadratic form of the transformed variable `h ↦ B h` collapses to
`‖h‖²` (Step 3: reduction of the Gaussian integral to the standard Gaussian integral). -/
theorem quadForm_sqrt_eq_norm_sq (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    ∀ h : EuclideanSpace ℝ (Fin n),
      (S⁻¹ *ᵥ (CFC.sqrt S *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (CFC.sqrt S *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2 := by
  have hSdetpos : 0 < S.det := hS.det_pos
  have hS0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBnn : 0 ≤ B := by rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdet : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr (by rw [hBdetEq]; exact ne_of_gt (Real.sqrt_pos.mpr hSdetpos))
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetpos)
  have hBT : Bᵀ = B := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hBher
  have h1eq : (S⁻¹ * B) * B = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.mul_assoc, hBB, Matrix.nonsing_inv_mul S hSdet]
  have h1 : B⁻¹ = S⁻¹ * B := Matrix.inv_eq_left_inv h1eq
  intro h
  set h' : Fin n → ℝ := (h : Fin n → ℝ) with hh'
  calc (S⁻¹ *ᵥ (B *ᵥ h')) ⬝ᵥ (B *ᵥ h')
      = ((S⁻¹ * B) *ᵥ h') ⬝ᵥ (B *ᵥ h') := by rw [Matrix.mulVec_mulVec]
    _ = (B⁻¹ *ᵥ h') ⬝ᵥ (B *ᵥ h') := by rw [h1]
    _ = h' ⬝ᵥ (Bᵀ *ᵥ (B⁻¹ *ᵥ h')) :=
        (Matrix.dotProduct_transpose_mulVec B h' (B⁻¹ *ᵥ h')).symm
    _ = h' ⬝ᵥ ((B * B⁻¹) *ᵥ h') := by rw [hBT, Matrix.mulVec_mulVec]
    _ = h' ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ h') := by rw [Matrix.mul_nonsing_inv B hBdet]
    _ = h' ⬝ᵥ h' := by rw [Matrix.one_mulVec]
    _ = ‖h‖ ^ 2 := by
        calc h' ⬝ᵥ h' = h' ⬝ᵥ star h' := by
              rw [show star h' = h' from by simp]
          _ = inner ℝ (WithLp.toLp 2 h') (WithLp.toLp 2 h') :=
              (EuclideanSpace.inner_toLp_toLp h' h').symm
          _ = ‖WithLp.toLp 2 h'‖ ^ 2 := real_inner_self_eq_norm_sq _
          _ = ‖h‖ ^ 2 := rfl


/-- Core: Fourier transform of the standard Gaussian density at general frequency `w`. -/
theorem stdGaussianDensity_ft {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ ι) :
    ∫ x : EuclideanSpace ℝ ι,
      Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2))
        * Complex.exp (Complex.ofReal (inner ℝ x w) * Complex.I)
    = ((2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) * Complex.exp (-‖w‖ ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hexp : ∀ x : EuclideanSpace ℝ ι,
      Real.exp (-‖x‖ ^ 2 / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by congr 1; ring
  have hint : ∀ x : EuclideanSpace ℝ ι,
      Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2))
        * Complex.exp (Complex.ofReal (inner ℝ x w) * Complex.I)
      = Complex.exp (-(Complex.ofReal (1 / 2)) * Complex.ofReal ‖x‖ ^ 2
          + Complex.I * Complex.ofReal (inner ℝ w x)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, real_inner_comm w x, mul_comm (Complex.ofReal (inner ℝ w x)) Complex.I]
  simp only [hexp, hint]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I w,
    finrank_euclideanSpace,
    ← Complex.ofReal_div,
    show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring,
    show (((Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)) = Complex.ofReal ((Fintype.card ι : ℝ) / 2) from by push_cast; rfl,
    ← Complex.ofReal_cpow h2pi.le ((Fintype.card ι : ℝ) / 2),
    Complex.I_sq, neg_one_mul,
    show ((4 : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 2 from by norm_num]


/-- Step 3 of `plan_integral_norm_gaussian_bounded.md` (Fourier characterization): the
characteristic function of the Gaussian measure with mean `μ` and positive definite
covariance `S`, realized as `volume.withDensity` of the Gaussian PDF
`multivariateGaussianPDF`, is `exp(i⟨t, μ⟩ - ⟨t, S t⟩ / 2)`, matching the characteristic
function of Mathlib's `multivariateGaussian μ S` (via `charFun_multivariateGaussian`).
The proof substitutes `x ↦ μ + √Σ x` (`integral_subst`), splits the pointwise integrand
(`hsplit`), extracts the constant factors, and evaluates the remaining standard Gaussian
Fourier integral (`stdGaussianDensity_ft`). -/
theorem multivariateGaussian_eq_withDensity (n : ℕ) (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (t : EuclideanSpace ℝ (Fin n)) :
    charFun (volume.withDensity (fun x => ENNReal.ofReal
      (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x))) t
      = Complex.exp (Complex.ofReal (inner ℝ t μ) * Complex.I
          - Complex.ofReal ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)) / 2) := by
  -- CFC bundle
  have hSdetpos : 0 < S.det := hS.det_pos
  have hS0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBnn : 0 ≤ B := by rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdetpos : 0 < B.det := by rw [hBdetEq]; exact Real.sqrt_pos.mpr hSdetpos
  have hBdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hBdetpos)
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetpos)
  have hBT : Bᵀ = B := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hBher
  have hquad' : ∀ h : EuclideanSpace ℝ (Fin n),
      (S⁻¹ *ᵥ (B *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (B *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2 := by
    intro h; rw [← hBdef] at *; exact quadForm_sqrt_eq_norm_sq n S hS h
  -- bridges
  have hcoep : ∀ x : EuclideanSpace ℝ (Fin n),
      ((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        - (μ : Fin n → ℝ) = B *ᵥ (x : Fin n → ℝ) := by
    intro x
    rw [WithLp.ofLp_add, add_sub_cancel_left]
    rfl
  have hinner : ∀ (x y : EuclideanSpace ℝ (Fin n)),
      inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B y) = x ⬝ᵥ B *ᵥ (y : Fin n → ℝ) :=
    fun x y => Matrix.inner_toEuclideanCLM B x y
  have hcoLt :
      (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t : Fin n → ℝ) = B *ᵥ (t : Fin n → ℝ) := rfl
  have hbridge : ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x) t
        = inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t) := by
    intro x
    rw [real_inner_comm, hinner t x, ← Matrix.dotProduct_transpose_mulVec, hBT, ← hinner]
  -- PDF facts
  have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x
        = ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
            ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)) :=
    fun _ => rfl
  have hP' : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hP'0 : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have hSqrt0 : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetpos)
  have hpos : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x := by
    intro x
    rw [hpdf x]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hP')
      (le_of_lt (Real.sqrt_pos.mpr hSdetpos)))) (le_of_lt (Real.exp_pos _))
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x)).toReal
        • Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)
      = Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        * (Complex.ofReal (Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
          ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)))
          * Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    intro x
    rw [ENNReal.toReal_ofReal (hpos x), hpdf x, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  have hmeasP : AEMeasurable (fun x => ENNReal.ofReal
      (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x)) volume := by
    have hinner_meas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
            ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2))) := by
      fun_prop
    have hRHS : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
        (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
            ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)))) volume :=
      (ENNReal.measurable_ofReal.comp hinner_meas).aemeasurable
    exact hRHS.congr (Filter.Eventually.of_forall (fun x => by simp only [hpdf]))
  have htop : ∀ᵐ x ∂volume,
      ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x) < ∞ := by simp
  -- norm bridge and scalar identities
  have hnorm2 : ‖Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t‖ ^ 2
      = (t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ) := by
    rw [← real_inner_self_eq_norm_sq,
      hinner (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t) t, hcoLt,
      ← Matrix.dotProduct_transpose_mulVec, hBT, Matrix.mulVec_mulVec, hBB]
  have hscal : B.det * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
      * (2 * Real.pi) ^ ((n : ℝ) / 2)) = 1 := by
    rw [hBdetEq, mul_comm (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
      ((2 * Real.pi) ^ ((n : ℝ) / 2)), ← mul_assoc,
      mul_comm (Real.sqrt S.det) ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      mul_inv_cancel₀ (mul_ne_zero hP'0 hSqrt0)]
  have hscalC : Complex.ofReal B.det * (Complex.ofReal
      (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
      * Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2))) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hscal, Complex.ofReal_one]
  have hfin : Complex.exp (Complex.ofReal (inner ℝ t μ) * Complex.I)
      * Complex.exp (Complex.ofReal (-
        ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2)
      = Complex.exp (Complex.ofReal (inner ℝ t μ) * Complex.I
          - Complex.ofReal ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)) / 2) := by
    rw [Complex.ofReal_neg, neg_div, ← Complex.exp_add, sub_eq_add_neg]
  -- pointwise splitting after substitution
  have hsplit : ∀ x : EuclideanSpace ℝ (Fin n),
      Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        * (Complex.ofReal (Real.exp (-(((S⁻¹ *ᵥ (((μ + Matrix.toEuclideanLin (𝕜 := ℝ)
          (m := Fin n) B x : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
          (((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x : EuclideanSpace ℝ (Fin n))
            : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)))
          * Complex.exp (Complex.ofReal (inner ℝ (μ + Matrix.toEuclideanLin (𝕜 := ℝ)
            (m := Fin n) B x) t) * Complex.I))
      = (Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
          * Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I))
        * (Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2))
          * Complex.exp (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ)
            (m := Fin n) B t)) * Complex.I)) := by
    intro x
    rw [hcoep x, hquad' x, ← neg_div, inner_add_left, Complex.ofReal_add, add_mul,
      hbridge x, Complex.exp_add]
    ring
  -- rearrangement and exponent normalization for the endgame
  have hrearr : Complex.ofReal B.det
      * ((Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
          * Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I))
        * (Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2))
          * Complex.exp (Complex.ofReal (-
            ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2)))
      = (Complex.ofReal B.det * (Complex.ofReal
        (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        * Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2))))
      * (Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I)
        * Complex.exp (Complex.ofReal (-
          ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2)) := by
    ring
  -- substitution
  have hsub := integral_subst n μ B hBdetpos
    (fun x => Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
      * (Complex.ofReal (Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
        ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)))
        * Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)))
    (by fun_prop)
  -- substitution + pointwise splitting + const extraction, in one step (defeq-chained,
  -- no brittle `rw` matching of the substituted integrand)
  have hstep2 : ∫ x : EuclideanSpace ℝ (Fin n), Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
      * (Complex.ofReal (Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
        ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)))
        * Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) ∂volume
      = (B.det : ℝ) • ((Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
          * Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I))
          * ∫ x : EuclideanSpace ℝ (Fin n), Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2))
            * Complex.exp (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ)
              (m := Fin n) B t)) * Complex.I) ∂volume) := by
    refine Eq.trans hsub (congrArg ((B.det : ℝ) • ·)
      (Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (fun y => hsplit y)))
        (integral_const_mul _
          (fun x : EuclideanSpace ℝ (Fin n) =>
            Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2))
              * Complex.exp (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ)
                (m := Fin n) B t)) * Complex.I)))))
  rw [charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeasP htop]
  simp only [hpoint]
  rw [hstep2, Complex.real_smul,
    stdGaussianDensity_ft (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t)]
  simp only [Fintype.card_fin]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, hnorm2, hrearr, hscalC, one_mul,
    real_inner_comm t μ, hfin]


/-- Step 4 of `plan_integral_norm_gaussian_bounded.md`: the multivariate Gaussian PDF with mean
`μ` and positive definite covariance `S` integrates to `1` over `EuclideanSpace ℝ (Fin n)`
(substitution `x ↦ μ + √Σ x` via `integral_subst`, reducing to the standard Gaussian integral
`stdGaussianDensity_integral_one`). -/
theorem integral_multivariateGaussianPDF_one (n : ℕ) (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x ∂volume = 1 := by
  -- CFC bundle (same as in `multivariateGaussian_eq_withDensity`)
  have hSdetpos : 0 < S.det := hS.det_pos
  have hS0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBnn : 0 ≤ B := by rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdetpos : 0 < B.det := by rw [hBdetEq]; exact Real.sqrt_pos.mpr hSdetpos
  have hquad' : ∀ h : EuclideanSpace ℝ (Fin n),
      (S⁻¹ *ᵥ (B *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (B *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2 := by
    intro h; rw [← hBdef] at *; exact quadForm_sqrt_eq_norm_sq n S hS h
  have hcoep : ∀ x : EuclideanSpace ℝ (Fin n),
      ((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        - (μ : Fin n → ℝ) = B *ᵥ (x : Fin n → ℝ) := by
    intro x
    rw [WithLp.ofLp_add, add_sub_cancel_left]
    rfl
  -- PDF facts
  have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x
        = ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
            ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2)) :=
    fun _ => rfl
  have hP'0 : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have hSqrt0 : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetpos)
  have hmeasRHS : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
        * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
          ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) / 2))) := by
    fun_prop
  have hf : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x) volume :=
    hmeasRHS.aemeasurable.congr (Filter.Eventually.of_forall (fun x => by simp only [hpdf]))
  -- shifted PDF reduces to the standard Gaussian density
  have hshift : ∀ y : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS
        (μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B y)
        = ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-‖y‖ ^ 2 / 2) := by
    intro y
    rw [hpdf, hcoep y, hquad' y, ← neg_div]
  -- substitution + pointwise shift + constant extraction, in one step (defeq-chained,
  -- no brittle `rw` matching of the substituted integrand)
  have hsub := integral_subst n μ B hBdetpos
    (fun x => multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x) hf
  have hstep : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x ∂volume
      = (B.det : ℝ) • (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
        * ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / 2) ∂volume) := by
    refine Eq.trans hsub (congrArg ((B.det : ℝ) • ·)
      (Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (fun y => hshift y)))
        (integral_const_mul _
          (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2)))))
  -- extract the standard Gaussian integral
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hPne : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have h0 := stdGaussianDensity_integral_one (ι := Fin n)
  simp only [Fintype.card_fin] at h0
  rw [integral_const_mul] at h0
  rw [show (-(↑n : ℝ)) / 2 = -((↑n : ℝ) / 2) from by ring] at h0
  rw [Real.rpow_neg h2pi.le ((n : ℝ) / 2)] at h0
  have h1 : ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / 2) ∂volume
      = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
    have h3 := congrArg (fun t : ℝ => (2 * Real.pi) ^ ((n : ℝ) / 2) * t) h0
    rw [← mul_assoc, mul_inv_cancel₀ hPne, one_mul, mul_one] at h3
    exact h3
  have hscal : B.det * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
      * (2 * Real.pi) ^ ((n : ℝ) / 2)) = 1 := by
    rw [hBdetEq, mul_comm (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
      ((2 * Real.pi) ^ ((n : ℝ) / 2)), ← mul_assoc,
      mul_comm (Real.sqrt S.det) ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      mul_inv_cancel₀ (mul_ne_zero hP'0 hSqrt0)]
  rw [hstep, smul_eq_mul, h1]
  rw [hscal]


/-- Step 5 of `plan_integral_norm_gaussian_bounded.md`: `volume.withDensity` of
`ENNReal.ofReal ∘ (multivariateGaussianPDF …)` is a finite measure (feeds
`Measure.ext_of_charFun`; the `∫⁻ … ≠ ∞` side condition follows from the integral being `1`,
via `ofReal_integral_eq_lintegral_ofReal`). -/
theorem isFiniteMeasure_gaussianPDF_withDensity (n : ℕ) (mean : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    IsFiniteMeasure (volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n mean S hS x))) := by
  have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (WithLp.toLp 2 mean : EuclideanSpace ℝ (Fin n)) S hS x
        = multivariateGaussianPDF n mean S hS x := fun _ => rfl
  have hint : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n mean S hS x ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 mean) S hS
    exact (integral_congr_ae (Filter.Eventually.of_forall
      (fun x => (hpdf x).symm))).trans h1
  have hSdetpos : 0 < S.det := hS.det_pos
  have hpos : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n mean S hS x := by
    intro x
    rw [show multivariateGaussianPDF n mean S hS x
        = ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹
          * Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - mean)) ⬝ᵥ
            ((x : Fin n → ℝ) - mean)) / 2)) from rfl]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt (by positivity))
      (le_of_lt (Real.sqrt_pos.mpr hSdetpos)))) (le_of_lt (Real.exp_pos _))
  have hfin : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n mean S hS x) volume :=
    Integrable.of_integral_ne_zero (by rw [hint]; norm_num)
  have hlint : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
      (multivariateGaussianPDF n mean S hS x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfin
      (Eventually.of_forall fun x => hpos x)]
    rw [hint, ENNReal.ofReal_one]
  exact isFiniteMeasure_withDensity (by rw [hlint]; simp)


/-- Pointwise unfolding of `multivariateGaussianPDF` for a general mean and covariance. -/
theorem multivariateGaussianPDF_eq (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    multivariateGaussianPDF n m Cov hC x
      = ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt Cov.det)⁻¹
        * Real.exp (-(((Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ
          ((x : Fin n → ℝ) - m)) / 2)) :=
  rfl

/-- Measurability of the multivariate Gaussian PDF. -/
theorem measurable_multivariateGaussianPDF (n : ℕ) (m : Fin n → ℝ)
    (Cov : Matrix (Fin n) (Fin n) ℝ) (hC : Cov.PosDef) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n m Cov hC x) := by
  simp only [multivariateGaussianPDF_eq n m Cov hC]
  fun_prop


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
  have hSig : (A⁻¹ * S * A⁻¹ᵀ).PosDef := sigmaTilde_posDef n S hS A hA
  -- PDF with mean `A⁻¹ y` and covariance `Σ̃ = A⁻¹ S A⁻ᵀ` (mean in plain form, matching
  -- `density_id`'s RHS verbatim)
  have hP' : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSigdetpos : 0 < (A⁻¹ * S * A⁻¹ᵀ).det := hSig.det_pos
  have hposT : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x := by
    intro x
    rw [multivariateGaussianPDF_eq n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hP')
      (le_of_lt (Real.sqrt_pos.mpr hSigdetpos)))) (le_of_lt (Real.exp_pos _))
  have hmeasPT : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x)) volume :=
    (ENNReal.measurable_ofReal.comp
      (measurable_multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ))
        (A⁻¹ * S * A⁻¹ᵀ) hSig)).aemeasurable
  have htopT : ∀ᵐ x ∂volume,
      ENNReal.ofReal (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ))
        (A⁻¹ * S * A⁻¹ᵀ) hSig x) < ∞ := by simp
  -- the cast mean (as produced by instantiating the EuclideanSpace-typed lemmas) agrees
  -- pointwise with the plain `(A⁻¹).mulVec y` mean
  have hcast : ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n
        ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        (A⁻¹ * S * A⁻¹ᵀ) hSig x
      = multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x :=
    fun _ => rfl
  -- the density measure is finite (feeds `Measure.ext_of_charFun`)
  have hfin : IsFiniteMeasure (volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n
        ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        (A⁻¹ * S * A⁻¹ᵀ) hSig x))) :=
    isFiniteMeasure_gaussianPDF_withDensity n
      ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
      (A⁻¹ * S * A⁻¹ᵀ) hSig
  -- the density measure is the multivariate Gaussian measure
  have hEqL : volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n
        ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
        (A⁻¹ * S * A⁻¹ᵀ) hSig x))
      = volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x)) :=
    congrArg volume.withDensity (funext fun x => congrArg ENNReal.ofReal (hcast x))
  have hEq : volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x))
      = multivariateGaussian (WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * A⁻¹ᵀ) := by
    refine hEqL.symm.trans ?_
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [multivariateGaussian_eq_withDensity n
      (WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * A⁻¹ᵀ) hSig t,
      charFun_multivariateGaussian hSig.posSemidef t]
  -- withDensity bridge: identity is integrable w.r.t. the density measure
  have hwithD : MeasureTheory.Integrable id (volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ))
        (A⁻¹ * S * A⁻¹ᵀ) hSig x))) := by
    rw [hEq]
    exact ProbabilityTheory.IsGaussian.integrable_id
  have hbridge := (integrable_withDensity_iff_integrable_smul₀' hmeasPT htopT).mp hwithD
  have hnormed := hbridge.norm
  -- pointwise: ‖toReal ofReal pdf • x‖ = ‖x‖ * pdf
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(ENNReal.ofReal (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ))
          (A⁻¹ * S * A⁻¹ᵀ) hSig x)).toReal • id x‖
        = ‖x‖ * multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ))
          (A⁻¹ * S * A⁻¹ᵀ) hSig x := by
    intro x
    rw [norm_smul, ENNReal.toReal_ofReal (hposT x), Real.norm_eq_abs,
      abs_of_nonneg (hposT x), show ‖id x‖ = ‖x‖ from rfl, mul_comm]
  have hkey := hnormed.congr (Filter.Eventually.of_forall hpt)
  -- bridge to the goal integrand via `density_id`
  have hcongr1 : ∀ h : EuclideanSpace ℝ (Fin n),
      ‖h‖
      * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
      * (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det))
      = ‖h‖ * multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig h := by
    intro h
    rw [mul_assoc,
      mul_comm (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))))
        (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)),
      ← density_id n S hS A hA y hSig h]
  exact hkey.congr (Filter.Eventually.of_forall (fun h => (hcongr1 h).symm))


