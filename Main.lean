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


theorem integral_normalized_gaussian_bounded
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

theorem integral_gaussian_bounded
  (n : ℕ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.PosDef)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A.det)
  (y : EuclideanSpace ℝ (Fin n))
  :
  MeasureTheory.Integrable (fun (h : EuclideanSpace ℝ (Fin n)) =>
    ‖h‖
    * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))) volume
  := by
  have hAdet2 : ((A⁻¹ * A⁻¹ᵀ).det) = ((A⁻¹).det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two ((A⁻¹).det)]
  have hAdetinv : (A⁻¹).det = (A.det)⁻¹ := by rw [Matrix.det_nonsing_inv]; norm_num
  have hne : Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det) ≠ 0 := by
    rw [hAdet2, Real.sqrt_sq_eq_abs, ne_eq, abs_eq_zero, hAdetinv, inv_eq_zero]
    exact isUnit_iff_ne_zero.mp hA
  have hnorm := integral_normalized_gaussian_bounded n S hS A hA y
  have h1 := hnorm.smul (Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det))
  refine h1.congr (Filter.Eventually.of_forall (fun h => ?_))
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp


/-! ## Uniform convergence of the observation densities (appendix_1.tex)

Setup: the latent `h` has density `f_h`, the measurement noise `n ~ N(0, S)` is independent,
and `y = A h + n`. By the convolution formula (change of variables `s = y - A h`), the density
of `y` is `f_y(y) = ∫ f_n(y - A h) f_h(h) dh`. The first part of the proof of the main result
shows: uniform convergence of `f_h^{(K)}` to `f_h` implies uniform convergence of the induced
observation densities, with quantitative bound
`|f_y(y) - f_y^{(K)}(y)| ≤ ‖f_h - f_h^{(K)}‖_∞ / |det A|`. -/

/-- The Gaussian noise density `n ~ N(0, S)` evaluated along the affine map `h ↦ y - A h`. -/
noncomputable def noiseDens (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n))
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
    (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))


/-- Pointwise identity of `noiseDens` with the Gaussian pdf evaluated at the linear-map form
`y + (-A) h` (the shape required by `integral_subst_unit`). -/
theorem noiseDens_eq (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n))
    (h : EuclideanSpace ℝ (Fin n)) :
    noiseDens n S hS A y h
      = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
  simp only [noiseDens]
  rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))),
    multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h)]
  have hco : ((WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) : Fin n → ℝ)
      = ((y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) : Fin n → ℝ) := by
    rw [WithLp.ofLp_toLp]
    show (y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)
      = (y : Fin n → ℝ) + ((-1 : ℝ) • A) *ᵥ (h : Fin n → ℝ)
    rw [Matrix.smul_mulVec, neg_one_smul, sub_eq_add_neg]
  rw [hco, WithLp.ofLp_add]


/-- Generalized linear change of variables over `EuclideanSpace ℝ (Fin n)`: `integral_subst`
of Step 3 with `0 < B.det` weakened to `IsUnit B.det`; the scaling factor is the absolute
value of the inverse Jacobian determinant. -/
theorem integral_subst_unit (n : ℕ) (μ : EuclideanSpace ℝ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : IsUnit B.det)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AEMeasurable f volume) :
    ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume
      = (|(B.det : ℝ)⁻¹|) • ∫ x, f x ∂volume := by
  have hLdet : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hLne : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) ≠ 0 := by
    rw [hLdet]; exact isUnit_iff_ne_zero.mp hB
  have hmapL : Measure.map (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) volume
      = ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLdet]
  have hmeasg : Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x := by fun_prop
  have hmapg : Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume
      = ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume := by
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
      = (|(B.det : ℝ)⁻¹|) • ∫ x, f x ∂volume := by
    calc ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume
        = ∫ y, f y ∂(Measure.map (fun x : EuclideanSpace ℝ (Fin n) =>
            μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) volume) :=
          (integral_map hmeasg.aemeasurable hf').symm
      _ = ∫ y, f y ∂(ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume) := by rw [hmapg]
      _ = (ENNReal.ofReal (|(B.det : ℝ)⁻¹|)).toReal • ∫ y, f y ∂volume :=
          integral_smul_measure _ _
      _ = (|(B.det : ℝ)⁻¹|) • ∫ y, f y ∂volume := by
          rw [ENNReal.toReal_ofReal (by positivity)]
  rw [H, abs_inv]


/-- Mass of the pulled-back noise density: `∫ f_n(y - A h) dh = |det A|⁻¹` — the appendix's
change of variables `s = y - A h` in `∫ f_n(s) ds = 1`. -/
theorem integral_noise_pullback (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n)) :
    ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume = (|A.det| : ℝ)⁻¹ := by
  set B : Matrix (Fin n) (Fin n) ℝ := (-1 : ℝ) • A with hBdef
  have hBdet : B.det = (-1 : ℝ) ^ n * A.det := by
    rw [hBdef, Matrix.det_smul, Fintype.card_fin]
  have hBunit : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr (by
      rw [hBdet]
      exact mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero))
        (isUnit_iff_ne_zero.mp hA))
  have hBabs : |B.det| = |A.det| := by
    rw [hBdet, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hmeas : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) volume :=
    (measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).aemeasurable
  have hint := integral_subst_unit n y B hBunit
    (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) hmeas
  have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
  calc ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume
      = ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume := by
        rw [integral_congr_ae (Filter.Eventually.of_forall
          (fun h => noiseDens_eq n S hS A y h))]
    _ = (|(B.det : ℝ)⁻¹|) • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume :=
        hint
    _ = (|B.det| : ℝ)⁻¹ • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume := by
        rw [abs_inv]
    _ = (|A.det| : ℝ)⁻¹ := by
        rw [hBabs]
        have h2 : (|A.det| : ℝ)⁻¹ • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x
            ∂volume = (|A.det| : ℝ)⁻¹ • 1 := congrArg _ h1
        rw [h2, smul_eq_mul, mul_one]


/-- The multivariate Gaussian pdf is bounded above by its normalizing constant: the quadratic
form `uᵀ Σ⁻¹ u` in the exponent is nonnegative, so the exponential factor is at most `1`. -/
theorem multivariateGaussianPDF_le_const (n : ℕ) (m : Fin n → ℝ)
    (Cov : Matrix (Fin n) (Fin n) ℝ) (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    multivariateGaussianPDF n m Cov hC x
      ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt Cov.det)⁻¹ := by
  rw [multivariateGaussianPDF_eq n m Cov hC x]
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hSqrtdet : 0 < Real.sqrt Cov.det := Real.sqrt_pos.mpr hC.det_pos
  have hc₀ : 0 < ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt Cov.det)⁻¹ :=
    inv_pos.mpr (mul_pos h2pi hSqrtdet)
  have hCdet : IsUnit Cov.det := isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  have hCH : Covᵀ = Cov := by
    ext i j
    simpa using hC.1.apply i j
  have hCinvH : Cov⁻¹.IsHermitian := by
    have h1 : Cov⁻¹ᵀ = Cov⁻¹ := by
      rw [← transpose_nonsing_inv Cov hCdet, hCH]
    exact Matrix.ext (fun i j => by
      simpa using (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) h1).symm)
  have hCinvPSD : Cov⁻¹.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hCinvH (fun u => by
      have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hC.posSemidef (Cov⁻¹ *ᵥ u)
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Cov hCdet, Matrix.one_mulVec] at h
      simpa [dotProduct_comm] using h)
  have hquad : ∀ u : Fin n → ℝ, 0 ≤ (Cov⁻¹ *ᵥ u) ⬝ᵥ u := by
    intro u
    have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hCinvPSD u
    rwa [dotProduct_comm] at h
  have hquadx : 0 ≤ (Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m) :=
    hquad ((x : Fin n → ℝ) - m)
  have hexp : Real.exp (-(((Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ
      ((x : Fin n → ℝ) - m)) / 2)) ≤ 1 := by
    have hnn : (0:ℝ) ≤ (Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m) / 2 :=
      div_nonneg hquadx (by norm_num)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound := mul_le_mul_of_nonneg_left hexp hc₀.le
  rwa [mul_one] at hbound


/-- The observation density induced by the measurement model `y = A h + n` with independent
Gaussian noise `n ~ N(0, S)` (appendix_1.tex, Eq. (convolution) after the change of variables
`s = y - A h`): `f_y(y) = ∫ f_n(y - A h) f(h) dh`. For a pdf `f` this is the density of `y`. -/
noncomputable def fyPDF (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume


/-- Uniform convergence transfer (appendix_1.tex, first part of the proof of the main result):
if `f_h^{(K)} → f_h` uniformly then `f_y^{(K)} → f_y` uniformly, where
`f_y(y) = ∫ f_n(y - A h) f(h) dh`. Only integrability of the densities is assumed; the
pdf property is not needed for this step. -/
theorem uniform_convergence_fy
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (fh : EuclideanSpace ℝ (Fin n) → ℝ) (hfh : MeasureTheory.Integrable fh volume)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhK : ∀ K, MeasureTheory.Integrable (fhK K) volume)
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ y : EuclideanSpace ℝ (Fin n),
      |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| < ε := by
  have hAbs : 0 < |A.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp hA)
  have hne : |A.det| ≠ 0 := ne_of_gt hAbs
  obtain ⟨K₁, hK₁⟩ := hconv (ε * |A.det| / 2) (div_pos (mul_pos hε hAbs) two_pos)
  refine ⟨K₁, fun K hK y => ?_⟩
  simp only [fyPDF]
  -- measurability and mass of the pulled-back noise density
  have haM : AEStronglyMeasurable (noiseDens n S hS A y) volume := by
    have hcomp : noiseDens n S hS A y
        = (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
          (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
      funext h
      exact noiseDens_eq n S hS A y h
    rw [hcomp]
    exact ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
      (by fun_prop : Measurable (fun h : EuclideanSpace ℝ (Fin n) =>
        y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aestronglyMeasurable
  have haint : MeasureTheory.Integrable (noiseDens n S hS A y) volume :=
    Integrable.of_integral_ne_zero (by
      rw [integral_noise_pullback n S hS A hA y]
      exact inv_ne_zero hne)
  have hposa : ∀ h, 0 ≤ noiseDens n S hS A y h := by
    intro h
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    positivity
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hSqrtdet : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  have hc₀ : ∀ h, noiseDens n S hS A y h
      ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ := by
    intro h
    simp only [noiseDens]
    exact multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
  -- the products are integrable by domination against `c₀ * |f|`
  have hmeas1 : AEStronglyMeasurable (fun h => noiseDens n S hS A y h * fh h) volume :=
    haM.mul hfh.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun h => noiseDens n S hS A y h * fhK K h) volume :=
    haM.mul (hfhK K).aestronglyMeasurable
  have hprod1 : MeasureTheory.Integrable
      (fun h => noiseDens n S hS A y h * fh h) volume := by
    have hg1 : MeasureTheory.Integrable
        (fun h => ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * |fh h|) volume :=
      (Integrable.smul (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) hfh.abs).congr
        (Filter.Eventually.of_forall fun h => by simp)
    refine Integrable.mono' hg1 hmeas1 (Filter.Eventually.of_forall (fun h => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hposa h)]
    exact mul_le_mul_of_nonneg_right (hc₀ h) (abs_nonneg _)
  have hprod2 : MeasureTheory.Integrable
      (fun h => noiseDens n S hS A y h * fhK K h) volume := by
    have hg2 : MeasureTheory.Integrable
        (fun h => ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * |fhK K h|) volume :=
      (Integrable.smul (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        (hfhK K).abs).congr (Filter.Eventually.of_forall fun h => by simp)
    refine Integrable.mono' hg2 hmeas2 (Filter.Eventually.of_forall (fun h => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hposa h)]
    exact mul_le_mul_of_nonneg_right (hc₀ h) (abs_nonneg _)
  have hdif : MeasureTheory.Integrable
      (fun h => noiseDens n S hS A y h * (fh h - fhK K h)) volume := by
    have hEq : (fun h => noiseDens n S hS A y h * (fh h - fhK K h))
        = (fun h => noiseDens n S hS A y h * fh h)
          - (fun h => noiseDens n S hS A y h * fhK K h) := by
      funext h
      simp only [Pi.sub_apply]
      ring
    rw [hEq]
    exact hprod1.sub hprod2
  -- the quantitative chain
  rw [← integral_sub hprod1 hprod2]
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun h =>
    show noiseDens n S hS A y h * fh h - noiseDens n S hS A y h * fhK K h
      = noiseDens n S hS A y h * (fh h - fhK K h) from by ring))]
  calc |∫ h, noiseDens n S hS A y h * (fh h - fhK K h) ∂volume|
      ≤ ∫ h, |noiseDens n S hS A y h * (fh h - fhK K h)| ∂volume :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ h, (ε * |A.det| / 2) * noiseDens n S hS A y h ∂volume := by
        refine integral_mono_ae hdif.abs ?_
          (Filter.Eventually.of_forall (fun h => ?_))
        · exact Integrable.smul (ε * |A.det| / 2) haint
        · show |noiseDens n S hS A y h * (fh h - fhK K h)|
            ≤ (ε * |A.det| / 2) * noiseDens n S hS A y h
          rw [abs_mul, abs_of_nonneg (hposa h), mul_comm (ε * |A.det| / 2)
            (noiseDens n S hS A y h)]
          exact mul_le_mul_of_nonneg_left (le_of_lt (hK₁ K hK h)) (hposa h)
    _ = (ε * |A.det| / 2) * ∫ h, noiseDens n S hS A y h ∂volume :=
        integral_const_mul _ _
    _ = (ε * |A.det| / 2) * (|A.det| : ℝ)⁻¹ := by
        rw [integral_noise_pullback n S hS A hA y]
    _ = ε / 2 := by
        field_simp
    _ < ε := by linarith


/-! ## Pdf-side setup for the uniform convergence theorem (appendix_1.tex)

The uniformly convergent approximating sequence `f_h^{(K)}` is *assumed*, not constructed
(Gaussian mixture models are the motivating example, but play no role here). All that is
needed of `f_h` and every `f_h^{(K)}` for the convergence transfer is that they are pdfs
(nonnegative with total mass 1); continuity and vanishing at infinity are recorded as separate
hypotheses on `f_h` to match the setting of `appendix_1.tex`. -/


/-- `f` is a probability density function w.r.t. `volume` on `EuclideanSpace ℝ (Fin n)`:
nonnegative with total mass `1`. -/
def IsPdf (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  0 ≤ f ∧ ∫ x, f x ∂volume = 1


/-- A pdf is integrable: in Mathlib's definition of the Lebesgue integral, a function with
nonzero integral is automatically integrable (non-integrable functions have integral `0`). -/
theorem integrable_of_isPdf {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsPdf f) : MeasureTheory.Integrable f volume :=
  Integrable.of_integral_ne_zero (by rw [hf.2]; norm_num)


/-- `f` vanishes at infinity: `f x → 0` as `x` leaves every compact set. On the proper space
`EuclideanSpace ℝ (Fin n)` this is equivalent to `f x → 0` as `‖x‖ → ∞`. -/
def VanishesAtInfinity (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Tendsto f (cocompact (EuclideanSpace ℝ (Fin n))) (nhds 0)


set_option linter.unusedVariables false in
/-- Uniform convergence of the observation densities for a uniformly convergent sequence of
pdfs (`appendix_1.tex`, first part of the proof of the main result): if `f_h` is a continuous
pdf vanishing at infinity and `f_h^{(K)}` is a sequence of pdfs converging uniformly to `f_h`
(an assumption motivated by, but independent of, Theorem 5(a) of
Nguyen–Nguyen–Chamroukhi–McLachlan 2020), then the induced observation densities
`f_y^{(K)} → f_y` uniformly, where `f_y(y) = ∫ f_n(y - A h) f_h(h) dh`.

Continuity and vanishing at infinity are not needed for the convergence transfer; they are
recorded to match the setting of `appendix_1.tex` (`f_h ∈ C₀`). -/
theorem uniform_convergence_fy_pdf
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh)
    (hfhcont : Continuous fh)
    (hfh0 : VanishesAtInfinity fh)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ y : EuclideanSpace ℝ (Fin n),
      |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| < ε :=
  uniform_convergence_fy n S hS A hA fh (integrable_of_isPdf hfhpdf) fhK
    (fun K => integrable_of_isPdf (hfhKpdf K)) hconv ε hε


/-! ## Step 3: `f_y` is the density of the observation law

Here we prove that `f_y(y) = ∫ f_n(y - A h) f(h) dh` is indeed the density (w.r.t. `volume`)
of the random variable `y = A h + n` where `h` has density `f` and, independently,
`n ~ N(0, S)` has density `f_n = multivariateGaussianPDF n 0 S hS` (`appendix_1.tex`,
the identification of `f_y` as the pdf of the observations). The route is characteristic
functions (`Measure.ext_of_charFun`): the law `map (A · + ·) (μ_h ×ᵐ μ_n)` and
`volume.withDensity (fun y => ENNReal.ofReal (f_y y))` are finite measures whose
characteristic functions are computed and shown to coincide; both factor as

  `(∫ h, exp(i⟪A h, t⟫) f(h) dh) * charFun(μ_n)(t)`. -/


/-- The characteristic function of the law of `y = A h + n`: the map `p ↦ A p.1 + p.2`
pushes forward the product of the law of `h` (density `f`) and the law of `n`
(density `f_n = N(0, S)`); its characteristic function factors into the `h`-integral
against `f` times the characteristic function of the noise. -/
theorem charFun_map_fy
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun (Measure.map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2)
        ((volume.withDensity (fun h => ENNReal.ofReal (f h))).prod
          (volume.withDensity (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))))
      t
      = (∫ h : EuclideanSpace ℝ (Fin n), Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h ∂volume)
        * charFun (volume.withDensity (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))) t := by
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  -- finiteness of the two density measures
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint
      (Eventually.of_forall fun x => hposf x), hf.2, ENNReal.ofReal_one]
  set μh : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h)) with hμhdef
  set μn : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)) with hμndef
  have hμhfin : MeasureTheory.IsFiniteMeasure μh :=
    isFiniteMeasure_withDensity (by rw [hlintf]; simp)
  have hμnfin : MeasureTheory.IsFiniteMeasure μn :=
    isFiniteMeasure_gaussianPDF_withDensity n (0 : Fin n → ℝ) S hS
  -- measurability of the joint map and of the complex exponential
  have hFmeas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) := by fun_prop
  have hexpmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by fun_prop
  -- the exponential splits over the two summands of `A p.1 + p.2`
  have hsplit : ∀ (a y : EuclideanSpace ℝ (Fin n)),
      Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (a : Fin n → ℝ)) + y) t) * Complex.I)
        = Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (a : Fin n → ℝ))) t) * Complex.I)
          * Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) := by
    intro a y
    rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  -- the integrand is bounded by 1, hence integrable on the product measure
  have hint1 : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ
          (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) * Complex.I))
      (μh.prod μn) := by
    have h1 : MeasureTheory.Integrable
        (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (1 : ℝ))
        (μh.prod μn) := integrable_const (1 : ℝ)
    refine h1.mono' (hexpmeas.comp hFmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    rw [hsplit p.1 p.2, norm_mul, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- the same integrand in split form (a.e.-equal, hence integrable)
  have hint1' : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) * Complex.I)
          * Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I))
      (μh.prod μn) :=
    hint1.congr (Filter.Eventually.of_forall fun p => hsplit p.1 p.2)
  -- split the exponential inside the pair integral (before Fubini, to keep the
  -- subsequent rewrites away from beta-redexes)
  have hpre : ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ
        (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) * Complex.I) ∂(μh.prod μn)
    = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) * Complex.I)
          * Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I) ∂(μh.prod μn) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => hsplit p.1 p.2)
  -- the inner `y`-integral is against the withDensity of `f` ...
  have hcongr : ∫ h : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (f h)).toReal • Complex.exp (Complex.ofReal
        (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) ∂volume
    = ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show (ENNReal.ofReal (f h)).toReal
        • Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
      = Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h
    rw [ENNReal.toReal_ofReal (hposf h), Complex.real_smul, mul_comm]
  -- inner `y`-integral: factor off the constant and recognize the noise characteristic
  -- function (as a pointwise statement so that `h` is a free variable during the rewrite)
  have hinner : ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
          * Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn
      = Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
        * charFun μn t := by
    intro h
    rw [integral_const_mul _
      (fun y => Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)), ← charFun_apply]
  have houter : ∫ h : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
        * Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn ∂μh
    = ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
          * charFun μn t ∂μh :=
    integral_congr_ae (Filter.Eventually.of_forall hinner)
  have houter2 : ∫ h : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
        * charFun μn t ∂μh
    = (∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) ∂μh)
      * charFun μn t :=
    integral_mul_const (charFun μn t)
      (fun (h : EuclideanSpace ℝ (Fin n)) => Complex.exp (Complex.ofReal
        (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
  have hmeasφ : AEMeasurable (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfint.aemeasurable
  have hdens : ∫ h : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) ∂μh
    = ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h
        ∂volume := by
    rw [hμhdef, integral_withDensity_eq_integral_toReal_smul₀ hmeasφ (by simp)
      (fun h => Complex.exp (Complex.ofReal
        (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))]
    exact hcongr
  calc charFun (Measure.map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) (μh.prod μn)) t
      = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ
            (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) * Complex.I)
          ∂(μh.prod μn) := by
        rw [charFun_apply, integral_map hFmeas.aemeasurable
          hexpmeas.aestronglyMeasurable]
    _ = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) * Complex.I)
            * Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I) ∂(μh.prod μn) := hpre
    _ = ∫ h : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
            * Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn ∂μh := by
        rw [integral_prod _ hint1']
    _ = ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal
              (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
            * charFun μn t ∂μh := houter
    _ = (∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) ∂μh)
        * charFun μn t := houter2
    _ = (∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h ∂volume)
        * charFun (volume.withDensity (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))) t :=
      congrArg (fun I : ℂ => I * charFun μn t) hdens


/-- Left-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`: for any
`c`, integrals along `y ↦ toLp 2 (c + y)` are unchanged. -/
theorem integral_toLp_trans {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] [OpensMeasurableSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] [SecondCountableTopology F]
    (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ y : EuclideanSpace ℝ (Fin n),
      g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume
      = ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  have hTmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (c + (y : Fin n → ℝ))) := by fun_prop
  have hTmap : MeasureTheory.Measure.map (fun y : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume = volume := by
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ)))
        = (WithLp.toLp 2 c + ·) := by
      funext y
      simp only [WithLp.toLp_add, WithLp.toLp_ofLp]
    rw [heq, MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  calc ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume
      = ∫ y : EuclideanSpace ℝ (Fin n), g y
          ∂(MeasureTheory.Measure.map (fun y : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume) :=
        (integral_map hTmeas.aemeasurable (by rw [hTmap]; exact hg)).symm
    _ = ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by rw [hTmap]

/-- Left-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`: for any
`c`, integrals along `y ↦ toLp 2 (c + y)` are unchanged (ℝ≥0∞ version). -/
theorem lintegral_toLp_trans (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n),
      g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume
      = ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  have hTmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (c + (y : Fin n → ℝ))) := by fun_prop
  have hTmap : MeasureTheory.Measure.map (fun y : EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume = volume := by
    have heq : (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ)))
        = (WithLp.toLp 2 c + ·) := by
      funext y
      simp only [WithLp.toLp_add, WithLp.toLp_ofLp]
    rw [heq, MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  calc ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume
      = ∫⁻ y : EuclideanSpace ℝ (Fin n), g y
          ∂(MeasureTheory.Measure.map (fun y : EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume) :=
        (lintegral_map hg hTmeas).symm
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by rw [hTmap]

/-- For fixed `h`, the density `y ↦ f_n(y - A h)` is the noise pdf translated by `-A h`, so it
has Lebesgue mass `1`. -/
theorem lintegral_noiseDens_mass
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (noiseDens n S hS A y x) ∂volume = 1 := by
  have hposn : ∀ z : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z := by
    intro z
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS z]
    positivity
  have hintn : ∫ z : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf : ∀ z : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS z
          = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z := fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun z => (hpdf z).symm)).trans h1
  have hfnint : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) volume :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hintn]; exact one_ne_zero)
  have hlintn : ∫⁻ z : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
      (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint
      (Filter.Eventually.of_forall fun z => hposn z), hintn, ENNReal.ofReal_one]
  have hndT : ∀ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y x
      = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro y
    simp only [noiseDens]
    rw [show ((y : Fin n → ℝ) - A.mulVec (x : Fin n → ℝ))
        = (-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ)) from by ring]
  calc ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (noiseDens n S hS A y x) ∂volume
      = ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
            (WithLp.toLp 2 ((-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ))))) ∂volume :=
        lintegral_congr (fun y => by rw [hndT y])
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y) ∂volume :=
        lintegral_toLp_trans n (-(A.mulVec (x : Fin n → ℝ)))
          (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))
          (ENNReal.measurable_ofReal.comp
            (measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS))
    _ = 1 := hlintn

set_option maxHeartbeats 10000000 in
/-- Tonelli's theorem on the coupled integrand `(y, h) ↦ f_n(y - A h) f(h)`: the `ℝ≥0∞`-norm
integral of the Bochner integrand in `charFun_fyPDF_density` over `volume.prod volume` equals
`1`, so the integrand is integrable although both factors have infinite mass. -/
theorem lintegral_enorm_noiseDens_mul
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ ∂(volume.prod volume) = 1 := by
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hposa : ∀ (y h : EuclideanSpace ℝ (Fin n)), 0 ≤ noiseDens n S hS A y h := by
    intro y h
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    positivity
  have hfnmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hpt : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ
        = ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2) := by
    intro p
    have habs : |noiseDens n S hS A p.1 p.2 * f p.2|
        = noiseDens n S hS A p.1 p.2 * f p.2 := by
      rw [abs_mul, abs_of_nonneg (hposa p.1 p.2), abs_of_nonneg (hposf p.2)]
    calc ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ
        = ENNReal.ofReal |noiseDens n S hS A p.1 p.2 * f p.2| :=
          Real.enorm_eq_ofReal_abs _
      _ = ENNReal.ofReal (noiseDens n S hS A p.1 p.2 * f p.2) := by rw [habs]
      _ = ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2) :=
          ENNReal.ofReal_mul (hposa p.1 p.2)
  have hmeas2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1))
      (volume.prod volume) :=
    (ENNReal.measurable_ofReal.comp (hndmeas.comp measurable_swap)).aemeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable hfint.aemeasurable.comp_fst)
  have hswap : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2)
      ∂(volume.prod volume)
    = ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1)
        ∂(volume.prod volume) :=
    (lintegral_prod_swap (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2))).symm
  have hton : ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1)
      ∂(volume.prod volume)
    = ∫⁻ x : EuclideanSpace ℝ (Fin n), ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume ∂volume :=
    lintegral_prod (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1)) hmeas2
  have hinner : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume
      = ENNReal.ofReal (f x) := by
    intro x
    have hmeasY : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (noiseDens n S hS A y x)) := by
      have h0 : Measurable ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (noiseDens n S hS A p.1 p.2)) ∘
        (fun y : EuclideanSpace ℝ (Fin n) => (y, x))) :=
        (ENNReal.measurable_ofReal.comp hndmeas).comp
          (by fun_prop : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (y, x)))
      have hfun : ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (noiseDens n S hS A p.1 p.2)) ∘
        (fun y : EuclideanSpace ℝ (Fin n) => (y, x)))
          = (fun y : EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (noiseDens n S hS A y x)) := by
        funext y
        simp [Function.comp]
      rw [hfun] at h0
      exact h0
    have h1 := lintegral_mul_const (μ := volume) (ENNReal.ofReal (f x)) hmeasY
    rw [lintegral_noiseDens_mass n S hS A x, one_mul] at h1
    exact h1
  calc ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ ∂(volume.prod volume)
      = ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2)
          ∂(volume.prod volume) := lintegral_congr hpt
    _ = ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1)
          ∂(volume.prod volume) := hswap
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin n), ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume ∂volume := hton
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume :=
        lintegral_congr (fun x => hinner x)
    _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal hfint
          (Filter.Eventually.of_forall fun x => hposf x), hf.2, ENNReal.ofReal_one]

set_option maxHeartbeats 2000000 in
/-- The density-side characteristic function: the characteristic function of the measure with
density `f_y(y) = ∫ f_n(y - A h) f(h) dh` factors into the same `h`-integral times the
characteristic function of the noise. Fubini is applied on `volume.prod volume` (both factors
infinite measures!), so integrability of the joint integrand is proved by Tonelli:
`∫⁻ ‖G‖ = (∫⁻ f)(∫⁻ f_n) = 1`. -/
theorem charFun_fyPDF_density
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun (volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A f y))) t
      = (∫ h : EuclideanSpace ℝ (Fin n), Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) * f h ∂volume)
        * charFun (volume.withDensity (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))) t := by
  classical
  -- pointwise nonnegativity and integrability of the two pdfs
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hposn : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := by
    intro x
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS x]
    positivity
  have hposa : ∀ (y h : EuclideanSpace ℝ (Fin n)), 0 ≤ noiseDens n S hS A y h := by
    intro y h
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    positivity
  have hposfy : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ fyPDF n S hS A f y := by
    intro y
    simp only [fyPDF]
    exact integral_nonneg fun h => mul_nonneg (hposa y h) (hposf h)
  -- mass of the noise pdf
  have hintn : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x
          = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  have hfnint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) volume :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hintn]; exact one_ne_zero)
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint
      (Filter.Eventually.of_forall fun x => hposf x), hf.2, ENNReal.ofReal_one]
  have hlintn : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
      (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint
      (Filter.Eventually.of_forall fun x => hposn x), hintn, ENNReal.ofReal_one]
  -- translation invariance of `volume` is provided by `integral_toLp_trans` and
  -- `lintegral_toLp_trans`; the Tonelli integrability is provided by
  -- `lintegral_enorm_noiseDens_mul`
  -- `noiseDens` as the noise pdf evaluated along the translation `y ↦ y - A h`
  have hndT : ∀ (h y : EuclideanSpace ℝ (Fin n)), noiseDens n S hS A y h
      = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro h y
    simp only [noiseDens]
    rw [show ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))
        = (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)) from by ring]
  -- measurability facts
  have hfnmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hφmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Complex.exp (Complex.ofReal (inner ℝ p.1 t) * Complex.I)) := by fun_prop
  -- replace `f` by a measurable representative
  have hfae : AEMeasurable f volume := hfint.aemeasurable
  set f' : EuclideanSpace ℝ (Fin n) → ℝ := hfae.mk f with hf'def
  have hf'meas : Measurable f' := hfae.measurable_mk
  have hf'ae : f =ᵐ[volume] f' := hfae.ae_eq_mk
  -- inner integrals agree a.e., hence pointwise after swapping the integrand
  have hfy' : ∀ y : EuclideanSpace ℝ (Fin n),
      ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f' h ∂volume
        = ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume := by
    intro y
    exact integral_congr_ae (hf'ae.mono fun x hx => by simp only [hx])
  -- measurability of the map `y ↦ ∫ f_n(y - A h) f'(h) dh` via Fubini's measurability lemma
  have hmeasF' : StronglyMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f' h ∂volume) :=
    (hndmeas.comp measurable_swap).mul (hf'meas.comp measurable_fst) |>.stronglyMeasurable.integral_prod_left
  -- hence a.e.-measurability of the density `f_y`
  have hmeasrho : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (fyPDF n S hS A f y)) volume :=
    AEMeasurable.congr (ENNReal.measurable_ofReal.comp_aemeasurable hmeasF'.aemeasurable)
      (Filter.Eventually.of_forall fun y => by
        simp only [fyPDF]
        exact congrArg ENNReal.ofReal (hfy' y))
  -- Tonelli: the coupled integrand is integrable on the product
  have hDint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2 * f p.2) (volume.prod volume) :=
    ⟨hndmeas.aestronglyMeasurable.mul hfint.1.comp_snd, by
      rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_noiseDens_mul n S hS A f hf]
      exact ENNReal.one_lt_top⟩
  -- the noise measure, as a named local abbreviation
  set μn : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
      (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)) with hμndef
  have hexpmeas : Measurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by fun_prop
  -- the characteristic function of the noise in integral form
  have hmeasφn : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfnint.aemeasurable
  have hcharN : ∫ z : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
        * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) ∂volume
    = charFun μn t := by
    rw [hμndef, charFun_apply, integral_withDensity_eq_integral_toReal_smul₀
      hmeasφn (by simp)
      (fun z => Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
        * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)
      = (ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)).toReal
          • Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
    rw [Complex.real_smul, ENNReal.toReal_ofReal (hposn z), mul_comm]
  -- Fubini: the complex integrand is dominated by the Tonelli-integrable `hDint`
  have hGaes : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun (y h : EuclideanSpace ℝ (Fin n)) =>
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)))
      (volume.prod volume) :=
    (hφmeas.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp hndmeas).aemeasurable.aestronglyMeasurable.mul
        ((Complex.measurable_ofReal.comp_aemeasurable hfint.aemeasurable.comp_snd).aestronglyMeasurable)))
  have hintH : MeasureTheory.Integrable
      (Function.uncurry fun (y h : EuclideanSpace ℝ (Fin n)) =>
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)))
      (volume.prod volume) := by
    refine hDint.mono' hGaes (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    show ‖(Complex.exp (Complex.ofReal (inner ℝ p.1 t) * Complex.I)) *
        (Complex.ofReal (noiseDens n S hS A p.1 p.2) * Complex.ofReal (f p.2))‖
      = noiseDens n S hS A p.1 p.2 * f p.2
    have hn1 : ‖Complex.ofReal (noiseDens n S hS A p.1 p.2)‖
        = |noiseDens n S hS A p.1 p.2| := RCLike.norm_ofReal _
    have hf1 : ‖Complex.ofReal (f p.2)‖ = |f p.2| := RCLike.norm_ofReal _
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hn1, hf1,
      abs_of_nonneg (hposa p.1 p.2), abs_of_nonneg (hposf p.2)]
  -- per `y`: move the constant factor out of the `h`-integral
  have hinner : ∀ y : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n),
            noiseDens n S hS A y h * f h ∂volume)
        = ∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
              * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume := by
    intro y
    have h1 := integral_const_mul (μ := volume)
      (Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I))
      (fun h : EuclideanSpace ℝ (Fin n) =>
        Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h))
    have h2 : ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h) ∂volume
      = Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n),
          noiseDens n S hS A y h * f h ∂volume) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun h =>
        (Complex.ofReal_mul (noiseDens n S hS A y h) (f h)).symm)]
      exact integral_ofReal
    calc Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        * Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n),
          noiseDens n S hS A y h * f h ∂volume)
      = Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * ∫ h : EuclideanSpace ℝ (Fin n),
            Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h) ∂volume := by rw [h2]
      _ = ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
            * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume :=
          h1.symm
  -- per `h`: move the `f`-factor out of the `y`-integral
  have hstep4 : ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume
      = (∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
            * Complex.ofReal (noiseDens n S hS A y h) ∂volume)
          * Complex.ofReal (f h) := by
    intro h
    have h1 := integral_mul_const (μ := volume) (Complex.ofReal (f h)) (fun y : EuclideanSpace ℝ (Fin n) =>
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        * Complex.ofReal (noiseDens n S hS A y h))
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans h1
    ring
  -- per `h`: the translated inner `y`-integral is the noise characteristic function
  have hinner2 : ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * Complex.ofReal (noiseDens n S hS A y h) ∂volume
      = charFun μn t * Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) := by
    intro h
    have hφsh : ∀ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          = Complex.exp (Complex.ofReal
              (inner ℝ (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) t)
              * Complex.I)
            * Complex.exp (Complex.ofReal
                (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) := by
      intro y
      have heq : (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))
          + (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) = y := by
        rw [← WithLp.toLp_add, show (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))
            + A.mulVec (h : Fin n → ℝ) = (y : Fin n → ℝ) by ring]
      conv_lhs => rw [← heq]
      rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
    have hGtrans : ∀ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
            * Complex.ofReal (noiseDens n S hS A y h)
          = (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
                * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))
            * Complex.exp (Complex.ofReal
                (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) := by
      intro y
      rw [hndT h y, hφsh y, mul_right_comm]
    have hmeasg : MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) =>
          Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
            * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)) volume :=
      (hexpmeas.mul (Complex.measurable_ofReal.comp hfnmeas)).aestronglyMeasurable
    calc ∫ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * Complex.ofReal (noiseDens n S hS A y h) ∂volume
      = ∫ y : EuclideanSpace ℝ (Fin n),
          (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
                * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))
            * Complex.exp (Complex.ofReal
                (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
          ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall hGtrans)
      _ = (∫ y : EuclideanSpace ℝ (Fin n),
          (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
                * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))
          ∂volume)
        * Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) :=
        integral_mul_const (Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
                * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))))
      _ = (∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
            * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y) ∂volume)
        * Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) :=
        congrArg (fun I : ℂ => I * Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
          (integral_toLp_trans n (-(A.mulVec (h : Fin n → ℝ)))
            (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
                * Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)) hmeasg)
      _ = charFun μn t * Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) := by
        rw [hcharN]
  -- final assembly
  calc charFun (volume.withDensity (fun y : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (fyPDF n S hS A f y))) t
      = ∫ y : EuclideanSpace ℝ (Fin n),
          (ENNReal.ofReal (fyPDF n S hS A f y)).toReal
            • Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂volume := by
        rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul₀ hmeasrho (by simp)
          (fun y => Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I))]
    _ = ∫ y : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        * Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n),
          noiseDens n S hS A y h * f h ∂volume) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show (ENNReal.ofReal (fyPDF n S hS A f y)).toReal
          • Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        = Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n),
            noiseDens n S hS A y h * f h ∂volume)
      rw [Complex.real_smul, ENNReal.toReal_ofReal (hposfy y), mul_comm]
      simp only [fyPDF]
    _ = ∫ y : EuclideanSpace ℝ (Fin n), ∫ h : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = ∫ h : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
        * (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume ∂volume :=
      integral_integral_swap hintH
    _ = ∫ h : EuclideanSpace ℝ (Fin n),
      (∫ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
          * Complex.ofReal (noiseDens n S hS A y h) ∂volume)
        * Complex.ofReal (f h) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hstep4)
    _ = ∫ h : EuclideanSpace ℝ (Fin n),
      (charFun μn t * Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
        * Complex.ofReal (f h) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun h => by
        show (∫ y : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)
              * Complex.ofReal (noiseDens n S hS A y h) ∂volume)
            * Complex.ofReal (f h)
          = (charFun μn t * Complex.exp (Complex.ofReal
              (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
            * Complex.ofReal (f h)
        rw [hinner2 h])
    _ = ∫ h : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal
          (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
        * f h * charFun μn t ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun h => by ring)
    _ = (∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
          * f h ∂volume)
      * charFun μn t :=
      integral_mul_const (charFun μn t) (fun h : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal
            (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I)
          * f h)

/-- `f_y(y) = ∫ f_n(y - A h) f(h) dh` is a pdf: nonnegative (integrandwise) with total
mass `1` (Fubini on the Tonelli-integrable joint integrand, then the translation `y ↦ y - A h`
in the inner integral). -/
theorem isPdf_fyPDF
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    IsPdf (fyPDF n S hS A f) := by
  classical
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hfnmeas : Measurable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hndT : ∀ (h y : EuclideanSpace ℝ (Fin n)), noiseDens n S hS A y h
      = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro h y
    simp only [noiseDens]
    rw [show ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))
        = (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)) from by ring]
  have hintn : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x
          = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  -- mass of the translated noise density along each `h`
  have hmassy : ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume = 1 := by
    intro h
    calc ∫ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume
        = ∫ y : EuclideanSpace ℝ (Fin n),
            multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
              (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) ∂volume :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => hndT h y)
      _ = ∫ y : EuclideanSpace ℝ (Fin n),
            multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y ∂volume :=
          integral_toLp_trans n (-(A.mulVec (h : Fin n → ℝ)))
            (fun z : EuclideanSpace ℝ (Fin n) =>
              multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) hfnmeas.aestronglyMeasurable
      _ = 1 := hintn
  -- Fubini on the ℝ-valued joint integrand
  have hDint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2 * f p.2) (volume.prod volume) :=
    ⟨hndmeas.aestronglyMeasurable.mul hfint.1.comp_snd, by
      rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_noiseDens_mul n S hS A f hf]
      exact ENNReal.one_lt_top⟩
  refine ⟨?_, ?_⟩
  · intro y
    simp only [fyPDF]
    exact integral_nonneg fun h => mul_nonneg
      (by
        simp only [noiseDens]
        rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
        positivity)
      (hposf h)
  · calc ∫ y : EuclideanSpace ℝ (Fin n), fyPDF n S hS A f y ∂volume
        = ∫ y : EuclideanSpace ℝ (Fin n), ∫ h : EuclideanSpace ℝ (Fin n),
            noiseDens n S hS A y h * f h ∂volume ∂volume := by
          simp only [fyPDF]
      _ = ∫ h : EuclideanSpace ℝ (Fin n), ∫ y : EuclideanSpace ℝ (Fin n),
            noiseDens n S hS A y h * f h ∂volume ∂volume :=
          integral_integral_swap hDint
      _ = ∫ h : EuclideanSpace ℝ (Fin n), f h ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          have h1 := integral_mul_const (μ := volume) (f h)
            (fun y : EuclideanSpace ℝ (Fin n) => noiseDens n S hS A y h)
          rw [hmassy h, one_mul] at h1
          exact h1
      _ = 1 := hf.2


/-- Assembly of Step 3: the law of `y = A h + n` equals `volume.withDensity (fun y =>
ENNReal.ofReal (f_y y))`, i.e. `f_y` is the pdf of the observations. Both sides are finite
measures on `EuclideanSpace ℝ (Fin n)` with equal characteristic functions
(`charFun_map_fy` and `charFun_fyPDF_density`), so `Measure.ext_of_charFun` applies. -/
theorem fyPDF_eq_map
    (n : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    Measure.map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2)
        ((volume.withDensity (fun h => ENNReal.ofReal (f h))).prod
          (volume.withDensity (fun y => ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))))
      = volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A f y)) := by
  classical
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hpdfpdf : IsPdf (fyPDF n S hS A f) := isPdf_fyPDF n S hS A f hf
  have hposfy : 0 ≤ fyPDF n S hS A f := hpdfpdf.1
  have hpdfint : MeasureTheory.Integrable (fyPDF n S hS A f) volume :=
    integrable_of_isPdf hpdfpdf
  -- finiteness of the two density measures on the left
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint
      (Filter.Eventually.of_forall fun x => hposf x), hf.2, ENNReal.ofReal_one]
  have hposn : ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := by
    intro x
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS x]
    positivity
  have hintn : ∫ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf : ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x
          = multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  have hfnint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) volume :=
    MeasureTheory.Integrable.of_integral_ne_zero (by rw [hintn]; exact one_ne_zero)
  have hlintn : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
      (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint
      (Filter.Eventually.of_forall fun x => hposn x), hintn, ENNReal.ofReal_one]
  have hμhfin : MeasureTheory.IsFiniteMeasure
      (volume.withDensity (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h))) :=
    isFiniteMeasure_withDensity (by rw [hlintf]; simp)
  have hμnfin : MeasureTheory.IsFiniteMeasure
      (volume.withDensity (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal
        (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))) :=
    isFiniteMeasure_gaussianPDF_withDensity n (0 : Fin n → ℝ) S hS
  -- finiteness of the right-hand side: `f_y` has mass `1`
  have hrhsfin : MeasureTheory.IsFiniteMeasure
      (volume.withDensity (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (fyPDF n S hS A f y))) :=
    isFiniteMeasure_withDensity (by
      rw [← ofReal_integral_eq_lintegral_ofReal hpdfint
        (Filter.Eventually.of_forall fun y => hposfy y), hpdfpdf.2, ENNReal.ofReal_one]
      exact ENNReal.one_ne_top)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_fy n S hS A f hf t, charFun_fyPDF_density n S hS A f hf t]



