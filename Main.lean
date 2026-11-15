module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped Matrix MatrixOrder ENNReal

--
-- definitions
--

/-- The multivariate Gaussian probability density function. -/
noncomputable def multivariateGaussianPDF
    -- Let n be a natural number.
    (n : ℕ)
    -- Mean vector in R^n.
    (mean : Fin n → ℝ)
    -- Covariance matrix in R^{n × n}.
    (Cov : Matrix (Fin n) (Fin n) ℝ)
    -- The covariance matrix should be positive definite.
    (_ : Cov.PosDef)
    -- The argument of the PDF lives in Eucledian R^n.
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -- The usual multivariate Gaussian PDF formula.
  let d := x - mean
  let quadForm := (mulVec (Cov⁻¹) d) ⬝ᵥ d
  let normalization := ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (Cov.det))⁻¹
  normalization * Real.exp (-(quadForm / 2))

/-- The Gaussian noise density `n ~ N(0, S)` evaluated along the affine map `h ↦ y - A h`. -/
noncomputable def noiseDens
    -- Let n be a natural number.
    (n : ℕ)
    -- Let S be a matrix in R^{n × n}.
    (S : Matrix (Fin n) (Fin n) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{n × n}.
    (A : Matrix (Fin n) (Fin n) ℝ)
    -- Let y be a vector in R^n.
    (y : EuclideanSpace ℝ (Fin n))
    -- Let h be a vector in R^n.
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
    (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))

/-- The observation density induced by the measurement model `y = A h + n` with independent Gaussian noise `n ~ N(0, S)`.
Convolution after the change of variables `s = y - A h`: `f_y(y) = ∫ f_n(y - A h) f(h) dh`. -/
noncomputable def fyPDF
    -- Let n be a natural number.
    (n : ℕ)
    -- Let S be a matrix in R^{n × n}.
    (S : Matrix (Fin n) (Fin n) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{n × n}.
    (A : Matrix (Fin n) (Fin n) ℝ)
    -- Let f be a function from R^n to R.
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let y be a vector in R^n.
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -- Note that `noiseDens` does the flip `y - A h`.
  ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume

/-- The conditional mean estimate associated with a pdf `f` in the model `y = A h + n`.
This is a Bochner integral of a `EuclideanSpace ℝ (Fin n)`-valued integrand.
For `f := fhK K` this is `ĥ^{(K)}` and for `f := fh` this is `ĥ`. -/
public noncomputable def cme
    -- Let n be a natural number.
    (n : ℕ)
    -- Let S be a matrix in R^{n × n}.
    (S : Matrix (Fin n) (Fin n) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{n × n}.
    (A : Matrix (Fin n) (Fin n) ℝ)
    -- Let f be a function from R^n to R.
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let y be a vector in R^n.
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  -- `∫ h · f_n(y - A h) f(h) / f_y(y) dh`, where `f_y` is the observation density `fyPDF` induced by `f`.
  ∫ h : EuclideanSpace ℝ (Fin n), ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h

/-- Rectangular noise density: the Gaussian `f_n = N(0, S)` on `ℝ^m` evaluated at
`y − A h`, for an observation matrix `A : ℝ^n → ℝ^m`. -/
noncomputable def noiseDensR
    -- Let m, n be natural numbers.
    (m n : ℕ)
    -- Let S be a matrix in R^{m × m}.
    (S : Matrix (Fin m) (Fin m) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{m × n}.
    (A : Matrix (Fin m) (Fin n) ℝ)
    -- Let y be a vector in R^m.
    (y : EuclideanSpace ℝ (Fin m))
    -- Let h be a vector in R^n.
    (h : EuclideanSpace ℝ (Fin n)) : ℝ :=
  multivariateGaussianPDF m (0 : Fin m → ℝ) S hS
    (WithLp.toLp 2 ((y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ)))

/-- Rectangular marginal density `f_y(y) = ∫ f_n(y − A h) f(h) dh`. -/
noncomputable def fyPDFR
    -- Let m, n be natural numbers.
    (m n : ℕ)
    -- Let S be a matrix in R^{m × m}.
    (S : Matrix (Fin m) (Fin m) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{m × n}.
    (A : Matrix (Fin m) (Fin n) ℝ)
    -- Let f be a function from R^n to R.
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let y be a vector in R^m.
    (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  -- Note that `noiseDensR` does the flip `y - A h`.
  ∫ h : EuclideanSpace ℝ (Fin n), noiseDensR m n S hS A y h * f h ∂volume

/-- Rectangular conditional mean estimate `ĥ(y) = ∫ h f_n(y − A h) f(h) / f_y(y) dh ∈ ℝ^n`. -/
noncomputable def cmeR
    -- Let m, n be natural numbers.
    (m n : ℕ)
    -- Let S be a matrix in R^{m × m}.
    (S : Matrix (Fin m) (Fin m) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{m × n}.
    (A : Matrix (Fin m) (Fin n) ℝ)
    -- Let f be a function from R^n to R.
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let y be a vector in R^m.
    (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  ∫ h : EuclideanSpace ℝ (Fin n), ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h

/-- `f` is a probability density function w.r.t. `volume` on `EuclideanSpace ℝ (Fin n)`: nonnegative with total mass `1`. -/
public def IsPdf (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  0 ≤ f ∧ ∫ x, f x ∂volume = 1

/-- `f` vanishes at infinity: `f x → 0` as `x` leaves every compact set. On the proper space
`EuclideanSpace ℝ (Fin n)` this is equivalent to `f x → 0` as `‖x‖ → ∞`. -/
def VanishesAtInfinity (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Tendsto f (cocompact (EuclideanSpace ℝ (Fin n))) (nhds 0)

--
-- theorems
--

/-- `(Aᵀ)⁻¹ = (A⁻¹)ᵀ` for a matrix with unit determinant, used to give the transposed matrix of
the change of variables `h ↦ y - A h` a unit. -/
theorem transpose_nonsing_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    (Aᵀ)⁻¹ = (A⁻¹)ᵀ := by
  have hTT : Aᵀ * (A⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul (M := A⁻¹) (N := A), Matrix.nonsing_inv_mul A hA,
      Matrix.transpose_one]
  rw [Matrix.inv_eq_right_inv hTT]

/-- The covariance matrix `Σ̃ = A⁻¹ S A⁻ᵀ` of the Gaussian obtained from the change of
variables `h ↦ y - A h` is positive definite (Step 1 of
`plan_integral_norm_gaussian_bounded.md`: "first construct `hΣ̃`"). -/
theorem sigmaTilde_posDef (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) : (A⁻¹ * S * A⁻¹ᵀ).PosDef := by
  have hATU : IsUnit Aᵀ :=
    Matrix.isUnit_iff_isUnit_det Aᵀ |>.mpr
      (by
        rw [Matrix.det_transpose]; exact hA)
  have hTU : IsUnit ((A⁻¹)ᵀ) := by
    rw [← transpose_nonsing_inv A hA]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hATU
  have hstar : star ((A⁻¹)ᵀ) = A⁻¹ := by
    ext i j
    simp
  have hMid : star ((A⁻¹)ᵀ) * S * (A⁻¹)ᵀ = A⁻¹ * S * (A⁻¹)ᵀ := by rw [hstar]
  rw [← hMid, Matrix.posDef_iff_posSemidef_and_mulVec_injective]
  refine ⟨(Matrix.IsUnit.posSemidef_star_left_conjugate_iff hTU).mpr hS.posSemidef, ?_⟩
  have hcancelT : Aᵀ * (A⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul (M := A⁻¹) (N := A), Matrix.nonsing_inv_mul A hA,
      Matrix.transpose_one]
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
theorem quadForm_eq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hSdet : IsUnit S.det)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (u w : Fin n → ℝ) :
    (((A⁻¹ * S * (A⁻¹)ᵀ)⁻¹ *ᵥ (u - A⁻¹ *ᵥ w)) ⬝ᵥ (u - A⁻¹ *ᵥ w)) =
      ((S⁻¹ *ᵥ (w - A *ᵥ u)) ⬝ᵥ (w - A *ᵥ u)) := by
  have hAA : A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = S * (A⁻¹)ᵀ := by
    rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc A, Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
  have h1 : Aᵀ * S⁻¹ * A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = 1 := by
    have h2 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
    calc
      Aᵀ * S⁻¹ * A * ((A⁻¹ * S) * (A⁻¹)ᵀ) = Aᵀ * S⁻¹ * (A * ((A⁻¹ * S) * (A⁻¹)ᵀ)) :=
        Matrix.mul_assoc _ _ _
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
theorem density_id (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n))
    (hSig : (A⁻¹ * S * A⁻¹ᵀ).PosDef) (h : EuclideanSpace ℝ (Fin n)) :
    (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)) *
        multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) =
      multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig h := by
  have hSdetPos : 0 < S.det := hS.det_pos
  have hSU : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetPos)
  have hd1 : (A⁻¹).det = (A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv]; norm_num
  have hSigdet : ((A⁻¹ * S * (A⁻¹)ᵀ).det) = S.det / (A.det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd1, mul_comm ((A.det)⁻¹) S.det,
      mul_assoc S.det ((A.det)⁻¹) ((A.det)⁻¹), div_eq_mul_inv, ← inv_pow (A.det) 2,
      pow_two ((A.det)⁻¹)]
  have hAdet2 : ((A⁻¹ * (A⁻¹)ᵀ).det) = ((A⁻¹).det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two ((A⁻¹).det)]
  have hAdetc : (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det)) = abs A.det := by
    rw [hAdet2, hd1, inv_pow (A.det) 2, Real.sqrt_inv, Real.sqrt_sq_eq_abs, one_div, inv_inv]
  have hKey :
    (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det)) * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (S.det))⁻¹) =
      (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt ((A⁻¹ * S * (A⁻¹)ᵀ).det))⁻¹) := by
    have hAp : A.det ≠ 0 := isUnit_iff_ne_zero.mp hA
    have hSdne : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetPos)
    have hZne : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
    have hAbsne : abs A.det ≠ 0 := abs_ne_zero.mpr hAp
    rw [hAdetc, hSigdet, Real.sqrt_div (le_of_lt hSdetPos), Real.sqrt_sq_eq_abs]
    field_simp [hZne, hSdne, hAbsne]
  simp only [multivariateGaussianPDF, sub_zero]
  rw [quadForm_eq S hSU A hA]
  rw [←
    mul_assoc (1 / Real.sqrt ((A⁻¹ * (A⁻¹)ᵀ).det))
      (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹),
    hKey]

/-- Sub-step 2a of `plan_integral_norm_gaussian_bounded.md` (Step 2): the standard Gaussian
density `(2π)^(-card ι / 2) · exp(-‖x‖²/2)` integrates to `1` over `EuclideanSpace ℝ ι`.
This makes `volume.withDensity` of it a probability measure (needed for
`Measure.ext_of_charFun` in sub-step 2c) and is the `c = 0` case of Mathlib's Gaussian
Fourier integral `GaussianFourier.integral_rexp_neg_mul_sq_norm` with `b = 1/2`. -/
theorem stdGaussianDensity_integral_one {ι : Type*} [Fintype ι] :
    ∫ x : EuclideanSpace ℝ ι,
        (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) =
      1 := by
  have hb : 0 < (1 / 2 : ℝ) := by norm_num
  have hf : ∀ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by
    congr 1; ring
  have h0 :
    ∫ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / 2) ∂volume =
      (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) := by
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
theorem charFun_stdGaussianDensity {ι : Type*} [Fintype ι] (t : EuclideanSpace ℝ ι) :
    charFun
        (volume.withDensity
          (fun x =>
            ENNReal.ofReal
              ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2))))
        t =
      Complex.exp (-‖t‖ ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) ≠ 0 := by positivity
  have hpos :
    ∀ x : EuclideanSpace ℝ ι,
      0 ≤ (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by positivity
  have hpoint :
    ∀ x : EuclideanSpace ℝ ι,
      (ENNReal.ofReal
              ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) *
                Real.exp (-(1 / 2) * ‖x‖ ^ 2))).toReal •
          Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I) =
        (Complex.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2))) *
          (Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2)) *
            Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    intro x
    rw [ENNReal.toReal_ofReal (hpos x), Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  have hint :
    ∀ x : EuclideanSpace ℝ ι,
      Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2)) *
          Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I) =
        Complex.exp
          (-(Complex.ofReal (1 / 2)) * Complex.ofReal ‖x‖ ^ 2 +
            Complex.I * Complex.ofReal (inner ℝ t x)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, real_inner_comm t x, mul_comm (Complex.ofReal (inner ℝ t x)) Complex.I]
  rw [charFun_apply]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  simp only [hpoint, hint]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I t,
    finrank_euclideanSpace, ← Complex.ofReal_div,
    show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring,
    show (((Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)) = Complex.ofReal ((Fintype.card ι : ℝ) / 2) from by
      push_cast; rfl,
    ← Complex.ofReal_cpow h2pi.le ((Fintype.card ι : ℝ) / 2), neg_div,
    Real.rpow_neg h2pi.le ((Fintype.card ι : ℝ) / 2), ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ hne, Complex.ofReal_one, one_mul, Complex.I_sq, neg_one_mul,
    show ((4 : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 2 from by norm_num]

/-- Sub-step 2c of `plan_integral_norm_gaussian_bounded.md` (Step 2): the standard Gaussian
measure `stdGaussian` equals `volume.withDensity` of the standard Gaussian density.
Via `Measure.ext_of_charFun` it suffices to compare characteristic functions, using
`charFun_stdGaussian` (Mathlib) and `charFun_stdGaussianDensity` (sub-step 2b); the
`IsFiniteMeasure` instance on the density side is derived from sub-step 2a
(`isFiniteMeasure_withDensity` needs `∫⁻ x, ENNReal.ofReal f ∂volume ≠ ∞`, which follows
from `∫ x, f x = 1` via `ofReal_integral_eq_lintegral_ofReal`). -/
theorem stdGaussian_eq_withDensity {ι : Type*} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity
        (fun x =>
          ENNReal.ofReal
            ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2))) := by
  have hexp : ∀ x : EuclideanSpace ℝ ι, Real.exp (-(1 / 2) * ‖x‖ ^ 2) = Real.exp (-‖x‖ ^ 2 / 2) :=
    fun x => by
    congr 1; ring
  have hint :
    ∫ x : EuclideanSpace ℝ ι,
        (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) =
      1 := by
    simp only [hexp]
    exact stdGaussianDensity_integral_one
  have hfin :
    Integrable
      (fun x : EuclideanSpace ℝ ι =>
        (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2))
      volume :=
    Integrable.of_integral_ne_zero
      (by
        rw [hint]; norm_num)
  have hlint :
    ∫⁻ x : EuclideanSpace ℝ ι,
        ENNReal.ofReal
          ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) ∂volume =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfin (Eventually.of_forall fun x => by positivity)]
    rw [hint, ENNReal.ofReal_one]
  have hmeas :
    IsFiniteMeasure
      (volume.withDensity
        (fun x : EuclideanSpace ℝ ι =>
          ENNReal.ofReal
            ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)))) :=
    isFiniteMeasure_withDensity
      (by
        rw [hlint]; simp)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_stdGaussianDensity]

/-- Linear change of variables for integrals over `EuclideanSpace ℝ (Fin n)`: for a matrix
`B` with positive determinant, pulling the integrand back along `x ↦ μ + B x` scales the
integral by `B.det` (Step 3 of `plan_integral_norm_gaussian_bounded.md`: the substitution
`x ↦ μ + √Σ x` in the Fourier integral of the Gaussian density). -/
theorem integral_subst {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [OpensMeasurableSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [SecondCountableTopology F] (n : ℕ) (μ : EuclideanSpace ℝ (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) (hBdet : 0 < B.det) (f : EuclideanSpace ℝ (Fin n) → F)
    (hf : AEMeasurable f volume) :
    ∫ x, f x ∂volume =
      (B.det : ℝ) • ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume := by
  have hLdet : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hLne : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) ≠ 0 := by
    rw [hLdet]; exact ne_of_gt hBdet
  have hmapL :
    Measure.map (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) volume =
      ENNReal.ofReal (B.det)⁻¹ • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLdet,
      abs_of_pos (inv_pos.mpr hBdet)]
  have hmeasg :
    Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x := by
    fun_prop
  have hmapg :
    Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume =
      ENNReal.ofReal (B.det)⁻¹ • volume := by
    rw [show
        (fun x : EuclideanSpace ℝ (Fin n) =>
            μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) =
          (μ + ·) ∘ (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B)
        from rfl,
      ←
      Measure.map_map (by fun_prop : Measurable (μ + ·))
        (by fun_prop : Measurable (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B)),
      hmapL, Measure.map_smul _ (by fun_prop), MeasureTheory.map_add_left_eq_self volume μ]
  have hac :
    Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume ≪
      volume := by
    rw [hmapg]; exact Measure.smul_absolutelyContinuous
  have hf' :
    AEStronglyMeasurable f
      (Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume) :=
    (hf.mono_ac hac).aestronglyMeasurable
  have H :
    ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume =
      (B.det)⁻¹ • ∫ x, f x ∂volume := by
    calc
      ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume =
          ∫ y,
            f
              y ∂(Measure.map
              (fun x : EuclideanSpace ℝ (Fin n) =>
                μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
              volume) :=
        (integral_map (hmeasg.aemeasurable) hf').symm
      _ = ∫ y, f y ∂(ENNReal.ofReal (B.det)⁻¹ • volume) := by rw [hmapg]
      _ = (ENNReal.ofReal (B.det)⁻¹).toReal • ∫ y, f y ∂volume := integral_smul_measure _ _
      _ = (B.det)⁻¹ • ∫ y, f y ∂volume := by rw [ENNReal.toReal_ofReal (by positivity)]
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
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdet : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr
      (by
        rw [hBdetEq]; exact ne_of_gt (Real.sqrt_pos.mpr hSdetpos))
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetpos)
  have hBT : Bᵀ = B := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hBher
  have h1eq : (S⁻¹ * B) * B = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [Matrix.mul_assoc, hBB, Matrix.nonsing_inv_mul S hSdet]
  have h1 : B⁻¹ = S⁻¹ * B := Matrix.inv_eq_left_inv h1eq
  intro h
  set h' : Fin n → ℝ := (h : Fin n → ℝ) with hh'
  calc
    (S⁻¹ *ᵥ (B *ᵥ h')) ⬝ᵥ (B *ᵥ h') = ((S⁻¹ * B) *ᵥ h') ⬝ᵥ (B *ᵥ h') := by rw [Matrix.mulVec_mulVec]
    _ = (B⁻¹ *ᵥ h') ⬝ᵥ (B *ᵥ h') := by rw [h1]
    _ = h' ⬝ᵥ (Bᵀ *ᵥ (B⁻¹ *ᵥ h')) := (Matrix.dotProduct_transpose_mulVec B h' (B⁻¹ *ᵥ h')).symm
    _ = h' ⬝ᵥ ((B * B⁻¹) *ᵥ h') := by rw [hBT, Matrix.mulVec_mulVec]
    _ = h' ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ h') := by rw [Matrix.mul_nonsing_inv B hBdet]
    _ = h' ⬝ᵥ h' := by rw [Matrix.one_mulVec]
    _ = ‖h‖ ^ 2 := by
      calc
        h' ⬝ᵥ h' = h' ⬝ᵥ star h' := by rw [show star h' = h' from by simp]
        _ = inner ℝ (WithLp.toLp 2 h') (WithLp.toLp 2 h') :=
          (EuclideanSpace.inner_toLp_toLp h' h').symm
        _ = ‖WithLp.toLp 2 h'‖ ^ 2 := real_inner_self_eq_norm_sq _
        _ = ‖h‖ ^ 2 := rfl

/-- Core: Fourier transform of the standard Gaussian density at general frequency `w`. -/
theorem stdGaussianDensity_ft {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ ι) :
    ∫ x : EuclideanSpace ℝ ι,
        Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) *
          Complex.exp (Complex.ofReal (inner ℝ x w) * Complex.I) =
      ((2 * Real.pi) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) * Complex.exp (-‖w‖ ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hexp : ∀ x : EuclideanSpace ℝ ι, Real.exp (-‖x‖ ^ 2 / 2) = Real.exp (-(1 / 2) * ‖x‖ ^ 2) :=
    fun x => by
    congr 1; ring
  have hint :
    ∀ x : EuclideanSpace ℝ ι,
      Complex.ofReal (Real.exp (-(1 / 2) * ‖x‖ ^ 2)) *
          Complex.exp (Complex.ofReal (inner ℝ x w) * Complex.I) =
        Complex.exp
          (-(Complex.ofReal (1 / 2)) * Complex.ofReal ‖x‖ ^ 2 +
            Complex.I * Complex.ofReal (inner ℝ w x)) := by
    intro x
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, real_inner_comm w x, mul_comm (Complex.ofReal (inner ℝ w x)) Complex.I]
  simp only [hexp, hint]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I w, finrank_euclideanSpace, ←
    Complex.ofReal_div, show (Real.pi / (1 / 2 : ℝ)) = 2 * Real.pi from by ring,
    show (((Fintype.card ι : ℕ) : ℂ) / (2 : ℂ)) = Complex.ofReal ((Fintype.card ι : ℝ) / 2) from by
      push_cast; rfl,
    ← Complex.ofReal_cpow h2pi.le ((Fintype.card ι : ℝ) / 2), Complex.I_sq, neg_one_mul,
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
    charFun
        (volume.withDensity
          (fun x => ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x)))
        t =
      Complex.exp
        (Complex.ofReal (inner ℝ t μ) * Complex.I -
          Complex.ofReal ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)) / 2) := by
  -- CFC bundle
  have hSdetpos : 0 < S.det := hS.det_pos
  have hS0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdetpos : 0 < B.det := by
    rw [hBdetEq]; exact Real.sqrt_pos.mpr hSdetpos
  have hBdet : IsUnit B.det := isUnit_iff_ne_zero.mpr (ne_of_gt hBdetpos)
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetpos)
  have hBT : Bᵀ = B := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hBher
  have hquad' :
    ∀ h : EuclideanSpace ℝ (Fin n),
      (S⁻¹ *ᵥ (B *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (B *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2 := by
    intro h; rw [← hBdef] at *; exact quadForm_sqrt_eq_norm_sq n S hS h
  -- bridges
  have hcoep :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x : EuclideanSpace ℝ (Fin n)) :
            Fin n → ℝ) -
          (μ : Fin n → ℝ) =
        B *ᵥ (x : Fin n → ℝ) := by
    intro x
    rw [WithLp.ofLp_add, add_sub_cancel_left]
    rfl
  have hinner :
    ∀ (x y : EuclideanSpace ℝ (Fin n)),
      inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B y) = x ⬝ᵥ B *ᵥ (y : Fin n → ℝ) :=
    fun x y => Matrix.inner_toEuclideanCLM B x y
  have hcoLt :
    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t : Fin n → ℝ) = B *ᵥ (t : Fin n → ℝ) := rfl
  have hbridge :
    ∀ x : EuclideanSpace ℝ (Fin n),
      inner ℝ (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x) t =
        inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t) := by
    intro x
    rw [real_inner_comm, hinner t x, ← Matrix.dotProduct_transpose_mulVec, hBT, ← hinner]
  -- PDF facts
  have hpdf :
    ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x =
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
          Real.exp
            (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                  ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                2)) :=
    fun _ => rfl
  have hP' : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hP'0 : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have hSqrt0 : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetpos)
  have hpos :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x := by
    intro x
    rw [hpdf x]
    exact
      mul_nonneg
        (inv_nonneg.mpr (mul_nonneg (le_of_lt hP') (le_of_lt (Real.sqrt_pos.mpr hSdetpos))))
        (le_of_lt (Real.exp_pos _))
  have hpoint :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x)).toReal •
          Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I) =
        Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
          (Complex.ofReal
              (Real.exp
                (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                      ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                    2))) *
            Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    intro x
    rw [ENNReal.toReal_ofReal (hpos x), hpdf x, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  have hmeasP :
    AEMeasurable (fun x => ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x))
      volume := by
    have hinner_meas :
      Measurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
            Real.exp
              (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                    ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                  2))) := by
      fun_prop
    have hRHS :
      AEMeasurable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
              Real.exp
                (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                      ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                    2))))
        volume :=
      (ENNReal.measurable_ofReal.comp hinner_meas).aemeasurable
    exact hRHS.congr (Filter.Eventually.of_forall (fun x => by simp only [hpdf]))
  have htop :
    ∀ᵐ x ∂volume, ENNReal.ofReal (multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x) < ∞ := by simp
  -- norm bridge and scalar identities
  have hnorm2 :
    ‖Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t‖ ^ 2 =
      (t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ) := by
    rw [← real_inner_self_eq_norm_sq, hinner (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t) t,
      hcoLt, ← Matrix.dotProduct_transpose_mulVec, hBT, Matrix.mulVec_mulVec, hBB]
  have hscal :
    B.det * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (2 * Real.pi) ^ ((n : ℝ) / 2)) =
      1 := by
    rw [hBdetEq,
      mul_comm (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      ← mul_assoc, mul_comm (Real.sqrt S.det) ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      mul_inv_cancel₀ (mul_ne_zero hP'0 hSqrt0)]
  have hscalC :
    Complex.ofReal B.det *
        (Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
          Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2))) =
      1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hscal, Complex.ofReal_one]
  have hfin :
    Complex.exp (Complex.ofReal (inner ℝ t μ) * Complex.I) *
        Complex.exp (Complex.ofReal (-((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2) =
      Complex.exp
        (Complex.ofReal (inner ℝ t μ) * Complex.I -
          Complex.ofReal ((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ)) / 2) := by
    rw [Complex.ofReal_neg, neg_div, ← Complex.exp_add, sub_eq_add_neg]
  -- pointwise splitting after substitution
  have hsplit :
    ∀ x : EuclideanSpace ℝ (Fin n),
      Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
          (Complex.ofReal
              (Real.exp
                (-(((S⁻¹ *ᵥ
                        (((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x :
                              EuclideanSpace ℝ (Fin n)) :
                            Fin n → ℝ) -
                          (μ : Fin n → ℝ))) ⬝ᵥ
                      (((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x :
                            EuclideanSpace ℝ (Fin n)) :
                          Fin n → ℝ) -
                        (μ : Fin n → ℝ))) /
                    2))) *
            Complex.exp
              (Complex.ofReal (inner ℝ (μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x) t) *
                Complex.I)) =
        (Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
            Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I)) *
          (Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) *
            Complex.exp
              (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t)) *
                Complex.I)) := by
    intro x
    rw [hcoep x, hquad' x, ← neg_div, inner_add_left, Complex.ofReal_add, add_mul, hbridge x,
      Complex.exp_add]
    ring
  -- rearrangement and exponent normalization for the endgame
  have hrearr :
    Complex.ofReal B.det *
        ((Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
            Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I)) *
          (Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2)) *
            Complex.exp (Complex.ofReal (-((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2))) =
      (Complex.ofReal B.det *
          (Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
            Complex.ofReal ((2 * Real.pi) ^ ((n : ℝ) / 2)))) *
        (Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I) *
          Complex.exp (Complex.ofReal (-((t : Fin n → ℝ) ⬝ᵥ S *ᵥ (t : Fin n → ℝ))) / 2)) := by
    ring
  -- substitution
  have hsub :=
    integral_subst n μ B hBdetpos
      (fun x =>
        Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
          (Complex.ofReal
              (Real.exp
                (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                      ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                    2))) *
            Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)))
      (by fun_prop)
  -- substitution + pointwise splitting + const extraction, in one step (defeq-chained,
  -- no brittle `rw` matching of the substituted integrand)
  have hstep2 :
    ∫ x : EuclideanSpace ℝ (Fin n),
        Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
          (Complex.ofReal
              (Real.exp
                (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                      ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                    2))) *
            Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) ∂volume =
      (B.det : ℝ) •
        ((Complex.ofReal (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) *
            Complex.exp (Complex.ofReal (inner ℝ μ t) * Complex.I)) *
          ∫ x : EuclideanSpace ℝ (Fin n),
            Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) *
              Complex.exp
                (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t)) *
                  Complex.I) ∂volume) := by
    refine
      Eq.trans hsub
        (congrArg ((B.det : ℝ) • ·)
          (Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (fun y => hsplit y)))
            (integral_const_mul _
              (fun x : EuclideanSpace ℝ (Fin n) =>
                Complex.ofReal (Real.exp (-‖x‖ ^ 2 / 2)) *
                  Complex.exp
                    (Complex.ofReal (inner ℝ x (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B t)) *
                      Complex.I)))))
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
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x ∂volume =
      1 := by
  -- CFC bundle (same as in `multivariateGaussian_eq_withDensity`)
  have hSdetpos : 0 < S.det := hS.det_pos
  have hS0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt S with hBdef
  have hBB : B * B = S := CFC.sqrt_mul_sqrt_self S hS0
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact CFC.sqrt_nonneg S
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBdetSq : B.det ^ 2 = S.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdetNN : 0 ≤ B.det := (Matrix.nonneg_iff_posSemidef.mp hBnn).det_nonneg
  have hBdetEq : B.det = Real.sqrt S.det :=
    ((Real.sqrt_eq_iff_eq_sq (le_of_lt hSdetpos) hBdetNN).mpr hBdetSq.symm).symm
  have hBdetpos : 0 < B.det := by
    rw [hBdetEq]; exact Real.sqrt_pos.mpr hSdetpos
  have hquad' :
    ∀ h : EuclideanSpace ℝ (Fin n),
      (S⁻¹ *ᵥ (B *ᵥ (h : Fin n → ℝ))) ⬝ᵥ (B *ᵥ (h : Fin n → ℝ)) = ‖h‖ ^ 2 := by
    intro h; rw [← hBdef] at *; exact quadForm_sqrt_eq_norm_sq n S hS h
  have hcoep :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ((μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B x : EuclideanSpace ℝ (Fin n)) :
            Fin n → ℝ) -
          (μ : Fin n → ℝ) =
        B *ᵥ (x : Fin n → ℝ) := by
    intro x
    rw [WithLp.ofLp_add, add_sub_cancel_left]
    rfl
  -- PDF facts
  have hpdf :
    ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x =
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
          Real.exp
            (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                  ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                2)) :=
    fun _ => rfl
  have hP'0 : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have hSqrt0 : Real.sqrt S.det ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hSdetpos)
  have hmeasRHS :
    Measurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
          Real.exp
            (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) ⬝ᵥ
                  ((x : Fin n → ℝ) - (μ : Fin n → ℝ))) /
                2))) := by
    fun_prop
  have hf :
    AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x)
      volume :=
    hmeasRHS.aemeasurable.congr (Filter.Eventually.of_forall (fun x => by simp only [hpdf]))
  -- shifted PDF reduces to the standard Gaussian density
  have hshift :
    ∀ y : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (μ : Fin n → ℝ) S hS
          (μ + Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B y) =
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * Real.exp (-‖y‖ ^ 2 / 2) := by
    intro y
    rw [hpdf, hcoep y, hquad' y, ← neg_div]
  -- substitution + pointwise shift + constant extraction, in one step (defeq-chained,
  -- no brittle `rw` matching of the substituted integrand)
  have hsub :=
    integral_subst n μ B hBdetpos (fun x => multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x) hf
  have hstep :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (μ : Fin n → ℝ) S hS x ∂volume =
      (B.det : ℝ) •
        (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
          ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / 2) ∂volume) := by
    refine
      Eq.trans hsub
        (congrArg ((B.det : ℝ) • ·)
          (Eq.trans (integral_congr_ae (Filter.Eventually.of_forall (fun y => hshift y)))
            (integral_const_mul _ (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / 2)))))
  -- extract the standard Gaussian integral
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hPne : (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by positivity
  have h0 := stdGaussianDensity_integral_one (ι := Fin n)
  simp only [Fintype.card_fin] at h0
  rw [integral_const_mul] at h0
  rw [show (-(↑n : ℝ)) / 2 = -((↑n : ℝ) / 2) from by ring] at h0
  rw [Real.rpow_neg h2pi.le ((n : ℝ) / 2)] at h0
  have h1 :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / 2) ∂volume =
      (2 * Real.pi) ^ ((n : ℝ) / 2) := by
    have h3 := congrArg (fun t : ℝ => (2 * Real.pi) ^ ((n : ℝ) / 2) * t) h0
    rw [← mul_assoc, mul_inv_cancel₀ hPne, one_mul, mul_one] at h3
    exact h3
  have hscal :
    B.det * (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (2 * Real.pi) ^ ((n : ℝ) / 2)) =
      1 := by
    rw [hBdetEq,
      mul_comm (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹)
        ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      ← mul_assoc, mul_comm (Real.sqrt S.det) ((2 * Real.pi) ^ ((n : ℝ) / 2)),
      mul_inv_cancel₀ (mul_ne_zero hP'0 hSqrt0)]
  rw [hstep, smul_eq_mul, h1]
  rw [hscal]

/-- Step 5 of `plan_integral_norm_gaussian_bounded.md`: `volume.withDensity` of
`ENNReal.ofReal ∘ (multivariateGaussianPDF …)` is a finite measure (feeds
`Measure.ext_of_charFun`; the `∫⁻ … ≠ ∞` side condition follows from the integral being `1`,
via `ofReal_integral_eq_lintegral_ofReal`). -/
theorem isFiniteMeasure_gaussianPDF_withDensity (n : ℕ) (mean : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) :
    IsFiniteMeasure
      (volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (multivariateGaussianPDF n mean S hS x))) := by
  have hpdf :
    ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n (WithLp.toLp 2 mean : EuclideanSpace ℝ (Fin n)) S hS x =
        multivariateGaussianPDF n mean S hS x :=
    fun _ => rfl
  have hint :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n mean S hS x ∂volume = 1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 mean) S hS
    exact (integral_congr_ae (Filter.Eventually.of_forall (fun x => (hpdf x).symm))).trans h1
  have hSdetpos : 0 < S.det := hS.det_pos
  have hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ multivariateGaussianPDF n mean S hS x := by
    intro x
    rw [show
        multivariateGaussianPDF n mean S hS x =
          ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
            Real.exp (-(((S⁻¹ *ᵥ ((x : Fin n → ℝ) - mean)) ⬝ᵥ ((x : Fin n → ℝ) - mean)) / 2))
        from rfl]
    exact
      mul_nonneg
        (inv_nonneg.mpr
          (mul_nonneg (le_of_lt (by positivity)) (le_of_lt (Real.sqrt_pos.mpr hSdetpos))))
        (le_of_lt (Real.exp_pos _))
  have hfin :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n mean S hS x) volume :=
    Integrable.of_integral_ne_zero
      (by
        rw [hint]; norm_num)
  have hlint :
    ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n mean S hS x) ∂volume =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfin (Eventually.of_forall fun x => hpos x)]
    rw [hint, ENNReal.ofReal_one]
  exact
    isFiniteMeasure_withDensity
      (by
        rw [hlint]; simp)

/-- Pointwise unfolding of `multivariateGaussianPDF` for a general mean and covariance. -/
theorem multivariateGaussianPDF_eq (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    multivariateGaussianPDF n m Cov hC x =
      ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt Cov.det)⁻¹ *
        Real.exp (-(((Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m)) / 2)) :=
  rfl

/-- Measurability of the multivariate Gaussian PDF. -/
theorem measurable_multivariateGaussianPDF (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n m Cov hC x) := by
  simp only [multivariateGaussianPDF_eq n m Cov hC]
  fun_prop

theorem integral_normalized_gaussian_bounded (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun (h : EuclideanSpace ℝ (Fin n)) =>
        ‖h‖ *
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
            (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) *
          (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)))
      volume := by
  have hSig : (A⁻¹ * S * A⁻¹ᵀ).PosDef := sigmaTilde_posDef n S hS A hA
  -- PDF with mean `A⁻¹ y` and covariance `Σ̃ = A⁻¹ S A⁻ᵀ` (mean in plain form, matching
  -- `density_id`'s RHS verbatim)
  have hP' : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSigdetpos : 0 < (A⁻¹ * S * A⁻¹ᵀ).det := hSig.det_pos
  have hposT :
    ∀ x : EuclideanSpace ℝ (Fin n),
      0 ≤ multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x := by
    intro x
    rw [multivariateGaussianPDF_eq n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x]
    exact
      mul_nonneg
        (inv_nonneg.mpr (mul_nonneg (le_of_lt hP') (le_of_lt (Real.sqrt_pos.mpr hSigdetpos))))
        (le_of_lt (Real.exp_pos _))
  have hmeasPT :
    AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal
          (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x))
      volume :=
    (ENNReal.measurable_ofReal.comp
        (measurable_multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ)
          hSig)).aemeasurable
  have htopT :
    ∀ᵐ x ∂volume,
      ENNReal.ofReal
          (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x) <
        ∞ := by
    simp
  -- the cast mean (as produced by instantiating the EuclideanSpace-typed lemmas) agrees
  -- pointwise with the plain `(A⁻¹).mulVec y` mean
  have hcast :
    ∀ x : EuclideanSpace ℝ (Fin n),
      multivariateGaussianPDF n
          ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
          (A⁻¹ * S * A⁻¹ᵀ) hSig x =
        multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x :=
    fun _ => rfl
  -- the density measure is finite (feeds `Measure.ext_of_charFun`)
  have hfin :
    IsFiniteMeasure
      (volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (multivariateGaussianPDF n
              ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
                Fin n → ℝ)
              (A⁻¹ * S * A⁻¹ᵀ) hSig x))) :=
    isFiniteMeasure_gaussianPDF_withDensity n
      ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)
      (A⁻¹ * S * A⁻¹ᵀ) hSig
  -- the density measure is the multivariate Gaussian measure
  have hEqL :
    volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (multivariateGaussianPDF n
              ((WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) :
                Fin n → ℝ)
              (A⁻¹ * S * A⁻¹ᵀ) hSig x)) =
      volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x)) :=
    congrArg volume.withDensity (funext fun x => congrArg ENNReal.ofReal (hcast x))
  have hEq :
    volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x)) =
      multivariateGaussian (WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * A⁻¹ᵀ) := by
    refine hEqL.symm.trans ?_
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [multivariateGaussian_eq_withDensity n (WithLp.toLp 2 ((A⁻¹).mulVec (y : Fin n → ℝ)))
        (A⁻¹ * S * A⁻¹ᵀ) hSig t,
      charFun_multivariateGaussian hSig.posSemidef t]
  -- withDensity bridge: identity is integrable w.r.t. the density measure
  have hwithD :
    MeasureTheory.Integrable id
      (volume.withDensity
        (fun x : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal
            (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig
              x))) := by
    rw [hEq]
    exact ProbabilityTheory.IsGaussian.integrable_id
  have hbridge := (integrable_withDensity_iff_integrable_smul₀' hmeasPT htopT).mp hwithD
  have hnormed := hbridge.norm
  -- pointwise: ‖toReal ofReal pdf • x‖ = ‖x‖ * pdf
  have hpt :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(ENNReal.ofReal
                (multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig
                  x)).toReal •
            id x‖ =
        ‖x‖ * multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig x := by
    intro x
    rw [norm_smul, ENNReal.toReal_ofReal (hposT x), Real.norm_eq_abs, abs_of_nonneg (hposT x),
      show ‖id x‖ = ‖x‖ from rfl, mul_comm]
  have hkey := hnormed.congr (Filter.Eventually.of_forall hpt)
  -- bridge to the goal integrand via `density_id`
  have hcongr1 :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ‖h‖ *
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
            (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) *
          (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)) =
        ‖h‖ * multivariateGaussianPDF n ((A⁻¹).mulVec (y : Fin n → ℝ)) (A⁻¹ * S * A⁻¹ᵀ) hSig h := by
    intro h
    rw [mul_assoc,
      mul_comm
        (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))))
        (1 / Real.sqrt ((A⁻¹ * A⁻¹ᵀ).det)),
      ← density_id n S hS A hA y hSig h]
  exact hkey.congr (Filter.Eventually.of_forall (fun h => (hcongr1 h).symm))

theorem integral_gaussian_bounded (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun (h : EuclideanSpace ℝ (Fin n)) =>
        ‖h‖ *
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
            (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))))
      volume := by
  have hAdet2 : ((A⁻¹ * A⁻¹ᵀ).det) = ((A⁻¹).det) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← pow_two ((A⁻¹).det)]
  have hAdetinv : (A⁻¹).det = (A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv]; norm_num
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

/-- Pointwise identity of `noiseDens` with the Gaussian pdf evaluated at the linear-map form
`y + (-A) h` (the shape required by `integral_subst_unit`). -/
theorem noiseDens_eq (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n)) :
    noiseDens n S hS A y h =
      multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
        (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
  simp only [noiseDens]
  rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))),
    multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
      (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h)]
  have hco :
    ((WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) : Fin n → ℝ) =
      ((y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) : Fin n → ℝ) := by
    rw [WithLp.ofLp_toLp]
    show
      (y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ) =
        (y : Fin n → ℝ) + ((-1 : ℝ) • A) *ᵥ (h : Fin n → ℝ)
    rw [Matrix.smul_mulVec, neg_one_smul, sub_eq_add_neg]
  rw [hco, WithLp.ofLp_add]

/-- Generalized linear change of variables over `EuclideanSpace ℝ (Fin n)`: `integral_subst`
of Step 3 with `0 < B.det` weakened to `IsUnit B.det`; the scaling factor is the absolute
value of the inverse Jacobian determinant. -/
theorem integral_subst_unit (n : ℕ) (μ : EuclideanSpace ℝ (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : IsUnit B.det) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AEMeasurable f volume) :
    ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume =
      (|(B.det : ℝ)⁻¹|) • ∫ x, f x ∂volume := by
  have hLdet : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have hLne : LinearMap.det (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) ≠ 0 := by
    rw [hLdet]; exact isUnit_iff_ne_zero.mp hB
  have hmapL :
    Measure.map (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) volume =
      ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hLne, hLdet]
  have hmeasg :
    Measurable fun x : EuclideanSpace ℝ (Fin n) =>
      μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x := by
    fun_prop
  have hmapg :
    Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume =
      ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume := by
    rw [show
        (fun x : EuclideanSpace ℝ (Fin n) =>
            μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) =
          (μ + ·) ∘ (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B)
        from rfl,
      ←
      Measure.map_map (by fun_prop : Measurable (μ + ·))
        (by fun_prop : Measurable (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B)),
      hmapL, Measure.map_smul _ (by fun_prop), MeasureTheory.map_add_left_eq_self volume μ]
  have hac :
    Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume ≪
      volume := by
    rw [hmapg]; exact Measure.smul_absolutelyContinuous
  have hf' :
    AEStronglyMeasurable f
      (Measure.map
        (fun x : EuclideanSpace ℝ (Fin n) => μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
        volume) :=
    (hf.mono_ac hac).aestronglyMeasurable
  have H :
    ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume =
      (|(B.det : ℝ)⁻¹|) • ∫ x, f x ∂volume := by
    calc
      ∫ x, f (μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume =
          ∫ y,
            f
              y ∂(Measure.map
              (fun x : EuclideanSpace ℝ (Fin n) =>
                μ + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x)
              volume) :=
        (integral_map hmeasg.aemeasurable hf').symm
      _ = ∫ y, f y ∂(ENNReal.ofReal (|(B.det : ℝ)⁻¹|) • volume) := by rw [hmapg]
      _ = (ENNReal.ofReal (|(B.det : ℝ)⁻¹|)).toReal • ∫ y, f y ∂volume := integral_smul_measure _ _
      _ = (|(B.det : ℝ)⁻¹|) • ∫ y, f y ∂volume := by rw [ENNReal.toReal_ofReal (by positivity)]
  rw [H, abs_inv]

/-- Mass of the pulled-back noise density: `∫ f_n(y - A h) dh = |det A|⁻¹` — the appendix's
change of variables `s = y - A h` in `∫ f_n(s) ds = 1`. -/
theorem integral_noise_pullback (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n)) :
    ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume = (|A.det| : ℝ)⁻¹ := by
  set B : Matrix (Fin n) (Fin n) ℝ := (-1 : ℝ) • A with hBdef
  have hBdet : B.det = (-1 : ℝ) ^ n * A.det := by rw [hBdef, Matrix.det_smul, Fintype.card_fin]
  have hBunit : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr
      (by
        rw [hBdet]
        exact mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)) (isUnit_iff_ne_zero.mp hA))
  have hBabs : |B.det| = |A.det| := by
    rw [hBdet, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hmeas :
    AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x)
      volume :=
    (measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).aemeasurable
  have hint :=
    integral_subst_unit n y B hBunit (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x)
      hmeas
  have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
  calc
    ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume =
        ∫ x,
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
            (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) B) x) ∂volume :=
      by rw [integral_congr_ae (Filter.Eventually.of_forall (fun h => noiseDens_eq n S hS A y h))]
    _ = (|(B.det : ℝ)⁻¹|) • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume := hint
    _ = (|B.det| : ℝ)⁻¹ • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume := by
      rw [abs_inv]
    _ = (|A.det| : ℝ)⁻¹ := by
      rw [hBabs]
      have h2 :
        (|A.det| : ℝ)⁻¹ • ∫ x, multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume =
          (|A.det| : ℝ)⁻¹ • 1 :=
        congrArg _ h1
      rw [h2, smul_eq_mul, mul_one]

/-- The multivariate Gaussian pdf is bounded above by its normalizing constant: the quadratic
form `uᵀ Σ⁻¹ u` in the exponent is nonnegative, so the exponential factor is at most `1`. -/
theorem multivariateGaussianPDF_le_const (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) :
    multivariateGaussianPDF n m Cov hC x ≤
      ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt Cov.det)⁻¹ := by
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
    have h1 : Cov⁻¹ᵀ = Cov⁻¹ := by rw [← transpose_nonsing_inv Cov hCdet, hCH]
    exact
      Matrix.ext
        (fun i j => by simpa using (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) h1).symm)
  have hCinvPSD : Cov⁻¹.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hCinvH
      (fun u => by
        have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hC.posSemidef (Cov⁻¹ *ᵥ u)
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Cov hCdet, Matrix.one_mulVec] at h
        simpa [dotProduct_comm] using h)
  have hquad : ∀ u : Fin n → ℝ, 0 ≤ (Cov⁻¹ *ᵥ u) ⬝ᵥ u := by
    intro u
    have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hCinvPSD u
    rwa [dotProduct_comm] at h
  have hquadx : 0 ≤ (Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m) :=
    hquad ((x : Fin n → ℝ) - m)
  have hexp :
    Real.exp (-(((Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m)) / 2)) ≤ 1 := by
    have hnn : (0 : ℝ) ≤ (Cov⁻¹ *ᵥ ((x : Fin n → ℝ) - m)) ⬝ᵥ ((x : Fin n → ℝ) - m) / 2 :=
      div_nonneg hquadx (by norm_num)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hbound := mul_le_mul_of_nonneg_left hexp hc₀.le
  rwa [mul_one] at hbound

/-- Uniform convergence transfer (appendix_1.tex, first part of the proof of the main result):
if `f_h^{(K)} → f_h` uniformly then `f_y^{(K)} → f_y` uniformly, where
`f_y(y) = ∫ f_n(y - A h) f(h) dh`. Only integrability of the densities is assumed; the
pdf property is not needed for this step. -/
theorem uniform_convergence_fy (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfh : MeasureTheory.Integrable fh volume) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhK : ∀ K, MeasureTheory.Integrable (fhK K) volume)
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ,
      ∀ K ≥ K₀,
        ∀ y : EuclideanSpace ℝ (Fin n), |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| < ε := by
  have hAbs : 0 < |A.det| := abs_pos.mpr (isUnit_iff_ne_zero.mp hA)
  have hne : |A.det| ≠ 0 := ne_of_gt hAbs
  obtain ⟨K₁, hK₁⟩ := hconv (ε * |A.det| / 2) (div_pos (mul_pos hε hAbs) two_pos)
  refine ⟨K₁, fun K hK y => ?_⟩
  simp only [fyPDF]
  -- measurability and mass of the pulled-back noise density
  have haM : AEStronglyMeasurable (noiseDens n S hS A y) volume := by
    have hcomp :
      noiseDens n S hS A y =
        (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
          (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
      funext h
      exact noiseDens_eq n S hS A y h
    rw [hcomp]
    exact
      ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
          (by fun_prop :
            Measurable
              (fun h : EuclideanSpace ℝ (Fin n) =>
                y +
                  (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A))
                    h))).aestronglyMeasurable
  have haint : MeasureTheory.Integrable (noiseDens n S hS A y) volume :=
    Integrable.of_integral_ne_zero
      (by
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
  have hc₀ : ∀ h, noiseDens n S hS A y h ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ := by
    intro h
    simp only [noiseDens]
    exact
      multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
  -- the products are integrable by domination against `c₀ * |f|`
  have hmeas1 : AEStronglyMeasurable (fun h => noiseDens n S hS A y h * fh h) volume :=
    haM.mul hfh.aestronglyMeasurable
  have hmeas2 : AEStronglyMeasurable (fun h => noiseDens n S hS A y h * fhK K h) volume :=
    haM.mul (hfhK K).aestronglyMeasurable
  have hprod1 : MeasureTheory.Integrable (fun h => noiseDens n S hS A y h * fh h) volume := by
    have hg1 :
      MeasureTheory.Integrable
        (fun h => ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * |fh h|) volume :=
      (Integrable.smul (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) hfh.abs).congr
        (Filter.Eventually.of_forall fun h => by simp)
    refine Integrable.mono' hg1 hmeas1 (Filter.Eventually.of_forall (fun h => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hposa h)]
    exact mul_le_mul_of_nonneg_right (hc₀ h) (abs_nonneg _)
  have hprod2 : MeasureTheory.Integrable (fun h => noiseDens n S hS A y h * fhK K h) volume := by
    have hg2 :
      MeasureTheory.Integrable
        (fun h => ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ * |fhK K h|) volume :=
      (Integrable.smul (((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹) (hfhK K).abs).congr
        (Filter.Eventually.of_forall fun h => by simp)
    refine Integrable.mono' hg2 hmeas2 (Filter.Eventually.of_forall (fun h => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hposa h)]
    exact mul_le_mul_of_nonneg_right (hc₀ h) (abs_nonneg _)
  have hdif :
    MeasureTheory.Integrable (fun h => noiseDens n S hS A y h * (fh h - fhK K h)) volume := by
    have hEq :
      (fun h => noiseDens n S hS A y h * (fh h - fhK K h)) =
        (fun h => noiseDens n S hS A y h * fh h) - (fun h => noiseDens n S hS A y h * fhK K h) := by
      funext h
      simp only [Pi.sub_apply]
      ring
    rw [hEq]
    exact hprod1.sub hprod2
  -- the quantitative chain
  rw [← integral_sub hprod1 hprod2]
  rw [integral_congr_ae
      (Filter.Eventually.of_forall
        (fun h =>
          show
            noiseDens n S hS A y h * fh h - noiseDens n S hS A y h * fhK K h =
              noiseDens n S hS A y h * (fh h - fhK K h)
            from by ring))]
  calc
    |∫ h, noiseDens n S hS A y h * (fh h - fhK K h) ∂volume| ≤
        ∫ h, |noiseDens n S hS A y h * (fh h - fhK K h)| ∂volume :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ h, (ε * |A.det| / 2) * noiseDens n S hS A y h ∂volume := by
      refine integral_mono_ae hdif.abs ?_ (Filter.Eventually.of_forall (fun h => ?_))
      · exact Integrable.smul (ε * |A.det| / 2) haint
      · show
          |noiseDens n S hS A y h * (fh h - fhK K h)| ≤ (ε * |A.det| / 2) * noiseDens n S hS A y h
        rw [abs_mul, abs_of_nonneg (hposa h), mul_comm (ε * |A.det| / 2) (noiseDens n S hS A y h)]
        exact mul_le_mul_of_nonneg_left (le_of_lt (hK₁ K hK h)) (hposa h)
    _ = (ε * |A.det| / 2) * ∫ h, noiseDens n S hS A y h ∂volume := integral_const_mul _ _
    _ = (ε * |A.det| / 2) * (|A.det| : ℝ)⁻¹ := by rw [integral_noise_pullback n S hS A hA y]
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-! ## Pdf-side setup for the uniform convergence theorem (appendix_1.tex)

The uniformly convergent approximating sequence `f_h^{(K)}` is *assumed*, not constructed
(Gaussian mixture models are the motivating example, but play no role here). All that is
needed of `f_h` and every `f_h^{(K)}` for the convergence transfer is that they are pdfs
(nonnegative with total mass 1); continuity and vanishing at infinity are recorded as separate
hypotheses on `f_h` to match the setting of `appendix_1.tex`. -/

/-- A pdf is integrable: in Mathlib's definition of the Lebesgue integral, a function with
nonzero integral is automatically integrable (non-integrable functions have integral `0`). -/
theorem integrable_of_isPdf {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsPdf f) :
    MeasureTheory.Integrable f volume :=
  Integrable.of_integral_ne_zero
    (by
      rw [hf.2]; norm_num)

/-- Uniform convergence of the observation densities for a uniformly convergent sequence of
pdfs (`appendix_1.tex`, first part of the proof of the main result): if `f_h` is a continuous
pdf vanishing at infinity and `f_h^{(K)}` is a sequence of pdfs converging uniformly to `f_h`
(an assumption motivated by, but independent of, Theorem 5(a) of
Nguyen–Nguyen–Chamroukhi–McLachlan 2020), then the induced observation densities
`f_y^{(K)} → f_y` uniformly, where `f_y(y) = ∫ f_n(y - A h) f_h(h) dh`.

Continuity and vanishing at infinity are not needed for the convergence transfer; they are
recorded to match the setting of `appendix_1.tex` (`f_h ∈ C₀`). -/
theorem uniform_convergence_fy_pdf (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (_hfhcont : Continuous fh) (_hfh0 : VanishesAtInfinity fh)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfhKpdf : ∀ K, IsPdf (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ,
      ∀ K ≥ K₀,
        ∀ y : EuclideanSpace ℝ (Fin n), |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| < ε :=
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
theorem charFun_map_fy (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun
        (Measure.map
          (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2)
          ((volume.withDensity (fun h => ENNReal.ofReal (f h))).prod
            (volume.withDensity
              (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))))
        t =
      (∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            f h ∂volume) *
        charFun
          (volume.withDensity
            (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))
          t := by
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  -- finiteness of the two density measures
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall fun x => hposf x), hf.2,
      ENNReal.ofReal_one]
  set μh : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h)) with hμhdef
  set μn : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)) with
    hμndef
  have hμhfin : MeasureTheory.IsFiniteMeasure μh :=
    isFiniteMeasure_withDensity
      (by
        rw [hlintf]; simp)
  have hμnfin : MeasureTheory.IsFiniteMeasure μn :=
    isFiniteMeasure_gaussianPDF_withDensity n (0 : Fin n → ℝ) S hS
  -- measurability of the joint map and of the complex exponential
  have hFmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) := by
    fun_prop
  have hexpmeas :
    Measurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    fun_prop
  -- the exponential splits over the two summands of `A p.1 + p.2`
  have hsplit :
    ∀ (a y : EuclideanSpace ℝ (Fin n)),
      Complex.exp
          (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (a : Fin n → ℝ)) + y) t) * Complex.I) =
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (a : Fin n → ℝ))) t) * Complex.I) *
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) := by
    intro a y
    rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
  -- the integrand is bounded by 1, hence integrable on the product measure
  have hint1 :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Complex.exp
          (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) *
            Complex.I))
      (μh.prod μn) := by
    have h1 :
      MeasureTheory.Integrable
        (fun _ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (μh.prod μn) :=
      integrable_const (1 : ℝ)
    refine
      h1.mono' (hexpmeas.comp hFmeas).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    rw [hsplit p.1 p.2, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  -- the same integrand in split form (a.e.-equal, hence integrable)
  have hint1' :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) * Complex.I) *
          Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I))
      (μh.prod μn) :=
    hint1.congr (Filter.Eventually.of_forall fun p => hsplit p.1 p.2)
  -- split the exponential inside the pair integral (before Fubini, to keep the
  -- subsequent rewrites away from beta-redexes)
  have hpre :
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Complex.exp
          (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) *
            Complex.I) ∂(μh.prod μn) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) * Complex.I) *
          Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I) ∂(μh.prod μn) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p => hsplit p.1 p.2)
  -- the inner `y`-integral is against the withDensity of `f` ...
  have hcongr :
    ∫ h : EuclideanSpace ℝ (Fin n),
        (ENNReal.ofReal (f h)).toReal •
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
              Complex.I) ∂volume =
      ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          f h ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show
      (ENNReal.ofReal (f h)).toReal •
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) =
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          f h
    rw [ENNReal.toReal_ofReal (hposf h), Complex.real_smul, mul_comm]
  -- inner `y`-integral: factor off the constant and recognize the noise characteristic
  -- function (as a pointwise statement so that `h` is a free variable during the rewrite)
  have hinner :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn =
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          charFun μn t := by
    intro h
    rw [integral_const_mul _ (fun y => Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I)), ←
      charFun_apply]
  have houter :
    ∫ h : EuclideanSpace ℝ (Fin n),
        ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn ∂μh =
      ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          charFun μn t ∂μh :=
    integral_congr_ae (Filter.Eventually.of_forall hinner)
  have houter2 :
    ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          charFun μn t ∂μh =
      (∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
              Complex.I) ∂μh) *
        charFun μn t :=
    integral_mul_const (charFun μn t)
      (fun (h : EuclideanSpace ℝ (Fin n)) =>
        Complex.exp
          (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
  have hmeasφ : AEMeasurable (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfint.aemeasurable
  have hdens :
    ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp
          (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) ∂μh =
      ∫ h : EuclideanSpace ℝ (Fin n),
        Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
          f h ∂volume := by
    rw [hμhdef,
      integral_withDensity_eq_integral_toReal_smul₀ hmeasφ (by simp)
        (fun h =>
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))]
    exact hcongr
  calc
    charFun
          (Measure.map
            (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2)
            (μh.prod μn))
          t =
        ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2) t) *
              Complex.I) ∂(μh.prod μn) :=
      by rw [charFun_apply, integral_map hFmeas.aemeasurable hexpmeas.aestronglyMeasurable]
    _ =
        ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ))) t) *
                Complex.I) *
            Complex.exp (Complex.ofReal (inner ℝ p.2 t) * Complex.I) ∂(μh.prod μn) :=
      hpre
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          ∫ y : EuclideanSpace ℝ (Fin n),
            Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                  Complex.I) *
              Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂μn ∂μh :=
      by rw [integral_prod _ hint1']
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            charFun μn t ∂μh :=
      houter
    _ =
        (∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                Complex.I) ∂μh) *
          charFun μn t :=
      houter2
    _ =
        (∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                  Complex.I) *
              f h ∂volume) *
          charFun
            (volume.withDensity
              (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))
            t :=
      congrArg (fun I : ℂ => I * charFun μn t) hdens

/-- Left-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`: for any
`c`, integrals along `y ↦ toLp 2 (c + y)` are unchanged. -/
theorem integral_toLp_trans {F : Type*} [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [OpensMeasurableSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    [SecondCountableTopology F] (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → F)
    (hg : MeasureTheory.AEStronglyMeasurable g volume) :
    ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume =
      ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  have hTmeas :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) := by
    fun_prop
  have hTmap :
    MeasureTheory.Measure.map
        (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume =
      volume := by
    have heq :
      (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) =
        (WithLp.toLp 2 c + ·) := by
      funext y
      simp only [WithLp.toLp_add, WithLp.toLp_ofLp]
    rw [heq, MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  calc
    ∫ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume =
        ∫ y : EuclideanSpace ℝ (Fin n),
          g
            y ∂(MeasureTheory.Measure.map
            (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume) :=
      (integral_map hTmeas.aemeasurable
          (by
            rw [hTmap]; exact hg)).symm
    _ = ∫ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by rw [hTmap]

/-- Left-translation invariance of `volume` integrals on `EuclideanSpace ℝ (Fin n)`: for any
`c`, integrals along `y ↦ toLp 2 (c + y)` are unchanged (ℝ≥0∞ version). -/
theorem lintegral_toLp_trans (n : ℕ) (c : Fin n → ℝ) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume =
      ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by
  have hTmeas :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) := by
    fun_prop
  have hTmap :
    MeasureTheory.Measure.map
        (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume =
      volume := by
    have heq :
      (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) =
        (WithLp.toLp 2 c + ·) := by
      funext y
      simp only [WithLp.toLp_add, WithLp.toLp_ofLp]
    rw [heq, MeasureTheory.map_add_left_eq_self volume (WithLp.toLp 2 c)]
  calc
    ∫⁻ y : EuclideanSpace ℝ (Fin n), g (WithLp.toLp 2 (c + (y : Fin n → ℝ))) ∂volume =
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
          g
            y ∂(MeasureTheory.Measure.map
            (fun y : EuclideanSpace ℝ (Fin n) => WithLp.toLp 2 (c + (y : Fin n → ℝ))) volume) :=
      (lintegral_map hg hTmeas).symm
    _ = ∫⁻ y : EuclideanSpace ℝ (Fin n), g y ∂volume := by rw [hTmap]

/-- For fixed `h`, the density `y ↦ f_n(y - A h)` is the noise pdf translated by `-A h`, so it
has Lebesgue mass `1`. -/
theorem lintegral_noiseDens_mass (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (noiseDens n S hS A y x) ∂volume = 1 := by
  have hposn :
    ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z := by
    intro z
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS z]
    positivity
  have hintn :
    ∫ z : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z ∂volume =
      1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf :
      ∀ z : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS z =
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z :=
      fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun z => (hpdf z).symm)).trans h1
  have hfnint :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)
      volume :=
    MeasureTheory.Integrable.of_integral_ne_zero
      (by
        rw [hintn]; exact one_ne_zero)
  have hlintn :
    ∫⁻ z : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) ∂volume =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint (Filter.Eventually.of_forall fun z => hposn z),
      hintn, ENNReal.ofReal_one]
  have hndT :
    ∀ y : EuclideanSpace ℝ (Fin n),
      noiseDens n S hS A y x =
        multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro y
    simp only [noiseDens]
    rw [show
        ((y : Fin n → ℝ) - A.mulVec (x : Fin n → ℝ)) =
          (-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ))
        from by ring]
  calc
    ∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (noiseDens n S hS A y x) ∂volume =
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal
            (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
              (WithLp.toLp 2 ((-(A.mulVec (x : Fin n → ℝ)) + (y : Fin n → ℝ))))) ∂volume :=
      lintegral_congr (fun y => by rw [hndT y])
    _ =
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y) ∂volume :=
      lintegral_toLp_trans n (-(A.mulVec (x : Fin n → ℝ)))
        (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))
        (ENNReal.measurable_ofReal.comp (measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS))
    _ = 1 := hlintn

/-- Tonelli's theorem on the coupled integrand `(y, h) ↦ f_n(y - A h) f(h)`: the `ℝ≥0∞`-norm
integral of the Bochner integrand in `charFun_fyPDF_density` over `volume.prod volume` equals
`1`, so the integrand is integrable although both factors have infinite mass. -/
theorem lintegral_enorm_noiseDens_mul (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ ∂(volume.prod volume) =
      1 := by
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hposa : ∀ (y h : EuclideanSpace ℝ (Fin n)), 0 ≤ noiseDens n S hS A y h := by
    intro y h
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    positivity
  have hfnmeas :
    Measurable
      (fun z : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hpt :
    ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ =
        ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2) := by
    intro p
    have habs : |noiseDens n S hS A p.1 p.2 * f p.2| = noiseDens n S hS A p.1 p.2 * f p.2 := by
      rw [abs_mul, abs_of_nonneg (hposa p.1 p.2), abs_of_nonneg (hposf p.2)]
    calc
      ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ =
          ENNReal.ofReal |noiseDens n S hS A p.1 p.2 * f p.2| :=
        Real.enorm_eq_ofReal_abs _
      _ = ENNReal.ofReal (noiseDens n S hS A p.1 p.2 * f p.2) := by rw [habs]
      _ = ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2) :=
        ENNReal.ofReal_mul (hposa p.1 p.2)
  have hmeas2 :
    AEMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1))
      (volume.prod volume) :=
    (ENNReal.measurable_ofReal.comp (hndmeas.comp measurable_swap)).aemeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable hfint.aemeasurable.comp_fst)
  have hswap :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2) ∂(volume.prod volume) =
      ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A p.2 p.1) *
          ENNReal.ofReal (f p.1) ∂(volume.prod volume) :=
    (lintegral_prod_swap
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (noiseDens n S hS A p.1 p.2) * ENNReal.ofReal (f p.2))).symm
  have hton :
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1) ∂(volume.prod volume) =
      ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume ∂volume :=
    lintegral_prod
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (noiseDens n S hS A p.2 p.1) * ENNReal.ofReal (f p.1))
      hmeas2
  have hinner :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ y : EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume =
        ENNReal.ofReal (f x) := by
    intro x
    have hmeasY :
      Measurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (noiseDens n S hS A y x)) := by
      have h0 :
        Measurable
          ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (noiseDens n S hS A p.1 p.2)) ∘
            (fun y : EuclideanSpace ℝ (Fin n) => (y, x))) :=
        (ENNReal.measurable_ofReal.comp hndmeas).comp
          (by fun_prop : Measurable (fun y : EuclideanSpace ℝ (Fin n) => (y, x)))
      have hfun :
        ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
              ENNReal.ofReal (noiseDens n S hS A p.1 p.2)) ∘
            (fun y : EuclideanSpace ℝ (Fin n) => (y, x))) =
          (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (noiseDens n S hS A y x)) := by
        funext y
        simp [Function.comp]
      rw [hfun] at h0
      exact h0
    have h1 := lintegral_mul_const (μ := volume) (ENNReal.ofReal (f x)) hmeasY
    rw [lintegral_noiseDens_mass n S hS A x, one_mul] at h1
    exact h1
  calc
    ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ‖(noiseDens n S hS A p.1 p.2 * f p.2 : ℝ)‖ₑ ∂(volume.prod volume) =
        ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A p.1 p.2) *
            ENNReal.ofReal (f p.2) ∂(volume.prod volume) :=
      lintegral_congr hpt
    _ =
        ∫⁻ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          ENNReal.ofReal (noiseDens n S hS A p.2 p.1) *
            ENNReal.ofReal (f p.1) ∂(volume.prod volume) :=
      hswap
    _ =
        ∫⁻ x : EuclideanSpace ℝ (Fin n),
          ∫⁻ y : EuclideanSpace ℝ (Fin n),
            ENNReal.ofReal (noiseDens n S hS A y x) * ENNReal.ofReal (f x) ∂volume ∂volume :=
      hton
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume :=
      lintegral_congr (fun x => hinner x)
    _ = 1 := by
      rw [←
        ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall fun x => hposf x),
        hf.2, ENNReal.ofReal_one]

/-- The density-side characteristic function: the characteristic function of the measure with
density `f_y(y) = ∫ f_n(y - A h) f(h) dh` factors into the same `h`-integral times the
characteristic function of the noise. Fubini is applied on `volume.prod volume` (both factors
infinite measures!), so integrability of the joint integrand is proved by Tonelli:
`∫⁻ ‖G‖ = (∫⁻ f)(∫⁻ f_n) = 1`. -/
theorem charFun_fyPDF_density (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (t : EuclideanSpace ℝ (Fin n)) :
    charFun (volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A f y))) t =
      (∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            f h ∂volume) *
        charFun
          (volume.withDensity
            (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))
          t := by
  classical
  -- pointwise nonnegativity and integrability of the two pdfs
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hposn :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := by
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
  have hintn :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume =
      1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf :
      ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x =
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x :=
      fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  have hfnint :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x)
      volume :=
    MeasureTheory.Integrable.of_integral_ne_zero
      (by
        rw [hintn]; exact one_ne_zero)
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall fun x => hposf x),
      hf.2, ENNReal.ofReal_one]
  have hlintn :
    ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∂volume =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint (Filter.Eventually.of_forall fun x => hposn x),
      hintn, ENNReal.ofReal_one]
  -- translation invariance of `volume` is provided by `integral_toLp_trans` and
  -- `lintegral_toLp_trans`; the Tonelli integrability is provided by
  -- `lintegral_enorm_noiseDens_mul`
  -- `noiseDens` as the noise pdf evaluated along the translation `y ↦ y - A h`
  have hndT :
    ∀ (h y : EuclideanSpace ℝ (Fin n)),
      noiseDens n S hS A y h =
        multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro h y
    simp only [noiseDens]
    rw [show
        ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) =
          (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))
        from by ring]
  -- measurability facts
  have hfnmeas :
    Measurable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hφmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ p.1 t) * Complex.I)) := by
    fun_prop
  -- replace `f` by a measurable representative
  have hfae : AEMeasurable f volume := hfint.aemeasurable
  set f' : EuclideanSpace ℝ (Fin n) → ℝ := hfae.mk f with hf'def
  have hf'meas : Measurable f' := hfae.measurable_mk
  have hf'ae : f =ᵐ[volume] f' := hfae.ae_eq_mk
  -- inner integrals agree a.e., hence pointwise after swapping the integrand
  have hfy' :
    ∀ y : EuclideanSpace ℝ (Fin n),
      ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f' h ∂volume =
        ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume := by
    intro y
    exact integral_congr_ae (hf'ae.mono fun x hx => by simp only [hx])
  -- measurability of the map `y ↦ ∫ f_n(y - A h) f'(h) dh` via Fubini's measurability lemma
  have hmeasF' :
    StronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f' h ∂volume) :=
    (hndmeas.comp measurable_swap).mul
        (hf'meas.comp measurable_fst) |>.stronglyMeasurable.integral_prod_left
  -- hence a.e.-measurability of the density `f_y`
  have hmeasrho :
    AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (fyPDF n S hS A f y)) volume :=
    AEMeasurable.congr (ENNReal.measurable_ofReal.comp_aemeasurable hmeasF'.aemeasurable)
      (Filter.Eventually.of_forall fun y => by
        simp only [fyPDF]
        exact congrArg ENNReal.ofReal (hfy' y))
  -- Tonelli: the coupled integrand is integrable on the product
  have hDint :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2 * f p.2)
      (volume.prod volume) :=
    ⟨hndmeas.aestronglyMeasurable.mul hfint.1.comp_snd, by
      rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_noiseDens_mul n S hS A f hf]
      exact ENNReal.one_lt_top⟩
  -- the noise measure, as a named local abbreviation
  set μn : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.withDensity
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)) with
    hμndef
  have hexpmeas :
    Measurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        Complex.exp (Complex.ofReal (inner ℝ x t) * Complex.I)) := by
    fun_prop
  -- the characteristic function of the noise in integral form
  have hmeasφn :
    AEMeasurable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x))
      volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfnint.aemeasurable
  have hcharN :
    ∫ z : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
          Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) ∂volume =
      charFun μn t := by
    rw [hμndef, charFun_apply,
      integral_withDensity_eq_integral_toReal_smul₀ hmeasφn (by simp)
        (fun z => Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show
      Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
          Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z) =
        (ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)).toReal •
          Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I)
    rw [Complex.real_smul, ENNReal.toReal_ofReal (hposn z), mul_comm]
  -- Fubini: the complex integrand is dominated by the Tonelli-integrable `hDint`
  have hGaes :
    MeasureTheory.AEStronglyMeasurable
      (Function.uncurry fun (y h : EuclideanSpace ℝ (Fin n)) =>
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
          (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)))
      (volume.prod volume) :=
    (hφmeas.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp hndmeas).aemeasurable.aestronglyMeasurable.mul
        ((Complex.measurable_ofReal.comp_aemeasurable
            hfint.aemeasurable.comp_snd).aestronglyMeasurable)))
  have hintH :
    MeasureTheory.Integrable
      (Function.uncurry fun (y h : EuclideanSpace ℝ (Fin n)) =>
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
          (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)))
      (volume.prod volume) := by
    refine hDint.mono' hGaes (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    show
      ‖(Complex.exp (Complex.ofReal (inner ℝ p.1 t) * Complex.I)) *
            (Complex.ofReal (noiseDens n S hS A p.1 p.2) * Complex.ofReal (f p.2))‖ =
        noiseDens n S hS A p.1 p.2 * f p.2
    have hn1 : ‖Complex.ofReal (noiseDens n S hS A p.1 p.2)‖ = |noiseDens n S hS A p.1 p.2| :=
      RCLike.norm_ofReal _
    have hf1 : ‖Complex.ofReal (f p.2)‖ = |f p.2| := RCLike.norm_ofReal _
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hn1, hf1,
      abs_of_nonneg (hposa p.1 p.2), abs_of_nonneg (hposf p.2)]
  -- per `y`: move the constant factor out of the `h`-integral
  have hinner :
    ∀ y : EuclideanSpace ℝ (Fin n),
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
          Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume) =
        ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume := by
    intro y
    have h1 :=
      integral_const_mul (μ := volume) (Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I))
        (fun h : EuclideanSpace ℝ (Fin n) =>
          Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h))
    have h2 :
      ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h) ∂volume =
        Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume) := by
      rw [integral_congr_ae
          (Filter.Eventually.of_forall fun h =>
            (Complex.ofReal_mul (noiseDens n S hS A y h) (f h)).symm)]
      exact integral_ofReal
    calc
      Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume) =
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            ∫ h : EuclideanSpace ℝ (Fin n),
              Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h) ∂volume :=
        by rw [h2]
      _ =
          ∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
              (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume :=
        h1.symm
  -- per `h`: move the `f`-factor out of the `y`-integral
  have hstep4 :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume =
        (∫ y : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
              Complex.ofReal (noiseDens n S hS A y h) ∂volume) *
          Complex.ofReal (f h) := by
    intro h
    have h1 :=
      integral_mul_const (μ := volume) (Complex.ofReal (f h))
        (fun y : EuclideanSpace ℝ (Fin n) =>
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal (noiseDens n S hS A y h))
    refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans h1
    ring
  -- per `h`: the translated inner `y`-integral is the noise characteristic function
  have hinner2 :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal (noiseDens n S hS A y h) ∂volume =
        charFun μn t *
          Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
              Complex.I) := by
    intro h
    have hφsh :
      ∀ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) =
          Complex.exp
              (Complex.ofReal
                  (inner ℝ (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) t) *
                Complex.I) *
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                Complex.I) := by
      intro y
      have heq :
        (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) +
            (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) =
          y := by
        rw [← WithLp.toLp_add,
          show
            (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)) + A.mulVec (h : Fin n → ℝ) =
              (y : Fin n → ℝ)
            by ring]
      conv_lhs => rw [← heq]
      rw [inner_add_left, Complex.ofReal_add, add_mul, Complex.exp_add]
    have hGtrans :
      ∀ y : EuclideanSpace ℝ (Fin n),
        Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal (noiseDens n S hS A y h) =
          (fun z : EuclideanSpace ℝ (Fin n) =>
                Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
                  Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) *
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                Complex.I) := by
      intro y
      rw [hndT h y, hφsh y, mul_right_comm]
    have hmeasg :
      MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) =>
          Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
            Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
        volume :=
      (hexpmeas.mul (Complex.measurable_ofReal.comp hfnmeas)).aestronglyMeasurable
    calc
      ∫ y : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
              Complex.ofReal (noiseDens n S hS A y h) ∂volume =
          ∫ y : EuclideanSpace ℝ (Fin n),
            (fun z : EuclideanSpace ℝ (Fin n) =>
                  Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
                    Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
                (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) *
              Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                  Complex.I) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hGtrans)
      _ =
          (∫ y : EuclideanSpace ℝ (Fin n),
              (fun z : EuclideanSpace ℝ (Fin n) =>
                  Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
                    Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
                (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))) ∂volume) *
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) :=
        integral_mul_const
          (Complex.exp
            (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (fun z : EuclideanSpace ℝ (Fin n) =>
                Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
                  Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
              (WithLp.toLp 2 (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))))
      _ =
          (∫ y : EuclideanSpace ℝ (Fin n),
              Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
                Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y) ∂volume) *
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) :=
        congrArg
          (fun I : ℂ =>
            I *
              Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I))
          (integral_toLp_trans n (-(A.mulVec (h : Fin n → ℝ)))
            (fun z : EuclideanSpace ℝ (Fin n) =>
              Complex.exp (Complex.ofReal (inner ℝ z t) * Complex.I) *
                Complex.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z))
            hmeasg)
      _ =
          charFun μn t *
            Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) :=
        by rw [hcharN]
  -- final assembly
  calc
    charFun
          (volume.withDensity
            (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (fyPDF n S hS A f y)))
          t =
        ∫ y : EuclideanSpace ℝ (Fin n),
          (ENNReal.ofReal (fyPDF n S hS A f y)).toReal •
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) ∂volume :=
      by
      rw [charFun_apply,
        integral_withDensity_eq_integral_toReal_smul₀ hmeasrho (by simp)
          (fun y => Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I))]
    _ =
        ∫ y : EuclideanSpace ℝ (Fin n),
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal
              (∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume) ∂volume :=
      by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show
        (ENNReal.ofReal (fyPDF n S hS A f y)).toReal •
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) =
          Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
            Complex.ofReal (∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume)
      rw [Complex.real_smul, ENNReal.toReal_ofReal (hposfy y), mul_comm]
      simp only [fyPDF]
    _ =
        ∫ y : EuclideanSpace ℝ (Fin n),
          ∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
              (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          ∫ y : EuclideanSpace ℝ (Fin n),
            Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
              (Complex.ofReal (noiseDens n S hS A y h) * Complex.ofReal (f h)) ∂volume ∂volume :=
      integral_integral_swap hintH
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          (∫ y : EuclideanSpace ℝ (Fin n),
              Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
                Complex.ofReal (noiseDens n S hS A y h) ∂volume) *
            Complex.ofReal (f h) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall hstep4)
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          (charFun μn t *
              Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                  Complex.I)) *
            Complex.ofReal (f h) ∂volume :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun h => by
          show
            (∫ y : EuclideanSpace ℝ (Fin n),
                  Complex.exp (Complex.ofReal (inner ℝ y t) * Complex.I) *
                    Complex.ofReal (noiseDens n S hS A y h) ∂volume) *
                Complex.ofReal (f h) =
              (charFun μn t *
                  Complex.exp
                    (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                      Complex.I)) *
                Complex.ofReal (f h)
          rw [hinner2 h])
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            f h *
            charFun μn t ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun h => by ring)
    _ =
        (∫ h : EuclideanSpace ℝ (Fin n),
            Complex.exp
                (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) *
                  Complex.I) *
              f h ∂volume) *
          charFun μn t :=
      integral_mul_const (charFun μn t)
        (fun h : EuclideanSpace ℝ (Fin n) =>
          Complex.exp
              (Complex.ofReal (inner ℝ (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ))) t) * Complex.I) *
            f h)

/-- `f_y(y) = ∫ f_n(y - A h) f(h) dh` is a pdf: nonnegative (integrandwise) with total
mass `1` (Fubini on the Tonelli-integrable joint integrand, then the translation `y ↦ y - A h`
in the inner integral). -/
theorem isPdf_fyPDF (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    IsPdf (fyPDF n S hS A f) := by
  classical
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hfnmeas :
    Measurable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) :=
    measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
  have hndmeas :
    Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2) := by
    simp only [noiseDens]
    exact hfnmeas.comp (by fun_prop)
  have hndT :
    ∀ (h y : EuclideanSpace ℝ (Fin n)),
      noiseDens n S hS A y h =
        multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) := by
    intro h y
    simp only [noiseDens]
    rw [show
        ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) =
          (-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ))
        from by ring]
  have hintn :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume =
      1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf :
      ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x =
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x :=
      fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  -- mass of the translated noise density along each `h`
  have hmassy :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ∫ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume = 1 := by
    intro h
    calc
      ∫ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ∂volume =
          ∫ y : EuclideanSpace ℝ (Fin n),
            multivariateGaussianPDF n (0 : Fin n → ℝ) S hS
              (WithLp.toLp 2 ((-(A.mulVec (h : Fin n → ℝ)) + (y : Fin n → ℝ)))) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => hndT h y)
      _ =
          ∫ y : EuclideanSpace ℝ (Fin n),
            multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y ∂volume :=
        integral_toLp_trans n (-(A.mulVec (h : Fin n → ℝ)))
          (fun z : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS z)
          hfnmeas.aestronglyMeasurable
      _ = 1 := hintn
  -- Fubini on the ℝ-valued joint integrand
  have hDint :
    MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        noiseDens n S hS A p.1 p.2 * f p.2)
      (volume.prod volume) :=
    ⟨hndmeas.aestronglyMeasurable.mul hfint.1.comp_snd, by
      rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_noiseDens_mul n S hS A f hf]
      exact ENNReal.one_lt_top⟩
  refine ⟨?_, ?_⟩
  · intro y
    simp only [fyPDF]
    exact
      integral_nonneg fun h =>
        mul_nonneg
          (by
            simp only [noiseDens]
            rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
                (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
            positivity)
          (hposf h)
  · calc
      ∫ y : EuclideanSpace ℝ (Fin n), fyPDF n S hS A f y ∂volume =
          ∫ y : EuclideanSpace ℝ (Fin n),
            ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume ∂volume :=
        by simp only [fyPDF]
      _ =
          ∫ h : EuclideanSpace ℝ (Fin n),
            ∫ y : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h * f h ∂volume ∂volume :=
        integral_integral_swap hDint
      _ = ∫ h : EuclideanSpace ℝ (Fin n), f h ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        have h1 :=
          integral_mul_const (μ := volume) (f h)
            (fun y : EuclideanSpace ℝ (Fin n) => noiseDens n S hS A y h)
        rw [hmassy h, one_mul] at h1
        exact h1
      _ = 1 := hf.2

/-- Assembly of Step 3: the law of `y = A h + n` equals `volume.withDensity (fun y =>
ENNReal.ofReal (f_y y))`, i.e. `f_y` is the pdf of the observations. Both sides are finite
measures on `EuclideanSpace ℝ (Fin n)` with equal characteristic functions
(`charFun_map_fy` and `charFun_fyPDF_density`), so `Measure.ext_of_charFun` applies. -/
theorem fyPDF_eq_map (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    Measure.map
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (A.mulVec (p.1 : Fin n → ℝ)) + p.2)
        ((volume.withDensity (fun h => ENNReal.ofReal (f h))).prod
          (volume.withDensity
            (fun y => ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y)))) =
      volume.withDensity (fun y => ENNReal.ofReal (fyPDF n S hS A f y)) := by
  classical
  have hposf : 0 ≤ f := hf.1
  have hfint : MeasureTheory.Integrable f volume := integrable_of_isPdf hf
  have hpdfpdf : IsPdf (fyPDF n S hS A f) := isPdf_fyPDF n S hS A f hf
  have hposfy : 0 ≤ fyPDF n S hS A f := hpdfpdf.1
  have hpdfint : MeasureTheory.Integrable (fyPDF n S hS A f) volume := integrable_of_isPdf hpdfpdf
  -- finiteness of the two density measures on the left
  have hlintf : ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (f x) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfint (Filter.Eventually.of_forall fun x => hposf x),
      hf.2, ENNReal.ofReal_one]
  have hposn :
    ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x := by
    intro x
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS x]
    positivity
  have hintn :
    ∫ x : EuclideanSpace ℝ (Fin n), multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x ∂volume =
      1 := by
    have h1 := integral_multivariateGaussianPDF_one n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS
    have hpdf :
      ∀ x : EuclideanSpace ℝ (Fin n),
        multivariateGaussianPDF n (WithLp.toLp 2 (0 : Fin n → ℝ)) S hS x =
          multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x :=
      fun _ => rfl
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => (hpdf x).symm)).trans h1
  have hfnint :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x)
      volume :=
    MeasureTheory.Integrable.of_integral_ne_zero
      (by
        rw [hintn]; exact one_ne_zero)
  have hlintn :
    ∫⁻ x : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∂volume =
      1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hfnint (Filter.Eventually.of_forall fun x => hposn x),
      hintn, ENNReal.ofReal_one]
  have hμhfin :
    MeasureTheory.IsFiniteMeasure
      (volume.withDensity (fun h : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (f h))) :=
    isFiniteMeasure_withDensity
      (by
        rw [hlintf]; simp)
  have hμnfin :
    MeasureTheory.IsFiniteMeasure
      (volume.withDensity
        (fun y : EuclideanSpace ℝ (Fin n) =>
          ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS y))) :=
    isFiniteMeasure_gaussianPDF_withDensity n (0 : Fin n → ℝ) S hS
  -- finiteness of the right-hand side: `f_y` has mass `1`
  have hrhsfin :
    MeasureTheory.IsFiniteMeasure
      (volume.withDensity
        (fun y : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (fyPDF n S hS A f y))) :=
    isFiniteMeasure_withDensity
      (by
        rw [←
          ofReal_integral_eq_lintegral_ofReal hpdfint
            (Filter.Eventually.of_forall fun y => hposfy y),
          hpdfpdf.2, ENNReal.ofReal_one]
        exact ENNReal.one_ne_top)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_fy n S hS A f hf t, charFun_fyPDF_density n S hS A f hf t]

/-! ## The main result (appendix_1.tex, `thm:main_result`)

The conditional mean estimate (CME) for the model `y = A h + n` is
`ĥ(y) = ∫ h · f_n(y - A h) f_h(h) / f_y(y) dh`. The main theorem states that if `f_h^{(K)}`
is a sequence of continuous pdfs converging uniformly to `f_h`, then the corresponding CMEs
converge to `ĥ` pointwise, and uniformly on every closed ball `B_r = {y : ‖y‖ ≤ r}`.

Notes on the formalization:
* Membership in the set `C` of continuous pdfs is expressed as `IsPdf f ∧ Continuous f`
  (`IsPdf` is the existing predicate; continuity is a separate hypothesis, as in
  `uniform_convergence_fy_pdf`).
* `f_n = N(0, Σ)` is not an arbitrary member of `C` but *the* Gaussian pdf
  `multivariateGaussianPDF n 0 S hS` (via `noiseDens`/`fyPDF`); its membership in `C`
  (positivity, mass, continuity) is derivable from `S.PosDef` and is not a hypothesis.
* Invertibility of `A` is `IsUnit A.det`, matching `uniform_convergence_fy`.
* The statement does *not* need `VanishesAtInfinity fh`: the `K`-independent factor
  `∫ ‖h‖ f_n(y - A h) dh` in the proof is bounded via `lem:bound_norm`'s Gaussian moment
  computation, which involves only `f_n`.
* `ĥ` and `ĥ^{(K)}` are the same construction applied to `fh` and `fhK K` respectively
  (one definition `cme`, instantiated twice).
* Division by `f_y^{(K)}(y)` is total in `ℝ`; positivity of `f_y^{(K)}` (proved in the
  appendix) is a fact about the construction, not a hypothesis of the statement. -/

/-! ## Step B.1 of `plan_main_theorem.md`: quantitative Gaussian domination -/

/-- The Euclidean norm squared of a plain vector agrees with its dot product with itself. -/
theorem dotProduct_self_eq_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  calc
    v ⬝ᵥ v = v ⬝ᵥ star v := by rw [show star v = v from by simp]
    _ = inner ℝ (WithLp.toLp 2 v) (WithLp.toLp 2 v) := (EuclideanSpace.inner_toLp_toLp v v).symm
    _ = ‖WithLp.toLp 2 v‖ ^ 2 := real_inner_self_eq_norm_sq _

/-- Quantitative positive definiteness (Step B.1 of `plan_main_theorem.md`): a positive
definite matrix has a quadratic form dominating a positive multiple of `v ⬝ᵥ v`. Via the
positive square root `B = √M` and the operator norm of `B⁻¹`:
`‖v‖ = ‖B⁻¹ (B v)‖ ≤ ‖B⁻¹‖ ‖B v‖`. -/
theorem posDef_quadForm_ge (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : Fin n → ℝ, lam * (v ⬝ᵥ v) ≤ (M *ᵥ v) ⬝ᵥ v := by
  classical
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  set B : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt M with hBdef
  have hBB : B * B = M := CFC.sqrt_mul_sqrt_self M hM0
  have hBnn : 0 ≤ B := by
    rw [hBdef]; exact CFC.sqrt_nonneg M
  have hBher : B.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hBnn).1
  have hBT : Bᵀ = B := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hBher
  have hBdetSq : B.det ^ 2 = M.det := by rw [pow_two, ← Matrix.det_mul, hBB]
  have hBdet : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr
      (by
        intro h0
        have h2 : M.det = 0 := by
          rw [← hBdetSq, h0]; simp
        exact absurd h2 (ne_of_gt hM.det_pos))
  -- the shift identity
  have hinv : ∀ u : Fin n → ℝ, B⁻¹ *ᵥ (B *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBdet, Matrix.one_mulVec]
  -- the mulVec of `B⁻¹` as a continuous linear map, with its operator norm
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) B⁻¹ with hLdef
  have hLapply : ∀ x : EuclideanSpace ℝ (Fin n), (L x).ofLp = B⁻¹ *ᵥ x.ofLp := fun x =>
    Matrix.ofLp_toEuclideanCLM B⁻¹ x
  set K : ℝ := ‖L‖ with hKdef
  -- the key element identity: `v = B⁻¹ *ᵥ (B *ᵥ v)` at the `EuclideanSpace` level
  have h1 :
    ∀ v : Fin n → ℝ, (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) = L (WithLp.toLp 2 (B *ᵥ v)) := by
    intro v
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_toLp, hLapply (WithLp.toLp 2 (B *ᵥ v)), WithLp.ofLp_toLp]
    exact (hinv v).symm
  by_cases hK0 : K = 0
  · -- trivial space: every quadratic form vanishes
    refine ⟨1, one_pos, fun v => ?_⟩
    have hnorm0 : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ = 0 := by
      have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (B *ᵥ v))
      rw [← h1 v, ← hKdef, hK0, zero_mul] at h2
      exact le_antisymm h2 (norm_nonneg _)
    have hRHS : 0 ≤ (M *ᵥ v) ⬝ᵥ v := by
      have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hM.posSemidef v
      rwa [dotProduct_comm] at h
    rw [dotProduct_self_eq_norm_sq v, hnorm0]
    simp
    exact hRHS
  · have hKpos : 0 < K := by
      rw [hKdef]
      refine norm_pos_iff.mpr ?_
      intro hL0
      exact
        hK0
          (by
            rw [hKdef, hL0]; exact norm_zero)
    refine ⟨K⁻¹ * K⁻¹, by positivity, fun v => ?_⟩
    have hbound :
      K⁻¹ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℝ (Fin n))‖ := by
      have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (B *ᵥ v))
      rw [← h1 v, ← hKdef] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (le_of_lt hKpos))
      rwa [← mul_assoc, inv_mul_cancel₀ hK0, one_mul] at h3
    have hmove : (M *ᵥ v) ⬝ᵥ v = ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      have hid : (M *ᵥ v) = B *ᵥ (B *ᵥ v) := by rw [Matrix.mulVec_mulVec, ← hBB]
      have ht : v ⬝ᵥ Bᵀ *ᵥ (B *ᵥ v) = (B *ᵥ v) ⬝ᵥ B *ᵥ v :=
        Matrix.dotProduct_transpose_mulVec B v (B *ᵥ v)
      rw [hBT] at ht
      calc
        (M *ᵥ v) ⬝ᵥ v = (B *ᵥ (B *ᵥ v)) ⬝ᵥ v := by rw [hid]
        _ = v ⬝ᵥ (B *ᵥ (B *ᵥ v)) := dotProduct_comm _ _
        _ = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := ht
        _ = ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
          dotProduct_self_eq_norm_sq (B *ᵥ v)
    calc
      K⁻¹ * K⁻¹ * (v ⬝ᵥ v) = (K⁻¹ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖) ^ 2 := by
        rw [dotProduct_self_eq_norm_sq v]
        ring
      _ ≤ ‖(WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℝ (Fin n))‖ ^ 2 :=
        (sq_le_sq₀ (mul_nonneg (inv_nonneg.mpr (le_of_lt hKpos)) (norm_nonneg _))
              (norm_nonneg _)).mpr
          hbound
      _ = (M *ᵥ v) ⬝ᵥ v := hmove.symm

/-- Quantitative Gaussian domination (Step B.1 of `plan_main_theorem.md`): the noise density
along `y − A·` decays like a Gaussian in `‖h‖`, with an `exp(κ‖y‖²)` factor; all constants
depend only on `S` and `A`. -/
theorem noiseDens_decay (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    ∃ κ c cS : ℝ,
      0 < κ ∧
        0 < c ∧
        0 < cS ∧
        ∀ (y h : EuclideanSpace ℝ (Fin n)),
          noiseDens n S hS A y h ≤ cS * Real.exp (κ * ‖y‖ ^ 2) * Real.exp (-(c * ‖h‖ ^ 2)) := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSdetpos : 0 < S.det := hS.det_pos
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hSdetpos
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hSdetpos)
  have hSU : IsUnit (S : Matrix (Fin n) (Fin n) ℝ) := (Matrix.isUnit_iff_isUnit_det S).mpr hSdet
  have hSinvU : IsUnit (S⁻¹ : Matrix (Fin n) (Fin n) ℝ) := Matrix.isUnit_nonsing_inv_iff.mpr hSU
  -- the operator norm of the mulVec of `A⁻¹`
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A⁻¹ with hLdef
  have hLapply : ∀ x : EuclideanSpace ℝ (Fin n), (L x).ofLp = A⁻¹ *ᵥ x.ofLp := fun x =>
    Matrix.ofLp_toEuclideanCLM A⁻¹ x
  have hAinv : ∀ u : Fin n → ℝ, A⁻¹ *ᵥ (A *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]
  have h1 :
    ∀ v : Fin n → ℝ, (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) = L (WithLp.toLp 2 (A *ᵥ v)) := by
    intro v
    apply WithLp.ofLp_injective
    rw [WithLp.ofLp_toLp, hLapply (WithLp.toLp 2 (A *ᵥ v)), WithLp.ofLp_toLp]
    exact (hAinv v).symm
  set K : ℝ := ‖L‖ with hKdef
  by_cases hK0 : K = 0
  · -- trivial space (n = 0): all norms vanish
    refine
      ⟨1, 1, ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹, one_pos, one_pos,
        inv_pos.mpr (mul_pos h2pi hSqrtpos), ?_⟩
    intro y h
    have hnorm0y : ‖y‖ = 0 := by
      have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (A *ᵥ (y : Fin n → ℝ)))
      rw [← h1 (y : Fin n → ℝ), ← hKdef, hK0, zero_mul] at h2
      exact le_antisymm h2 (norm_nonneg _)
    have hnorm0h : ‖h‖ = 0 := by
      have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (A *ᵥ (h : Fin n → ℝ)))
      rw [← h1 (h : Fin n → ℝ), ← hKdef, hK0, zero_mul] at h2
      exact le_antisymm h2 (norm_nonneg _)
    rw [show (y : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 ((y : Fin n → ℝ)) from rfl, hnorm0y,
      show (h : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 ((h : Fin n → ℝ)) from rfl, hnorm0h]
    simp only [mul_zero, zero_pow two_ne_zero, Real.exp_zero, mul_one, neg_zero]
    simp only [noiseDens]
    exact
      multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
  · have hKpos : 0 < K := by
      refine norm_pos_iff.mpr ?_
      intro hL0
      exact
        hK0
          (by
            rw [hKdef, hL0]; exact norm_zero)
    have hAge :
      ∀ v : Fin n → ℝ,
        K⁻¹ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ≤
          ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℝ (Fin n))‖ := by
      intro v
      have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (A *ᵥ v))
      rw [← h1 v, ← hKdef] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (le_of_lt hKpos))
      rwa [← mul_assoc, inv_mul_cancel₀ hK0, one_mul] at h3
    -- `S⁻¹` is positive definite
    have hSH : S.IsHermitian := hS.1
    have hST : Sᵀ = S := by
      ext i j
      simpa using hSH.apply i j
    have hSinvH : S⁻¹.IsHermitian := by
      have h1 : S⁻¹ᵀ = S⁻¹ := by rw [← transpose_nonsing_inv S hSdet, hST]
      exact
        Matrix.ext
          (fun i j => by simpa using (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j i) h1).symm)
    have hSinvPD : S⁻¹.PosDef := by
      refine
        Matrix.posDef_iff_posSemidef_and_mulVec_injective.mpr
          ⟨?_, mulVec_injective_of_isUnit hSinvU⟩
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hSinvH ?_
      intro u
      have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hS.posSemidef (S⁻¹ *ᵥ u)
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hSdet, Matrix.one_mulVec] at h
      simpa [dotProduct_comm] using h
    obtain ⟨lamS, hlamS, hquadS⟩ := posDef_quadForm_ge n S⁻¹ hSinvPD
    refine
      ⟨lamS / 2, lamS / (4 * K * K), ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹,
        div_pos hlamS two_pos,
        div_pos hlamS (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hKpos) hKpos),
        inv_pos.mpr (mul_pos h2pi hSqrtpos), ?_⟩
    intro y h
    -- the explicit form of the noise density
    have hform :
      noiseDens n S hS A y h =
        ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
          Real.exp
            (-(((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
                  ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
                2)) := by
      simp only [noiseDens]
      rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))),
        WithLp.ofLp_toLp, sub_zero]
    -- the reverse triangle: `|K⁻¹‖h‖ − ‖y‖| ≤ ‖y − A·h‖`
    have h1' :
      (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
        y -
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
            EuclideanSpace ℝ (Fin n)) := by
      rw [WithLp.toLp_sub, WithLp.toLp_ofLp, WithLp.toLp_ofLp, sub_sub_cancel]
    have htri1 :
      ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ +
          ‖y‖ := by
      have h2 :
        ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ≤
          ‖y - (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ + ‖y‖ := by
        have h1 :=
          norm_add_le ((WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) - y) y
        rw [sub_add_cancel, norm_sub_rev] at h1
        exact h1
      have hyd :
        ‖y - (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ =
          ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
              EuclideanSpace ℝ (Fin n))‖ := by
        have h3 :
          y - (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
            (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
              EuclideanSpace ℝ (Fin n)) := by
          rw [h1', sub_sub_cancel]
        rw [h3]
      linarith [h2, hyd]
    have htri2 :
      ‖y‖ ≤
        ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ +
          ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ := by
      have h2' :
        y =
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) +
            (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) := by
        have h3 := (eq_sub_iff_add_eq).mp h1'
        rw [add_comm]
        exact h3.symm
      calc
        ‖y‖ =
            ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
                  EuclideanSpace ℝ (Fin n)) +
                (WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ :=
          by exact congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) h2'
        _ ≤
            ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
                  EuclideanSpace ℝ (Fin n))‖ +
              ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ :=
          norm_add_le _ _
    have habs :
      |‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ - ‖y‖| ≤
        ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ :=
      abs_le.mpr ⟨by linarith [htri1], by linarith [htri2]⟩
    have hsq :
      (‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ - ‖y‖) ^ 2 ≤
        ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^
          2 := by
      have h2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr habs
      rwa [sq_abs] at h2
    have hAh2 :
      (K⁻¹ * ‖h‖) ^ 2 ≤
        ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      have h1 :=
        mul_le_mul (hAge h) (hAge h) (mul_nonneg (inv_nonneg.mpr hKpos.le) (norm_nonneg _))
          (norm_nonneg _)
      rw [← pow_two, ← pow_two] at h1
      exact h1
    have hK2 :
      K⁻¹ * K⁻¹ * ‖h‖ ^ 2 ≤
        ‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      have h1d : (K⁻¹ * ‖h‖) ^ 2 = K⁻¹ * K⁻¹ * ‖h‖ ^ 2 := by ring
      rw [← h1d]
      exact hAh2
    have hlin :
      -(((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
              ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
            2) ≤
        (lamS / 2) * ‖y‖ ^ 2 + -(lamS / (4 * K * K) * ‖h‖ ^ 2) := by
      have h1 :
        lamS * (K⁻¹ * K⁻¹ * ‖h‖ ^ 2 / 2 - ‖y‖ ^ 2) ≤
          (S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
            ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) := by
        have h2 :
          lamS * (K⁻¹ * K⁻¹ * ‖h‖ ^ 2 / 2 - ‖y‖ ^ 2) ≤
            lamS *
              (‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2 -
                ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hK2]) (le_of_lt hlamS)
        have h3 :
          lamS *
              (‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2 -
                ‖y‖ ^ 2) ≤
            lamS *
              ((‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ - ‖y‖) ^
                2) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hlamS)
          nlinarith [sq_nonneg
              (‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ / 2 - ‖y‖)]
        have h4 :
          lamS *
              ((‖(WithLp.toLp 2 (A.mulVec (h : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ - ‖y‖) ^
                2) ≤
            lamS *
              ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
                    EuclideanSpace ℝ (Fin n))‖ ^
                2 :=
          mul_le_mul_of_nonneg_left hsq (le_of_lt hlamS)
        have h5 :
          lamS *
              ‖(WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :
                    EuclideanSpace ℝ (Fin n))‖ ^
                2 ≤
            lamS *
              (((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) ⬝ᵥ
                ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) := by
          rw [dotProduct_self_eq_norm_sq]
        linarith [h2, h3, h4, h5, hquadS ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))]
      have h1' :
        (lamS / (4 * K * K)) * ‖h‖ ^ 2 - (lamS / 2) * ‖y‖ ^ 2 ≤
          ((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
              ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
            2 := by
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [show
            ((1 : ℝ) / 2) * (lamS * (K⁻¹ * K⁻¹ * ‖h‖ ^ 2 / 2 - ‖y‖ ^ 2)) =
              (lamS / (4 * K * K)) * ‖h‖ ^ 2 - (lamS / 2) * ‖y‖ ^ 2
            from by ring,
          show
            ((1 : ℝ) / 2) *
                ((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
                  ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) =
              ((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
                  ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
                2
            from by ring] at h2
        exact h2
      have hnn :
        0 ≤
          (S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
            ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) := by
        have h :=
          Matrix.PosSemidef.dotProduct_mulVec_nonneg hSinvPD.posSemidef
            ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))
        simpa [dotProduct_comm] using h
      have hhalf :
        ((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
              ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
            2 ≤
          (S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
            ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)) :=
        div_le_self hnn (by norm_num)
      linarith [h1', hhalf]
    -- the exponential bound and the conclusion
    have hexp :
      Real.exp
          (-(((S⁻¹ *ᵥ ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) ⬝ᵥ
                ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) /
              2)) ≤
        Real.exp ((lamS / 2) * ‖y‖ ^ 2) * Real.exp (-(lamS / (4 * K * K) * ‖h‖ ^ 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hlin
    rw [hform, mul_assoc]
    exact mul_le_mul_of_nonneg_left hexp (le_of_lt (inv_pos.mpr (mul_pos h2pi hSqrtpos)))

/-- Uniform moment bound (Step A.1 of `plan_main_theorem.md`): on the ball `‖y‖ ≤ r` the
`K`-independent factor `∫ ‖h‖ f_n(y − A h) dh` is bounded by a constant depending only on
`n, S, A, r`. Via the translation `h = h' + A⁻¹ y` (`integral_toLp_trans`), the triangle
inequality, and the per-`y` integrability `integral_gaussian_bounded`. -/
theorem noiseDens_moment_uniform (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (r : ℝ) (_hr : 0 < r) :
    ∃ C : ℝ,
      ∀ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ ≤ r → ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume ≤ C := by
  classical
  -- the operator-norm constant of `A⁻¹`
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A⁻¹ with hLdef
  have hLapply : ∀ x : EuclideanSpace ℝ (Fin n), (L x).ofLp = A⁻¹ *ᵥ x.ofLp := fun x =>
    Matrix.ofLp_toEuclideanCLM A⁻¹ x
  set K : ℝ := ‖L‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hAYle :
    ∀ y : EuclideanSpace ℝ (Fin n),
      ‖(WithLp.toLp 2 (A⁻¹.mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖y‖ := by
    intro y
    have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (y : Fin n → ℝ))
    have h3 :
      (WithLp.toLp 2 (A⁻¹.mulVec (y : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
        L (WithLp.toLp 2 (y : Fin n → ℝ)) := by
      apply WithLp.ofLp_injective
      show A⁻¹ *ᵥ (y : Fin n → ℝ) = A⁻¹ *ᵥ (y : Fin n → ℝ)
      rfl
    rw [← h3] at h2
    exact h2
  -- the mass and integrability of the noise density at `y = 0`
  have hint0 : ∫ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A 0 h ∂volume = (|A.det| : ℝ)⁻¹ :=
    integral_noise_pullback n S hS A hA 0
  have hnd0 : MeasureTheory.Integrable (noiseDens n S hS A 0) volume :=
    MeasureTheory.Integrable.of_integral_ne_zero
      (by
        rw [hint0]
        exact inv_ne_zero (abs_ne_zero.mpr (isUnit_iff_ne_zero.mp hA)))
  refine
    ⟨(∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A 0 h ∂volume) +
        K * r * (|A.det| : ℝ)⁻¹,
      ?_⟩
  intro y hy
  set c : Fin n → ℝ := A⁻¹.mulVec (y : Fin n → ℝ) with hc
  have hAc : A.mulVec c = (y : Fin n → ℝ) := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  -- the measurability of the translated integrand
  have hG :
    MeasureTheory.AEStronglyMeasurable
      (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖ * noiseDens n S hS A y w) volume := by
    have hndY : MeasureTheory.AEStronglyMeasurable (noiseDens n S hS A y) volume := by
      have hcomp :
        noiseDens n S hS A y =
          (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
            (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
        funext h
        exact noiseDens_eq n S hS A y h
      rw [hcomp]
      exact
        ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
            (by fun_prop :
              Measurable
                (fun h : EuclideanSpace ℝ (Fin n) =>
                  y +
                    (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A))
                      h))).aestronglyMeasurable
    exact ((Continuous.aemeasurable continuous_norm).aestronglyMeasurable).mul hndY
  calc
    ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume =
        ∫ x : EuclideanSpace ℝ (Fin n),
          ‖(WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ *
            noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) ∂volume :=
      (integral_toLp_trans n c (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖ * noiseDens n S hS A y w)
          hG).symm
    _ =
        ∫ x : EuclideanSpace ℝ (Fin n),
          ‖(WithLp.toLp 2 (x : Fin n → ℝ)) + (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n))‖ *
            noiseDens n S hS A 0 x ∂volume :=
      by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show
        ‖(WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ *
            noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) =
          ‖(WithLp.toLp 2 (x : Fin n → ℝ)) + (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n))‖ *
            noiseDens n S hS A 0 x
      have hndEq :
        noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) = noiseDens n S hS A 0 x := by
        simp only [noiseDens]
        rw [Matrix.mulVec_add, hAc, WithLp.ofLp_zero]
        rw [show ((y : Fin n → ℝ) - (y + A.mulVec (x : Fin n → ℝ))) = (0 - A.mulVec (x : Fin n → ℝ))
            from by ring]
      have hnormEq :
        (WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
          (WithLp.toLp 2 (x : Fin n → ℝ)) + (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n)) := by
        rw [WithLp.toLp_add, add_comm]
      rw [hndEq, hnormEq]
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin n), (‖x‖ + K * ‖y‖) * noiseDens n S hS A 0 x ∂volume := by
      refine
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x =>
            mul_nonneg (norm_nonneg _)
              (by
                simp only [noiseDens]
                rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
                    (WithLp.toLp 2 (WithLp.ofLp 0 - A.mulVec (x : Fin n → ℝ)))]
                positivity))
          ?_ (Filter.Eventually.of_forall fun x => ?_)
      · -- integrability of the dominating integrand
        have hA :
          MeasureTheory.Integrable
            (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * noiseDens n S hS A 0 x) volume := by
          simpa only [noiseDens] using integral_gaussian_bounded n S hS A hA 0
        have hB :
          MeasureTheory.Integrable
            (fun x : EuclideanSpace ℝ (Fin n) => (K * ‖y‖) * noiseDens n S hS A 0 x) volume := by
          exact
            (MeasureTheory.Integrable.smul (K * ‖y‖) hnd0).congr
              (Filter.Eventually.of_forall fun x => by simp)
        have hpt :
          ∀ x : EuclideanSpace ℝ (Fin n),
            ‖x‖ * noiseDens n S hS A 0 x + (K * ‖y‖) * noiseDens n S hS A 0 x =
              (‖x‖ + K * ‖y‖) * noiseDens n S hS A 0 x :=
          fun x => by rw [add_mul]
        exact (hA.add hB).congr (Filter.Eventually.of_forall fun x => hpt x)
      · -- the pointwise bound
        refine
          mul_le_mul_of_nonneg_right (le_trans (norm_add_le _ _) (add_le_add (le_refl _) (hAYle y)))
            (by
              simp only [noiseDens]
              rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
                  (WithLp.toLp 2 (WithLp.ofLp 0 - A.mulVec (x : Fin n → ℝ)))]
              positivity)
  -- the split and the final bound
  have hA :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ * noiseDens n S hS A 0 x)
      volume := by
    simpa only [noiseDens] using integral_gaussian_bounded n S hS A hA 0
  have hB :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (K * ‖y‖) * noiseDens n S hS A 0 x) volume := by
    exact
      (MeasureTheory.Integrable.smul (K * ‖y‖) hnd0).congr
        (Filter.Eventually.of_forall fun x => by simp)
  have hpt :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (‖x‖ + K * ‖y‖) * noiseDens n S hS A 0 x =
        ‖x‖ * noiseDens n S hS A 0 x + (K * ‖y‖) * noiseDens n S hS A 0 x :=
    fun x => by rw [add_mul]
  have hsplit :
    ∫ x : EuclideanSpace ℝ (Fin n), (‖x‖ + K * ‖y‖) * noiseDens n S hS A 0 x ∂volume =
      (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ * noiseDens n S hS A 0 x ∂volume) +
        (∫ x : EuclideanSpace ℝ (Fin n), (K * ‖y‖) * noiseDens n S hS A 0 x ∂volume) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => hpt x), integral_add hA hB]
  have hc' :
    ∫ x : EuclideanSpace ℝ (Fin n), (K * ‖y‖) * noiseDens n S hS A 0 x ∂volume ≤
      (K * r) * (|A.det| : ℝ)⁻¹ := by
    rw [integral_const_mul, hint0]
    exact
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hK0)
        (inv_nonneg.mpr (abs_nonneg A.det))
  linarith [hsplit, hc']

/-- Step B.2 of `plan_main_theorem.md` (first part): the function `h ↦ ‖h‖ · f_n(−A h)`
is globally bounded by a positive constant. From the decay bound B.1 at `y = 0`, with the
two-case split `‖h‖ ≤ 1` / `‖h‖ ≥ 1` and the elementary estimates
`Real.exp (-(c * ‖h‖ ^ 2)) ≤ 1` and `c * ‖h‖ ≤ Real.exp (c * ‖h‖ ^ 2)`
(via `Real.add_one_le_exp`), so that `‖h‖ * exp(−c‖h‖²) ≤ max(1, 1/c)`. -/
theorem norm_mul_noiseDens_zero_le (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A 0 h ≤ D₀ := by
  classical
  obtain ⟨κ, c, cS, hκ, hc, hcS, hdecay⟩ := noiseDens_decay n S hS A hA
  refine ⟨cS * max 1 c⁻¹, mul_pos hcS (by positivity), ?_⟩
  intro h
  have hnorm0 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  -- the decay bound B.1 evaluated at `y = 0`
  have h0 : noiseDens n S hS A 0 h ≤ cS * Real.exp (-(c * ‖h‖ ^ 2)) := by
    have h2 := hdecay 0 h
    rwa [show (κ * (‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2)) = 0 from by simp, Real.exp_zero,
      mul_one] at h2
  rcases le_or_gt ‖h‖ 1 with h1 | h1
  · -- small case: `‖h‖ ≤ 1`, `exp(−c‖h‖²) ≤ 1`
    have hexpNonNeg : 0 ≤ c * ‖h‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    have he1 : Real.exp (-(c * ‖h‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hprod : ‖h‖ * Real.exp (-(c * ‖h‖ ^ 2)) ≤ 1 :=
      (mul_le_mul h1 he1 (Real.exp_nonneg _) zero_le_one).trans (by norm_num)
    calc
      ‖h‖ * noiseDens n S hS A 0 h ≤ ‖h‖ * (cS * Real.exp (-(c * ‖h‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left h0 hnorm0
      _ = cS * (‖h‖ * Real.exp (-(c * ‖h‖ ^ 2))) := by ring
      _ ≤ cS * max 1 c⁻¹ := mul_le_mul_of_nonneg_left (hprod.trans (le_max_left (1 : ℝ) c⁻¹)) hcS.le
  · -- large case: `‖h‖ ≥ 1`, `‖h‖ * exp(−c‖h‖²) ≤ 1/c`
    have hpos : 0 < c * ‖h‖ := mul_pos hc (zero_lt_one.trans h1)
    have hne : ‖h‖ ≠ 0 := ne_of_gt (zero_lt_one.trans h1)
    have h1le : (1 : ℝ) ≤ ‖h‖ := h1.le
    have hge : c * ‖h‖ ≤ c * ‖h‖ ^ 2 := by
      calc
        c * ‖h‖ = (c * ‖h‖) * 1 := by ring
        _ ≤ (c * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_left h1le (mul_nonneg hc.le hnorm0)
        _ = c * ‖h‖ ^ 2 := by ring
    have hexple : c * ‖h‖ ≤ Real.exp (c * ‖h‖ ^ 2) := by
      have h1' := Real.add_one_le_exp (c * ‖h‖)
      have h2' := Real.exp_monotone hge
      linarith
    have hle : Real.exp (-(c * ‖h‖ ^ 2)) ≤ (c * ‖h‖)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hexple
    calc
      ‖h‖ * noiseDens n S hS A 0 h ≤ ‖h‖ * (cS * Real.exp (-(c * ‖h‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left h0 hnorm0
      _ = cS * (‖h‖ * Real.exp (-(c * ‖h‖ ^ 2))) := by ring
      _ ≤ cS * (‖h‖ * (c * ‖h‖)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hnorm0) hcS.le
      _ = cS * c⁻¹ := by rw [_root_.mul_inv_rev, mul_inv_cancel_left₀ hne]
      _ ≤ cS * max 1 c⁻¹ := mul_le_mul_of_nonneg_left (le_max_right _ _) hcS.le

/-- Step B.2 of `plan_main_theorem.md` (second part): the posterior moment
`J(y) = ∫ h, (noiseDens n S hS A y h * f h) • h` is uniformly bounded on every ball
`‖y‖ ≤ r`, with a constant depending only on `n, S, A, f, r`. Via the translation
`h = h' + A⁻¹ y` (`integral_toLp_trans`), the triangle inequality, the `D₀`-bound of
`norm_mul_noiseDens_zero_le`, the pointwise Gaussian bound
`multivariateGaussianPDF_le_const` (so `noiseDens n S hS A 0 ≤ c₀`), and the translation
invariance `∫ f (toLp (c + x)) = ∫ f = 1`. -/
theorem posterior_moment_bound (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (r : ℝ) (_hr : 0 < r) :
    ∃ C : ℝ,
      ∀ y : EuclideanSpace ℝ (Fin n),
        ‖y‖ ≤ r →
          ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ ≤ C := by
  classical
  obtain ⟨D₀, _, hD₀⟩ := norm_mul_noiseDens_zero_le n S hS A hA
  -- `c₀`: the constant pointwise bound on the Gaussian pdf
  set c₀ : ℝ := ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSdetpos : 0 < S.det := hS.det_pos
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hSdetpos
  have hc₀pos : 0 < c₀ := by
    rw [hc₀def]; positivity
  have hnd0le : ∀ x : EuclideanSpace ℝ (Fin n), noiseDens n S hS A 0 x ≤ c₀ := by
    intro x
    simp only [noiseDens]
    exact
      multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 (WithLp.ofLp 0 - A.mulVec (x : Fin n → ℝ)))
  -- the operator-norm constant of `A⁻¹`
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A⁻¹ with hLdef
  set K : ℝ := ‖L‖ with hKdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hAYle :
    ∀ z : EuclideanSpace ℝ (Fin n),
      ‖(WithLp.toLp 2 (A⁻¹.mulVec (z : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ≤ K * ‖z‖ := by
    intro z
    have h2 := ContinuousLinearMap.le_opNorm L (WithLp.toLp 2 (z : Fin n → ℝ))
    have h3 :
      (WithLp.toLp 2 (A⁻¹.mulVec (z : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
        L (WithLp.toLp 2 (z : Fin n → ℝ)) := by
      apply WithLp.ofLp_injective
      show A⁻¹ *ᵥ (z : Fin n → ℝ) = A⁻¹ *ᵥ (z : Fin n → ℝ)
      rfl
    rw [← h3] at h2
    exact h2
  refine ⟨D₀ + K * r * c₀, ?_⟩
  intro y hy
  set c : Fin n → ℝ := A⁻¹.mulVec (y : Fin n → ℝ) with hc
  have hAc : A.mulVec c = (y : Fin n → ℝ) := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  set Cc : ℝ := ‖(WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n))‖ with hCc
  -- AES-strong measurability of the (vector-valued) translated integrand
  have hGm :
    MeasureTheory.AEStronglyMeasurable
      (fun w : EuclideanSpace ℝ (Fin n) => (noiseDens n S hS A y w * f w) • w) volume := by
    have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
      have hcomp :
        noiseDens n S hS A y =
          (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
            (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
        funext h
        exact noiseDens_eq n S hS A y h
      rw [hcomp]
      exact
        ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
            (by fun_prop :
              Measurable
                (fun h : EuclideanSpace ℝ (Fin n) =>
                  y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
    exact
      ((hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).smul
          (measurable_id.aemeasurable)).aestronglyMeasurable
  -- the translated mass of `f`
  have hTint :
    ∫ x : EuclideanSpace ℝ (Fin n), f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) ∂volume = 1 := by
    rw [integral_toLp_trans n c f ((integrable_of_isPdf hf).aestronglyMeasurable)]
    exact hf.2
  have hTfint :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) volume :=
    MeasureTheory.Integrable.of_integral_ne_zero
      (by
        rw [hTint]; exact one_ne_zero)
  have hKint :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => (D₀ + Cc * c₀) * f (WithLp.toLp 2 (c + (x : Fin n → ℝ))))
      volume :=
    MeasureTheory.Integrable.smul (D₀ + Cc * c₀) hTfint
  -- pointwise bound on the norm of the translated integrand
  have hpw :
    ∀ x : EuclideanSpace ℝ (Fin n),
      ‖(noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
            (WithLp.toLp 2 (c + (x : Fin n → ℝ)))‖ ≤
        (D₀ + Cc * c₀) * f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) := by
    intro x
    have hsnd : 0 ≤ noiseDens n S hS A 0 x := by
      simp only [noiseDens]
      rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 (WithLp.ofLp 0 - A.mulVec (x : Fin n → ℝ)))]
      positivity
    have hfT : 0 ≤ f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) := hf.1 _
    have hnormT :
      ‖(WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x‖ + Cc := by
      have hnormEq :
        (WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n)) =
          (WithLp.toLp 2 (x : Fin n → ℝ)) + (WithLp.toLp 2 c : EuclideanSpace ℝ (Fin n)) := by
        rw [WithLp.toLp_add, add_comm]
      rw [hnormEq]
      exact le_trans (norm_add_le _ _) (add_le_add (le_refl _) (le_refl Cc))
    have hsplit1 :
      ‖(noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
            (WithLp.toLp 2 (c + (x : Fin n → ℝ)))‖ =
        (noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) *
          ‖(WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsnd hfT)]
    calc
      ‖(noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
              (WithLp.toLp 2 (c + (x : Fin n → ℝ)))‖ =
          (noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) *
            ‖(WithLp.toLp 2 (c + (x : Fin n → ℝ)) : EuclideanSpace ℝ (Fin n))‖ :=
        hsplit1
      _ ≤ (noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) * (‖x‖ + Cc) :=
        mul_le_mul_of_nonneg_left hnormT (mul_nonneg hsnd hfT)
      _ =
          (‖x‖ * noiseDens n S hS A 0 x + Cc * noiseDens n S hS A 0 x) *
            f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) :=
        by ring
      _ ≤ (D₀ + Cc * c₀) * f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ hfT
        have h1 : ‖x‖ * noiseDens n S hS A 0 x ≤ D₀ := hD₀ x
        have h2 : Cc * noiseDens n S hS A 0 x ≤ Cc * c₀ :=
          mul_le_mul_of_nonneg_left (hnd0le x) (norm_nonneg _)
        linarith
  calc
    ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ =
        ‖∫ x : EuclideanSpace ℝ (Fin n),
            (noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) *
                f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
              (WithLp.toLp 2 (c + (x : Fin n → ℝ))) ∂volume‖ :=
      congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖)
        (integral_toLp_trans n c
            (fun w : EuclideanSpace ℝ (Fin n) => (noiseDens n S hS A y w * f w) • w) hGm).symm
    _ =
        ‖∫ x : EuclideanSpace ℝ (Fin n),
            (noiseDens n S hS A 0 x * f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
              (WithLp.toLp 2 (c + (x : Fin n → ℝ))) ∂volume‖ :=
      by
      refine congrArg (fun w : EuclideanSpace ℝ (Fin n) => ‖w‖) ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show
        (noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) *
              f (WithLp.toLp 2 (c + (x : Fin n → ℝ)))) •
            (WithLp.toLp 2 (c + (x : Fin n → ℝ))) =
          _
      have hndEq :
        noiseDens n S hS A y (WithLp.toLp 2 (c + (x : Fin n → ℝ))) = noiseDens n S hS A 0 x := by
        simp only [noiseDens]
        rw [Matrix.mulVec_add, hAc, WithLp.ofLp_zero]
        rw [show ((y : Fin n → ℝ) - (y + A.mulVec (x : Fin n → ℝ))) = (0 - A.mulVec (x : Fin n → ℝ))
            from by ring]
      rw [hndEq]
    _ ≤
        ∫ x : EuclideanSpace ℝ (Fin n),
          (D₀ + Cc * c₀) * f (WithLp.toLp 2 (c + (x : Fin n → ℝ))) ∂volume :=
      MeasureTheory.norm_integral_le_of_norm_le hKint (Filter.Eventually.of_forall hpw)
    _ = (D₀ + Cc * c₀) * 1 := by rw [MeasureTheory.integral_const_mul, hTint]
    _ = D₀ + Cc * c₀ := by ring
    _ ≤ D₀ + K * r * c₀ := by
      refine add_le_add_right ?_ _
      exact
        mul_le_mul_of_nonneg_right ((hAYle y).trans (mul_le_mul_of_nonneg_left hy hK0)) hc₀pos.le

/-- Step B.3 of `plan_main_theorem.md`: the marginal density `f_y(y) = ∫ f_n(y − A h) f(h) dh`
is strictly positive for every `y` and every pdf `f`. The integrand is nonnegative
(pointwise positivity of the Gaussian pdf); if the integral vanished, the integrand would be
zero a.e., and since `f_n > 0` everywhere this forces `f = 0` a.e., contradicting
`∫ f = 1`. -/
theorem fy_pos (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (A : Matrix (Fin n) (Fin n) ℝ)
    (_hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin n)) : 0 < fyPDF n S hS A f y := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  -- the integrand is nonnegative
  have hposintegrand : ∀ h : EuclideanSpace ℝ (Fin n), 0 ≤ noiseDens n S hS A y h * f h := by
    intro h
    refine mul_nonneg ?_ (hf.1 h)
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
  -- pointwise strict positivity of `noiseDens`
  have hndpos : ∀ h : EuclideanSpace ℝ (Fin n), 0 < noiseDens n S hS A y h := by
    intro h
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    exact mul_pos (inv_pos.mpr (mul_pos h2pi hSqrtpos)) (Real.exp_pos _)
  -- integrability of the integrand, via the pointwise bound `noiseDens ≤ c₀`
  have hndle : ∀ h : EuclideanSpace ℝ (Fin n), noiseDens n S hS A y h ≤ c₀ := by
    intro h
    simp only [noiseDens]
    exact
      multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
  have hinteg : MeasureTheory.Integrable (fun h => noiseDens n S hS A y h * f h) volume := by
    have hprodM :
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDens n S hS A y h * f h) volume := by
      have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
        have hcomp :
          noiseDens n S hS A y =
            (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
              (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
          funext h
          exact noiseDens_eq n S hS A y h
        rw [hcomp]
        exact
          ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
              (by fun_prop :
                Measurable
                  (fun h : EuclideanSpace ℝ (Fin n) =>
                    y +
                      (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
      exact
        (hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    have hfint : MeasureTheory.Integrable (fun h => c₀ * f h) volume :=
      MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf hf)
    refine MeasureTheory.Integrable.mono' hfint hprodM (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_eq_self.mpr (hposintegrand h)]
    exact mul_le_mul_of_nonneg_right (hndle h) (hf.1 h)
  have hnonneg : 0 ≤ fyPDF n S hS A f y := by
    rw [fyPDF]
    exact MeasureTheory.integral_nonneg hposintegrand
  by_contra hcon
  have hle : fyPDF n S hS A f y ≤ 0 := le_of_not_gt hcon
  have hzero : fyPDF n S hS A f y = 0 := le_antisymm hle hnonneg
  have haezero : (fun h => noiseDens n S hS A y h * f h) =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hposintegrand)
          hinteg).mp
      hzero
  -- therefore `f = 0` a.e., contradicting `∫ f = 1`
  have hfeq : f =ᵐ[volume] 0 := by
    filter_upwards [haezero] with h hval
    rcases mul_eq_zero.mp hval with h0' | h0'
    · exact absurd h0' (ne_of_gt (hndpos h))
    · exact h0'
  have hintf : ∫ x, f x ∂volume = 0 := by
    rw [MeasureTheory.integral_congr_ae hfeq]
    simp
  rw [hf.2] at hintf
  exact one_ne_zero hintf

/-- Continuity of the Gaussian pdf (used by Step B.4 `fy_cont`). -/
theorem multivariateGaussianPDF_continuous (n : ℕ) (m : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ)
    (hC : Cov.PosDef) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => multivariateGaussianPDF n m Cov hC x) := by
  simp only [multivariateGaussianPDF]
  fun_prop

/-- Step B.4 of `plan_main_theorem.md`: for a continuous pdf `f` the marginal density
`f_y = ∫ f_n(y − A h) f(h) dh` is continuous in `y`, by dominated convergence in the
parameter (the integrand is dominated by `c₀ · f` and continuous in `y` for each `h`). -/
theorem fy_cont (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (_hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (_hfc : Continuous f) : Continuous (fyPDF n S hS A f) := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  -- measurability of the parameter-dependent integrand
  have hFm :
    ∀ y : EuclideanSpace ℝ (Fin n),
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDens n S hS A y h * f h) volume := by
    intro y
    have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
      have hcomp :
        noiseDens n S hS A y =
          (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
            (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
        funext h
        exact noiseDens_eq n S hS A y h
      rw [hcomp]
      exact
        ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
            (by fun_prop :
              Measurable
                (fun h : EuclideanSpace ℝ (Fin n) =>
                  y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
    exact
      (hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  -- the domination `‖noiseDens(y,h) · f h‖ ≤ c₀ · f h`
  have hbnd :
    ∀ (y : EuclideanSpace ℝ (Fin n)) (h : EuclideanSpace ℝ (Fin n)),
      ‖noiseDens n S hS A y h * f h‖ ≤ c₀ * f h := by
    intro y h
    have hsnd : 0 ≤ noiseDens n S hS A y h := by
      simp only [noiseDens]
      rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
    have hndle : noiseDens n S hS A y h ≤ c₀ := by
      simp only [noiseDens]
      exact
        multivariateGaussianPDF_le_const n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
    rw [Real.norm_eq_abs, abs_eq_self.mpr (mul_nonneg hsnd (hf.1 h))]
    exact mul_le_mul_of_nonneg_right hndle (hf.1 h)
  have hbint : MeasureTheory.Integrable (fun h => c₀ * f h) volume :=
    MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf hf)
  -- continuity in `y` for every fixed `h`
  have hcont :
    ∀ h : EuclideanSpace ℝ (Fin n), Continuous (fun y => noiseDens n S hS A y h * f h) := by
    intro h
    have hndc : Continuous (fun y => noiseDens n S hS A y h) := by
      have hcomp :
        (fun y : EuclideanSpace ℝ (Fin n) => noiseDens n S hS A y h) =
          (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
            (fun y => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
        funext y
        exact noiseDens_eq n S hS A y h
      rw [hcomp]
      exact
        (multivariateGaussianPDF_continuous n (0 : Fin n → ℝ) S hS).comp
          (by fun_prop :
            Continuous
              (fun y : EuclideanSpace ℝ (Fin n) =>
                y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))
    exact hndc.mul continuous_const
  unfold fyPDF
  refine continuous_iff_continuousAt.mpr fun y => ?_
  refine
    MeasureTheory.continuousAt_of_dominated (x₀ := y) (bound := fun h => c₀ * f h)
      (Filter.Eventually.of_forall hFm)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (hbnd x)) hbint
      (Filter.Eventually.of_forall fun h => (hcont h).continuousAt)

/-- Step B.5 of `plan_main_theorem.md`: on every ball `‖y‖ ≤ r` the marginal density `f_y`
admits a positive lower bound `m` (its minimum over the compact ball, by B.3 `fy_pos` and
B.4 `fy_cont`). -/
theorem fy_min_pos (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (hfc : Continuous f) (r : ℝ) (hr : 0 < r) :
    ∃ m : ℝ, 0 < m ∧ ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ r → m ≤ fyPDF n S hS A f y := by
  classical
  have hcomp : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) :=
    ProperSpace.isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr.le⟩
  obtain ⟨y₀, hy₀mem, hy₀min⟩ :=
    hcomp.exists_isMinOn hne ((fy_cont n S hS A hA f hf hfc).continuousOn)
  have hpos : 0 < fyPDF n S hS A f y₀ := fy_pos n S hS A hA f hf y₀
  refine ⟨fyPDF n S hS A f y₀, hpos, ?_⟩
  intro y hy
  have hmem : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hy
  exact isMinOn_iff.mp hy₀min y hmem

/-- Step B.6 of `plan_main_theorem.md`: for `K` large enough, the marginal density of the
approximating model admits the uniform lower bound `m / 2` on every ball `‖y‖ ≤ r`, where
`m` is the lower bound of `f_y` (B.5) and the convergence of `f_y^{(K)}` to `f_y` is
`uniform_convergence_fy` at `ε = m / 2`. -/
theorem fyK_lower_bound (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (hfhcont : Continuous fh) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K)) (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (r : ℝ) (hr : 0 < r) :
    ∃ M₁ : ℝ,
      0 < M₁ ∧
        ∃ N₁ : ℕ,
          ∀ K ≥ N₁, ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ≤ r → M₁ ≤ fyPDF n S hS A (fhK K) y := by
  classical
  obtain ⟨m, hm, hmin⟩ := fy_min_pos n S hS A hA fh hfhpdf hfhcont r hr
  obtain ⟨N₁, hN₁⟩ :=
    uniform_convergence_fy n S hS A hA fh (integrable_of_isPdf hfhpdf) fhK
      (fun K => integrable_of_isPdf (hfhKpdf K)) hconv (m / 2) (by linarith)
  refine ⟨m / 2, by linarith, N₁, fun K hK y hy => ?_⟩
  have hΔ := hN₁ K hK y
  have h2 :
    fyPDF n S hS A fh y - |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| ≤
      fyPDF n S hS A (fhK K) y := by
    have hw :
      fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y ≤
        |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| :=
      le_abs_self _
    linarith
  have h3 : m - m / 2 ≤ fyPDF n S hS A fh y - |fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y| := by
    have h4 : m ≤ fyPDF n S hS A fh y := hmin y hy
    linarith
  linarith

/-- Step B.2 of `plan_main_theorem.md` (generalization of `norm_mul_noiseDens_zero_le`):
for every `y` the function `h ↦ ‖h‖ · f_n(y − A h)` is bounded by a positive constant
(depending on `y` through `exp(κ‖y‖²)`). -/
theorem norm_mul_noiseDens_le (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (y : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ≤ C := by
  classical
  obtain ⟨κ, c, cS, _, hc, hcS, hdecay⟩ := noiseDens_decay n S hS A hA
  have hfac : 0 ≤ Real.exp (κ * ‖y‖ ^ 2) := Real.exp_nonneg _
  refine
    ⟨cS * Real.exp (κ * ‖y‖ ^ 2) * max 1 c⁻¹,
      mul_pos (mul_pos hcS (Real.exp_pos _)) (by positivity), ?_⟩
  intro h
  have hnorm0 : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
  rcases le_or_gt ‖h‖ 1 with h1 | h1
  · -- small case: `‖h‖ ≤ 1`
    have hexpNonNeg : 0 ≤ c * ‖h‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
    have he1 : Real.exp (-(c * ‖h‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hprod : ‖h‖ * Real.exp (-(c * ‖h‖ ^ 2)) ≤ 1 :=
      (mul_le_mul h1 he1 (Real.exp_nonneg _) zero_le_one).trans (by norm_num)
    calc
      ‖h‖ * noiseDens n S hS A y h ≤
          ‖h‖ * (cS * Real.exp (κ * ‖y‖ ^ 2) * Real.exp (-(c * ‖h‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (hdecay y h) hnorm0
      _ = cS * Real.exp (κ * ‖y‖ ^ 2) * (‖h‖ * Real.exp (-(c * ‖h‖ ^ 2))) := by ring
      _ ≤ cS * Real.exp (κ * ‖y‖ ^ 2) * max 1 c⁻¹ :=
        mul_le_mul_of_nonneg_left (hprod.trans (le_max_left (1 : ℝ) c⁻¹)) (mul_nonneg hcS.le hfac)
  · -- large case: `‖h‖ ≥ 1`
    have hpos : 0 < c * ‖h‖ := mul_pos hc (zero_lt_one.trans h1)
    have hne : ‖h‖ ≠ 0 := ne_of_gt (zero_lt_one.trans h1)
    have h1le : (1 : ℝ) ≤ ‖h‖ := h1.le
    have hge : c * ‖h‖ ≤ c * ‖h‖ ^ 2 := by
      calc
        c * ‖h‖ = (c * ‖h‖) * 1 := by ring
        _ ≤ (c * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_left h1le (mul_nonneg hc.le hnorm0)
        _ = c * ‖h‖ ^ 2 := by ring
    have hexple : c * ‖h‖ ≤ Real.exp (c * ‖h‖ ^ 2) := by
      have ha := Real.add_one_le_exp (c * ‖h‖)
      have hb := Real.exp_monotone hge
      linarith
    have hle : Real.exp (-(c * ‖h‖ ^ 2)) ≤ (c * ‖h‖)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) hpos).mpr hexple
    calc
      ‖h‖ * noiseDens n S hS A y h ≤
          ‖h‖ * (cS * Real.exp (κ * ‖y‖ ^ 2) * Real.exp (-(c * ‖h‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (hdecay y h) hnorm0
      _ = cS * Real.exp (κ * ‖y‖ ^ 2) * (‖h‖ * Real.exp (-(c * ‖h‖ ^ 2))) := by ring
      _ ≤ cS * Real.exp (κ * ‖y‖ ^ 2) * (‖h‖ * (c * ‖h‖)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hnorm0) (mul_nonneg hcS.le hfac)
      _ = cS * Real.exp (κ * ‖y‖ ^ 2) * c⁻¹ := by rw [_root_.mul_inv_rev, mul_inv_cancel_left₀ hne]
      _ ≤ cS * Real.exp (κ * ‖y‖ ^ 2) * max 1 c⁻¹ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hcS.le hfac)

/-- Step B.2 of `plan_main_theorem.md` (last part): the `cme` integrand
`fun h => ((noiseDens n S hS A y h * f h) / f_y(y)) • h` is Bochner integrable for every
pdf `f` and every `y` (domination by `(C(y) / f_y(y)) • f`, using B.3 `fy_pos` and the
per-`y` bound `norm_mul_noiseDens_le`). -/
theorem cme_integrable (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (y : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable
      (fun h : EuclideanSpace ℝ (Fin n) =>
        ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h)
      volume := by
  classical
  obtain ⟨C, _, hC⟩ := norm_mul_noiseDens_le n S hS A hA y
  have hfypos : 0 < fyPDF n S hS A f y := fy_pos n S hS A hA f hf y
  -- measurability of the integrand
  have hM :
    MeasureTheory.AEStronglyMeasurable
      (fun h => ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h) volume := by
    have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
      have hcomp :
        noiseDens n S hS A y =
          (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
            (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
        funext h
        exact noiseDens_eq n S hS A y h
      rw [hcomp]
      exact
        ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
            (by fun_prop :
              Measurable
                (fun h : EuclideanSpace ℝ (Fin n) =>
                  y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
    have hprod : AEMeasurable (fun h => noiseDens n S hS A y h * f h) volume :=
      hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)
    have hsM :
      AEMeasurable (fun h => (noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) volume := by
      have h1 :
        AEMeasurable (fun h => (1 / fyPDF n S hS A f y) * (noiseDens n S hS A y h * f h)) volume :=
        hprod.const_mul (1 / fyPDF n S hS A f y)
      have h2 :
        (fun h => (noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) = fun h =>
          (1 / fyPDF n S hS A f y) * (noiseDens n S hS A y h * f h) := by
        funext h
        ring
      rw [h2]
      exact h1
    exact (hsM.smul (measurable_id.aemeasurable)).aestronglyMeasurable
  -- domination by `(C / f_y) • f`
  have hgint : MeasureTheory.Integrable (fun h => (C / fyPDF n S hS A f y) * f h) volume :=
    MeasureTheory.Integrable.smul (C / fyPDF n S hS A f y) (integrable_of_isPdf hf)
  refine MeasureTheory.Integrable.mono' hgint hM (Filter.Eventually.of_forall fun h => ?_)
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  have hsnd : 0 ≤ noiseDens n S hS A y h := by
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
  rw [norm_smul, Real.norm_eq_abs,
    abs_eq_self.mpr (div_nonneg (mul_nonneg hsnd (hf.1 h)) hfypos.le)]
  have h1 :
    (noiseDens n S hS A y h * f h) / fyPDF n S hS A f y * ‖h‖ =
      (‖h‖ * noiseDens n S hS A y h) * (f h / fyPDF n S hS A f y) := by
    ring
  rw [h1]
  have h2 : (C / fyPDF n S hS A f y) * f h = C * (f h / fyPDF n S hS A f y) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right (hC h) (div_nonneg (hf.1 h) hfypos.le)

/-- Step B.2 auxiliary: the posterior-moment integrand `fun h => (f_n(y − A h) f(h)) • h`
is Bochner integrable (domination by `C(y) · f`, using `norm_mul_noiseDens_le`). -/
theorem posterior_integrable (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (y : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable (fun h => (noiseDens n S hS A y h * f h) • h) volume := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  obtain ⟨C, _, hC⟩ := norm_mul_noiseDens_le n S hS A hA y
  have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
    have hcomp :
      noiseDens n S hS A y =
        (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
          (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
      funext h
      exact noiseDens_eq n S hS A y h
    rw [hcomp]
    exact
      ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
          (by fun_prop :
            Measurable
              (fun h : EuclideanSpace ℝ (Fin n) =>
                y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
  have hprodM : MeasureTheory.AEStronglyMeasurable (fun h => noiseDens n S hS A y h * f h) volume :=
    (hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hvecM :
    MeasureTheory.AEStronglyMeasurable (fun h => (noiseDens n S hS A y h * f h) • h) volume :=
    hprodM.smul aestronglyMeasurable_id
  have hgint : MeasureTheory.Integrable (fun h => C * f h) volume :=
    MeasureTheory.Integrable.smul C (integrable_of_isPdf hf)
  refine MeasureTheory.Integrable.mono' hgint hvecM (Filter.Eventually.of_forall fun h => ?_)
  have hsnd : 0 ≤ noiseDens n S hS A y h := by
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
  calc
    ‖(noiseDens n S hS A y h * f h) • h‖ = ‖noiseDens n S hS A y h * f h‖ * ‖h‖ := by rw [norm_smul]
    _ = noiseDens n S hS A y h * f h * ‖h‖ := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_eq_self.mpr hsnd,
        abs_eq_self.mpr (hf.1 h)]
    _ = (‖h‖ * noiseDens n S hS A y h) * f h := by ring
    _ ≤ C * f h := mul_le_mul_of_nonneg_right (hC h) (hf.1 h)

/-- Step B.2 auxiliary: the integrand `fun h => (f_n(y − A h) (fK − f)(h)) • h` is Bochner
integrable (domination by `C(y) · (fK + f)`, using `norm_mul_noiseDens_le` and the triangle
bound `|fK − f| ≤ fK + f` for nonnegative pdfs). -/
theorem posterior_diff_integrable (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK)
    (y : EuclideanSpace ℝ (Fin n)) :
    MeasureTheory.Integrable (fun h => (noiseDens n S hS A y h * (fK h - f h)) • h) volume := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  obtain ⟨C, _, hC⟩ := norm_mul_noiseDens_le n S hS A hA y
  have hndM : AEMeasurable (noiseDens n S hS A y) volume := by
    have hcomp :
      noiseDens n S hS A y =
        (fun x => multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x) ∘
          (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h) := by
      funext h
      exact noiseDens_eq n S hS A y h
    rw [hcomp]
    exact
      ((measurable_multivariateGaussianPDF n (0 : Fin n → ℝ) S hS).comp
          (by fun_prop :
            Measurable
              (fun h : EuclideanSpace ℝ (Fin n) =>
                y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) ((-1 : ℝ) • A)) h))).aemeasurable
  have hdiffM : AEMeasurable (fun h => noiseDens n S hS A y h * (fK h - f h)) volume := by
    have h1 :
      (fun h => noiseDens n S hS A y h * (fK h - f h)) =
        (fun h => noiseDens n S hS A y h * fK h) - (fun h => noiseDens n S hS A y h * f h) := by
      funext h
      rw [Pi.sub_apply, mul_sub]
    rw [h1]
    exact
      (hndM.mul ((integrable_of_isPdf hfK).aestronglyMeasurable.aemeasurable)).sub
        (hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable))
  have hvecM :
    MeasureTheory.AEStronglyMeasurable (fun h => (noiseDens n S hS A y h * (fK h - f h)) • h)
      volume :=
    (hdiffM.smul (measurable_id.aemeasurable)).aestronglyMeasurable
  have hgint : MeasureTheory.Integrable (fun h => C * (fK h + f h)) volume :=
    (MeasureTheory.Integrable.smul C ((integrable_of_isPdf hfK).add (integrable_of_isPdf hf))).congr
      (Filter.Eventually.of_forall fun h => by simp)
  refine MeasureTheory.Integrable.mono' hgint hvecM (Filter.Eventually.of_forall fun h => ?_)
  have hsnd : 0 ≤ noiseDens n S hS A y h := by
    simp only [noiseDens]
    rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
        (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
  have hFK : (0 : ℝ) ≤ fK h := hfK.1 h
  have hF : (0 : ℝ) ≤ f h := hf.1 h
  have hsub : |fK h - f h| ≤ fK h + f h := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  calc
    ‖(noiseDens n S hS A y h * (fK h - f h)) • h‖ = ‖noiseDens n S hS A y h * (fK h - f h)‖ * ‖h‖ :=
      by rw [norm_smul]
    _ = noiseDens n S hS A y h * |fK h - f h| * ‖h‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_eq_self.mpr hsnd, Real.norm_eq_abs]
    _ ≤ noiseDens n S hS A y h * (fK h + f h) * ‖h‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub hsnd) (norm_nonneg _)
    _ = (‖h‖ * noiseDens n S hS A y h) * (fK h + f h) := by ring
    _ ≤ C * (fK h + f h) := mul_le_mul_of_nonneg_right (hC h) (add_nonneg (hfK.1 h) (hf.1 h))

/-- Step C.1 of `plan_main_theorem.md`: the two-term decomposition of the `cme` difference:
for pdfs `f`, `fK` and `f_y^{(K)}(y) ≠ 0 ≠ f_y(y)`,

`cme(fK) − cme(f) = (1/f_y^{(K)}(y)) • ∫ h, (f_n(y−Ah) (fK − f)(h)) • h`
`  + ((f_y(y) − f_y^{(K)}(y))/(f_y^{(K)}(y) f_y(y))) • ∫ h, (f_n(y−Ah) f(h)) • h`. -/
theorem cme_decomp (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK)
    (y : EuclideanSpace ℝ (Fin n)) (hfyK : fyPDF n S hS A fK y ≠ 0) (hfy : fyPDF n S hS A f y ≠ 0) :
    cme n S hS A fK y - cme n S hS A f y =
      (1 / fyPDF n S hS A fK y) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * (fK h - f h)) • h ∂volume +
        ((fyPDF n S hS A f y - fyPDF n S hS A fK y) / (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume := by
  classical
  obtain ⟨C, _, hC⟩ := norm_mul_noiseDens_le n S hS A hA y
  -- integrability of the two `cme` integrands
  have hI1 :
    MeasureTheory.Integrable (fun h => ((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h)
      volume :=
    cme_integrable n S hS A hA fK hfK y
  have hI2 :
    MeasureTheory.Integrable (fun h => ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h)
      volume :=
    cme_integrable n S hS A hA f hf y
  -- integrability of the two summand integrands
  have hIa := posterior_diff_integrable n S hS A hA f hf fK hfK y
  have hIb := posterior_integrable n S hS A hA f hf y
  -- the difference-of-integrals identity (`MeasureTheory.integral_sub`)
  have hstep1 :
    ∫ h : EuclideanSpace ℝ (Fin n),
        (((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h -
          ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h) ∂volume =
      ∫ h : EuclideanSpace ℝ (Fin n),
          ((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h ∂volume -
        ∫ h : EuclideanSpace ℝ (Fin n),
          ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h ∂volume :=
    MeasureTheory.integral_sub hI1 hI2
  calc
    cme n S hS A fK y - cme n S hS A f y =
        ∫ h : EuclideanSpace ℝ (Fin n),
            ((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h ∂volume -
          ∫ h : EuclideanSpace ℝ (Fin n),
            ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h ∂volume :=
      by
      unfold cme
      rfl
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          (((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h -
            ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h) ∂volume :=
      hstep1.symm
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          ((1 / fyPDF n S hS A fK y) • ((noiseDens n S hS A y h * (fK h - f h)) • h) +
            ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
                (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
              ((noiseDens n S hS A y h * f h) • h)) ∂volume :=
      by
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      show
        ((noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y) • h -
            ((noiseDens n S hS A y h * f h) / fyPDF n S hS A f y) • h =
          (1 / fyPDF n S hS A fK y) • ((noiseDens n S hS A y h * (fK h - f h)) • h) +
            ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
                (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
              ((noiseDens n S hS A y h * f h) • h)
      have hscal :
        (noiseDens n S hS A y h * fK h) / fyPDF n S hS A fK y -
            (noiseDens n S hS A y h * f h) / fyPDF n S hS A f y =
          (1 / fyPDF n S hS A fK y) * (noiseDens n S hS A y h * (fK h - f h)) +
            ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
                (fyPDF n S hS A fK y * fyPDF n S hS A f y)) *
              (noiseDens n S hS A y h * f h) := by
        field_simp
        ring
      rw [← sub_smul, hscal, add_smul, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul]
    _ =
        (1 / fyPDF n S hS A fK y) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * (fK h - f h)) • h ∂volume +
          ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
              (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume :=
      by
      have hIa' :
        MeasureTheory.Integrable
          (fun h => (1 / fyPDF n S hS A fK y) • ((noiseDens n S hS A y h * (fK h - f h)) • h))
          volume :=
        (MeasureTheory.Integrable.smul (1 / fyPDF n S hS A fK y) hIa).congr
          (Filter.Eventually.of_forall fun h => by simp)
      have hIb' :
        MeasureTheory.Integrable
          (fun h =>
            ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
                (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
              ((noiseDens n S hS A y h * f h) • h))
          volume :=
        (MeasureTheory.Integrable.smul
              ((fyPDF n S hS A f y - fyPDF n S hS A fK y) /
                (fyPDF n S hS A fK y * fyPDF n S hS A f y))
              hIb).congr
          (Filter.Eventually.of_forall fun h => by simp)
      rw [integral_add hIa' hIb', integral_smul _ _, integral_smul _ _]

/-- Step C.2 of `plan_main_theorem.md` (first rate): if `f_y^{(K)}(y) ≠ 0` and the sup-norm
bound `|f_h^{(K)} − f_h| ≤ ε` holds everywhere, then the first summand of `cme_decomp` is
bounded by `(1/f_y^{(K)}(y)) · ε · ∫ ‖h‖ f_n(y − A h) dh` (the last factor is bounded
uniformly on balls by Step A.1 `noiseDens_moment_uniform`). -/
theorem cme_rate_T1 (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK)
    (y : EuclideanSpace ℝ (Fin n)) (_hfyK : fyPDF n S hS A fK y ≠ 0) (ε : ℝ) (_hε : 0 < ε)
    (hδ : ∀ x, |fK x - f x| ≤ ε) :
    ‖(1 / fyPDF n S hS A fK y) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * (fK h - f h)) • h ∂volume‖ ≤
      (1 / fyPDF n S hS A fK y) * ε *
        ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume := by
  classical
  have hIa := posterior_diff_integrable n S hS A hA f hf fK hfK y
  have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  have hfyKpos : 0 < fyPDF n S hS A fK y := fy_pos n S hS A hA fK hfK y
  have hscal : 0 ≤ 1 / fyPDF n S hS A fK y := le_of_lt (div_pos one_pos hfyKpos)
  have hint : MeasureTheory.Integrable (fun h => ε * (‖h‖ * noiseDens n S hS A y h)) volume := by
    have h2 : MeasureTheory.Integrable (fun h => ‖h‖ * noiseDens n S hS A y h) volume := by
      simpa only [noiseDens] using integral_gaussian_bounded n S hS A hA y
    exact (MeasureTheory.Integrable.smul ε h2).congr (Filter.Eventually.of_forall fun h => by simp)
  have hpt :
    ∀ h : EuclideanSpace ℝ (Fin n),
      ‖(noiseDens n S hS A y h * (fK h - f h)) • h‖ ≤ ε * (‖h‖ * noiseDens n S hS A y h) := by
    intro h
    have hsnd : 0 ≤ noiseDens n S hS A y h := by
      simp only [noiseDens]
      rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
          (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le)) (Real.exp_nonneg _)
    calc
      ‖(noiseDens n S hS A y h * (fK h - f h)) • h‖ =
          ‖noiseDens n S hS A y h * (fK h - f h)‖ * ‖h‖ :=
        by rw [norm_smul]
      _ = noiseDens n S hS A y h * |fK h - f h| * ‖h‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_eq_self.mpr hsnd, Real.norm_eq_abs]
      _ ≤ noiseDens n S hS A y h * ε * ‖h‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hδ h) hsnd) (norm_nonneg _)
      _ = ε * (‖h‖ * noiseDens n S hS A y h) := by ring
  calc
    ‖(1 / fyPDF n S hS A fK y) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * (fK h - f h)) • h ∂volume‖ =
        (1 / fyPDF n S hS A fK y) *
          ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * (fK h - f h)) • h ∂volume‖ :=
      by rw [norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hscal]
    _ ≤
        (1 / fyPDF n S hS A fK y) *
          ∫ h : EuclideanSpace ℝ (Fin n), ‖(noiseDens n S hS A y h * (fK h - f h)) • h‖ ∂volume :=
      mul_le_mul_of_nonneg_left
        (norm_integral_le_integral_norm (fun h => (noiseDens n S hS A y h * (fK h - f h)) • h))
        hscal
    _ ≤
        (1 / fyPDF n S hS A fK y) *
          (ε * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume) :=
      by
      refine mul_le_mul_of_nonneg_left ?_ hscal
      refine
        le_trans
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => norm_nonneg _) hint
            (Filter.Eventually.of_forall hpt))
          ?_
      rw [integral_const_mul]
    _ =
        (1 / fyPDF n S hS A fK y) * ε *
          ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume :=
      by ring

/-- Step C.2 of `plan_main_theorem.md` (second rate): if `f_y^{(K)}(y) ≠ 0` and
`|f_y(y) − f_y^{(K)}(y)| ≤ ε` then the second summand of `cme_decomp` is bounded by
`(ε/(f_y^{(K)}(y) f_y(y))) · ‖J(y)‖` (Step D bounds `‖J(y)‖` via
`posterior_moment_bound`). -/
theorem cme_rate_T2 (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsPdf f) (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK)
    (y : EuclideanSpace ℝ (Fin n)) (_hfyK : fyPDF n S hS A fK y ≠ 0) (ε : ℝ)
    (hδ : |fyPDF n S hS A f y - fyPDF n S hS A fK y| ≤ ε) :
    ‖((fyPDF n S hS A f y - fyPDF n S hS A fK y) / (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ ≤
      (ε / (fyPDF n S hS A fK y * fyPDF n S hS A f y)) *
        ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ := by
  classical
  have hfyKpos : 0 < fyPDF n S hS A fK y := fy_pos n S hS A hA fK hfK y
  have hfypos : 0 < fyPDF n S hS A f y := fy_pos n S hS A hA f hf y
  have hpos : 0 < fyPDF n S hS A fK y * fyPDF n S hS A f y := mul_pos hfyKpos hfypos
  calc
    ‖((fyPDF n S hS A f y - fyPDF n S hS A fK y) / (fyPDF n S hS A fK y * fyPDF n S hS A f y)) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ =
        |fyPDF n S hS A f y - fyPDF n S hS A fK y| / (fyPDF n S hS A fK y * fyPDF n S hS A f y) *
          ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ :=
      by rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    _ ≤
        ε / (fyPDF n S hS A fK y * fyPDF n S hS A f y) *
          ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * f h) • h ∂volume‖ :=
      by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [div_le_iff₀ hpos, div_mul_cancel₀ _ hpos.ne']
      exact hδ

/-
Take a look at `cme_uniform_balls_eps` for the eps-delta formulation of locally uniform convergence.
-/
public theorem main_theorem
    -- Let n be a natural number.
    (n : ℕ)
    -- Let S be an n-by-n matrix.
    (S : Matrix (Fin n) (Fin n) ℝ)
    -- Let S be positive definite. (S is the noise covariance matrix.)
    (hS : S.PosDef)
    -- Let A be an n-by-n matrix.
    (A : Matrix (Fin n) (Fin n) ℝ)
    -- Let A be invertible.
    (hA : IsUnit A.det)
    -- Let fh be a function from R^n to R.
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fh be a PDF.
    (hfhpdf : IsPdf fh)
    -- Let fh be continuous.
    (hfhcont : Continuous fh)
    -- For every K, let fhK be a function from R^n to R.
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    -- For every K, let fhK be a PDF.
    (hfhKpdf : ∀ K, IsPdf (fhK K))
    -- For every K, let fhK be continuous.
    (_hfhKcont : ∀ K, Continuous (fhK K))
    -- Let fhK converge uniformly to fh.
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε) :
    -- Then we have locally uniform convergence:
    -- For every radius r > 0,
    ∀ r : ℝ,
      0 < r →
        Tendsto
          (fun K =>
            -- the supremum over the closed ball around 0 with radius r
            ⨆ y ∈ Metric.closedBall 0 r,
              -- of the norm of the CME difference
              ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖)
          -- tends to 0 as K → ∞.
          atTop (nhds 0) := by
  classical
  intro r hr
  -- the constants from Steps A/B
  obtain ⟨m, hm, hmin⟩ := fy_min_pos n S hS A hA fh hfhpdf hfhcont r hr
  obtain ⟨M₁, hM₁pos, N₁, hM₁⟩ :=
    fyK_lower_bound n S hS A hA fh hfhpdf hfhcont fhK hfhKpdf hconv r hr
  obtain ⟨C, hC⟩ := noiseDens_moment_uniform n S hS A hA r hr
  obtain ⟨D, hD⟩ := posterior_moment_bound n S hS A hA fh hfhpdf r hr
  -- the positive envelopes `C'`, `D'`
  have hC'pos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD'pos : 0 < max D 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCle :
    ∀ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ≤ r → (∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume) ≤ max C 1 :=
    fun y hy => le_trans (hC y hy) (le_max_left _ _)
  have hDle :
    ∀ y : EuclideanSpace ℝ (Fin n),
      ‖y‖ ≤ r →
        ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * fh h) • h ∂volume‖ ≤ max D 1 :=
    fun y hy => le_trans (hD y hy) (le_max_left _ _)
  -- reduce the limit to the `Iio`-basis of `nhds 0` in `ℝ≥0∞`
  show
    Tendsto
      (fun K =>
        ⨆ y ∈ Metric.closedBall 0 r, ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖)
      atTop (𝓝 (⊥ : ℝ≥0∞))
  rw [nhds_bot_basis.tendsto_right_iff]
  -- the uniform machinery: for each `ε > 0`, eventually the sup is at most `ofReal ε`
  have hmach :
    ∀ ε > 0,
      ∀ᶠ K in atTop,
        ⨆ y ∈ Metric.closedBall 0 r, ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖ ≤
          ENNReal.ofReal ε := by
    intro ε hε
    have h2pi : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
    have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
    obtain ⟨K₀₁, hK₀₁⟩ :=
      hconv (M₁ * ε / (2 * max C 1)) (div_pos (mul_pos hM₁pos hε) (by positivity))
    obtain ⟨K₀₂, hK₀₂⟩ :=
      uniform_convergence_fy n S hS A hA fh (integrable_of_isPdf hfhpdf) fhK
        (fun K => integrable_of_isPdf (hfhKpdf K)) hconv (M₁ * m * ε / (2 * max D 1))
        (div_pos (mul_pos (mul_pos hM₁pos hm) hε) (by positivity))
    filter_upwards [Filter.eventually_ge_atTop (max (max K₀₁ K₀₂) N₁)] with K hK
    have hK₁ : K ≥ K₀₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hK)
    have hK₂ : K ≥ K₀₂ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hK)
    have hN₁ : K ≥ N₁ := le_trans (le_max_right _ _) hK
    refine iSup₂_le fun y hy => ?_
    have hy' : ‖y‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
      exact hy
    have hfyKpos : 0 < fyPDF n S hS A (fhK K) y := lt_of_lt_of_le hM₁pos (hM₁ K hN₁ y hy')
    have hfypos : 0 < fyPDF n S hS A fh y := lt_of_lt_of_le hm (hmin y hy')
    have hfyKne : fyPDF n S hS A (fhK K) y ≠ 0 := ne_of_gt hfyKpos
    have hfyne : fyPDF n S hS A fh y ≠ 0 := ne_of_gt hfypos
    -- the two accuracy thresholds
    set δ₁ : ℝ := M₁ * ε / (2 * max C 1) with hδ₁def
    set δ₂ : ℝ := M₁ * m * ε / (2 * max D 1) with hδ₂def
    have hδ₁pos : 0 < δ₁ := div_pos (mul_pos hM₁pos hε) (by positivity)
    have hδ₂pos : 0 < δ₂ := div_pos (mul_pos (mul_pos hM₁pos hm) hε) (by positivity)
    have hconv1 := hK₀₁ K hK₁
    have hconv2 := hK₀₂ K hK₂
    -- the `T₁` rate
    have hT1 :
      ‖(1 / fyPDF n S hS A (fhK K) y) •
            ∫ h : EuclideanSpace ℝ (Fin n),
              (noiseDens n S hS A y h * ((fhK K) h - fh h)) • h ∂volume‖ ≤
        (1 / M₁) * δ₁ * max C 1 := by
      refine
        le_trans
          (cme_rate_T1 n S hS A hA fh hfhpdf (fhK K) (hfhKpdf K) y hfyKne δ₁ hδ₁pos
            (fun x => by
              rw [abs_sub_comm]
              exact le_of_lt (hconv1 x)))
          ?_
      have hfac2 : 0 ≤ (1 / M₁) * δ₁ := mul_nonneg (le_of_lt (div_pos one_pos hM₁pos)) hδ₁pos.le
      calc
        (1 / fyPDF n S hS A (fhK K) y) * δ₁ *
              (∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume) ≤
            (1 / M₁) * δ₁ *
              (∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * noiseDens n S hS A y h ∂volume) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              ((div_le_div_iff_of_pos_left zero_lt_one hfyKpos hM₁pos).mpr (hM₁ K hN₁ y hy'))
              hδ₁pos.le)
            (MeasureTheory.integral_nonneg fun h =>
              mul_nonneg (norm_nonneg _)
                (by
                  simp only [noiseDens]
                  rw [multivariateGaussianPDF_eq n (0 : Fin n → ℝ) S hS
                      (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))]
                  exact
                    mul_nonneg (inv_nonneg.mpr (mul_nonneg h2pi.le hSqrtpos.le))
                      (Real.exp_nonneg _)))
        _ ≤ (1 / M₁) * δ₁ * max C 1 := mul_le_mul_of_nonneg_left (hCle y hy') hfac2
    -- the `T₂` rate
    have hT2 :
      ‖((fyPDF n S hS A fh y - fyPDF n S hS A (fhK K) y) /
              (fyPDF n S hS A (fhK K) y * fyPDF n S hS A fh y)) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * fh h) • h ∂volume‖ ≤
        (δ₂ / (M₁ * m)) * max D 1 := by
      refine
        le_trans
          (cme_rate_T2 n S hS A hA fh hfhpdf (fhK K) (hfhKpdf K) y hfyKne δ₂ (le_of_lt (hconv2 y)))
          ?_
      have hBle : M₁ * m ≤ fyPDF n S hS A (fhK K) y * fyPDF n S hS A fh y :=
        mul_le_mul (hM₁ K hN₁ y hy') (hmin y hy') hm.le hfyKpos.le
      have hBpos : 0 < fyPDF n S hS A (fhK K) y * fyPDF n S hS A fh y := mul_pos hfyKpos hfypos
      calc
        (δ₂ / (fyPDF n S hS A (fhK K) y * fyPDF n S hS A fh y)) *
              ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * fh h) • h ∂volume‖ ≤
            (δ₂ / (M₁ * m)) *
              ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDens n S hS A y h * fh h) • h ∂volume‖ :=
          mul_le_mul_of_nonneg_right
            ((div_le_div_iff_of_pos_left hδ₂pos (mul_pos hfyKpos hfypos) (mul_pos hM₁pos hm)).mpr
              hBle)
            (norm_nonneg _)
        _ ≤ (δ₂ / (M₁ * m)) * max D 1 :=
          mul_le_mul_of_nonneg_left (hDle y hy')
            (div_nonneg hδ₂pos.le (le_of_lt (mul_pos hM₁pos hm)))
    -- the field algebra of the thresholds
    have hval1 : (1 / M₁) * δ₁ * max C 1 = ε / 2 := by
      rw [hδ₁def]; field_simp
    have hval2 : (δ₂ / (M₁ * m)) * max D 1 = ε / 2 := by
      rw [hδ₂def]; field_simp
    -- the decomposition and the final bound
    have hdec := cme_decomp n S hS A hA fh hfhpdf (fhK K) (hfhKpdf K) y hfyKne hfyne
    have hnormle : ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖ ≤ ε := by
      rw [norm_sub_rev, hdec]
      exact le_trans (norm_add_le _ _) (by linarith [hT1, hT2, hval1, hval2])
    exact ENNReal.ofReal_le_ofReal hnormle
  -- conclude via the `Iio`-basis of `nhds 0`
  intro a ha
  by_cases htop : a = ⊤
  · subst htop
    refine
      Filter.Eventually.mono (hmach 1 one_pos) fun K hK =>
        Set.mem_Iio.2 (lt_of_le_of_lt hK ENNReal.ofReal_lt_top)
  · have hε : 0 < a.toReal := ENNReal.toReal_pos (ne_of_gt ha) htop
    refine
      Filter.Eventually.mono (hmach (a.toReal / 2) (div_pos hε two_pos)) fun K hK =>
        Set.mem_Iio.2
          (lt_of_le_of_lt hK
            ((ENNReal.ofReal_lt_iff_lt_toReal (by linarith) htop).mpr (div_lt_self hε one_lt_two)))

/-- Pointwise convergence of the conditional mean estimates (appendix_1.tex, Eq.
(pointwise_convergence) of `thm:main_result`): an immediate consequence of
`main_theorem`, since every point lies in some sufficiently large ball. -/
theorem cme_pointwise_convergence (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (hfhcont : Continuous fh) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K)) (hfhKcont : ∀ K, Continuous (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (y : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun K => ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖) atTop (nhds 0) := by
  have hr : 0 < ‖y‖ + 1 := by linarith [norm_nonneg y]
  have hmem : y ∈ Metric.closedBall 0 (‖y‖ + 1) :=
    Metric.mem_closedBall'.2
      (by
        rw [dist_eq_norm, zero_sub, norm_neg]
        linarith [norm_nonneg y])
  have hsup := main_theorem n S hS A hA fh hfhpdf hfhcont fhK hfhKpdf hfhKcont hconv (‖y‖ + 1) hr
  have h0 :
    Tendsto (fun K => ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds hsup
      (fun _ => zero_le) (fun K => le_iSup₂_of_le y hmem (le_refl _))
  have h1 :
    Tendsto (fun K => ENNReal.toReal (ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖))
      atTop (nhds 0) :=
    (ENNReal.continuousAt_toReal (x := (0 : ℝ≥0∞)) (by simp)).tendsto.comp h0
  exact Tendsto.congr' (Filter.Eventually.of_forall fun K => by simp) h1

/-! ## Epsilon–delta form and compact-set generalization of `main_theorem` -/

/-- Bridge between the `ℝ≥0∞`-supremum limit form of uniform convergence and the ε-δ form:
if the suprema of `ofReal ‖g K y‖` over `s` tend to `0`, then for every `ε > 0` there is a
threshold beyond which `‖g K y‖ ≤ ε` holds for all `y ∈ s` simultaneously. -/
theorem tendsto_iSup_norm_eps {E : Type*} {F : Type*} [NormedAddCommGroup F] {s : Set E}
    (g : ℕ → E → F) (h : Tendsto (fun K => ⨆ y ∈ s, ENNReal.ofReal ‖g K y‖) atTop (nhds 0)) (ε : ℝ)
    (hε : 0 < ε) : ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ y ∈ s, ‖g K y‖ ≤ ε := by
  classical
  have h' : Tendsto (fun K => ⨆ y ∈ s, ENNReal.ofReal ‖g K y‖) atTop (𝓝 (⊥ : ℝ≥0∞)) := h
  rw [nhds_bot_basis.tendsto_right_iff] at h'
  have h1 := h' (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp h1
  refine ⟨K₀, fun K hK y hy => ?_⟩
  have hpt : ENNReal.ofReal ‖g K y‖ ≤ ⨆ y' ∈ s, ENNReal.ofReal ‖g K y'‖ :=
    le_iSup₂_of_le y hy (le_refl _)
  have hlt : ENNReal.ofReal ‖g K y‖ < ENNReal.ofReal ε :=
    lt_of_le_of_lt hpt (Set.mem_Iio.mp (hK₀ K hK))
  exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff').mp hlt).1

/-- Epsilon–delta restatement of `main_theorem`: uniform convergence of the conditional
mean estimates on the closed ball `B_r`, in the familiar form

`∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∀ y ∈ B_r, ‖ĥ^{(K)}(y) − ĥ(y)‖ ≤ ε`. -/
theorem cme_uniform_balls_eps (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (hfhcont : Continuous fh) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K)) (hfhKcont : ∀ K, Continuous (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε) (r : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ K₀ : ℕ,
      ∀ K ≥ K₀, ∀ y ∈ Metric.closedBall 0 r, ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖ ≤ ε :=
  tendsto_iSup_norm_eps (fun K y => cme n S hS A fh y - cme n S hS A (fhK K) y)
    (main_theorem n S hS A hA fh hfhpdf hfhcont fhK hfhKpdf hfhKcont hconv r hr) ε hε

/-- Generalization of `main_theorem` from closed balls to arbitrary compact sets: the
conditional mean estimates converge uniformly on every compact subset of `ℝ^N`
(compact convergence). A compact set is contained in some closed ball, so this follows
from `main_theorem` by monotonicity of the supremum. -/
theorem cme_uniform_compact (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (hfhcont : Continuous fh) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K)) (hfhKcont : ∀ K, Continuous (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsCompact s) :
    Tendsto (fun K => ⨆ y ∈ s, ENNReal.ofReal ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖) atTop
      (nhds 0) := by
  classical
  obtain ⟨R, hRpos, hR⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds
      (main_theorem n S hS A hA fh hfhpdf hfhcont fhK hfhKpdf hfhKcont hconv R hRpos)
      (fun _ => zero_le) (fun K => iSup₂_le fun y hy => le_iSup₂_of_le y (hR hy) (le_refl _))

/-- Epsilon–delta form of `cme_uniform_compact`: for every compact set `s` and every
`ε > 0` there is a threshold beyond which `‖ĥ^{(K)}(y) − ĥ(y)‖ ≤ ε` holds for all
`y ∈ s` simultaneously. -/
theorem cme_uniform_compact_eps (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhpdf : IsPdf fh) (hfhcont : Continuous fh) (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfhKpdf : ∀ K, IsPdf (fhK K)) (hfhKcont : ∀ K, Continuous (fhK K))
    (hconv : ∀ ε > 0, ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ x, |fh x - fhK K x| < ε)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsCompact s) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ y ∈ s, ‖cme n S hS A fh y - cme n S hS A (fhK K) y‖ ≤ ε :=
  tendsto_iSup_norm_eps (fun K y => cme n S hS A fh y - cme n S hS A (fhK K) y)
    (cme_uniform_compact n S hS A hA fh hfhpdf hfhcont fhK hfhKpdf hfhKcont hconv s hs) ε hε

/-! ## Rectangular observation matrices (`A : Fin m × Fin n`, Tracks A + B)

For `m < n` (more latent coordinates than observations) `A` cannot be invertible, and the
likelihood `f_n(y − A h)` is constant along the fibers `h₀ + ker A`, so the square-case
mechanisms (the `|det A|⁻¹` change of variables, the translation `h = h' + A⁻¹y`, and the
decay `‖h‖ · f_n(y − A h) ≤ C(y)`) all fail. What survives — for *every* rectangular `A`,
with no rank hypothesis — is the denominator side of the theory (positivity, continuity
and compact lower bounds of `f_y`), because it only uses that the nondegenerate Gaussian
noise density is positive and bounded everywhere. Uniform convergence of the marginals
over *all* of `ℝ^m` then holds under weighted-L¹ convergence of the priors
(`uniform_convergence_fyR`); that hypothesis is phrased with the `ℝ≥0∞`-valued integral,
since the real Bochner integral of a non-integrable nonnegative function vanishes in
Mathlib (non-integrable functions have integral `0`), which would make a real-integral
hypothesis vacuous. -/

/-- Pointwise identity of the rectangular noise density with the Gaussian pdf evaluated
at the linear-map form `y + (−A) h`. -/
theorem noiseDensR_eq (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin n)) :
    noiseDensR m n S hS A y h =
      multivariateGaussianPDF m (0 : Fin m → ℝ) S hS
        (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h) := by
  simp only [noiseDensR]
  rw [multivariateGaussianPDF_eq m (0 : Fin m → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ))),
    multivariateGaussianPDF_eq m (0 : Fin m → ℝ) S hS
      (y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h)]
  have hco :
    ((WithLp.toLp 2 ((y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ))) : Fin m → ℝ) =
      ((y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h) : Fin m → ℝ) := by
    rw [WithLp.ofLp_toLp]
    show
      (y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ) =
        (y : Fin m → ℝ) + ((-1 : ℝ) • A) *ᵥ (h : Fin n → ℝ)
    rw [Matrix.smul_mulVec, neg_one_smul, sub_eq_add_neg]
  rw [hco, WithLp.ofLp_add]

/-- Measurability of the rectangular noise density in `h`. -/
theorem aemeasurable_noiseDensR (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    AEMeasurable (noiseDensR m n S hS A y) volume := by
  have hcomp :
    noiseDensR m n S hS A y =
      (fun x => multivariateGaussianPDF m (0 : Fin m → ℝ) S hS x) ∘
        (fun h => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h) := by
    funext h
    exact noiseDensR_eq m n S hS A y h
  rw [hcomp]
  exact
    ((measurable_multivariateGaussianPDF m (0 : Fin m → ℝ) S hS).comp
        (by fun_prop :
          Measurable
            (fun h : EuclideanSpace ℝ (Fin n) =>
              y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h))).aemeasurable

/-- Pointwise positivity of the rectangular noise density (the Gaussian is positive
everywhere on `ℝ^m`). -/
theorem noiseDensR_pos (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin n)) :
    0 < noiseDensR m n S hS A y h := by
  have h2pi : 0 < (2 * Real.pi) ^ ((m : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  simp only [noiseDensR]
  rw [multivariateGaussianPDF_eq m (0 : Fin m → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ)))]
  exact mul_pos (inv_pos.mpr (mul_pos h2pi hSqrtpos)) (Real.exp_pos _)

/-- The constant pointwise bound on the rectangular noise density (the Gaussian sup). -/
theorem noiseDensR_le_const (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin n)) :
    noiseDensR m n S hS A y h ≤ ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ := by
  simp only [noiseDensR]
  exact
    multivariateGaussianPDF_le_const m (0 : Fin m → ℝ) S hS
      (WithLp.toLp 2 ((y : Fin m → ℝ) - A.mulVec (h : Fin n → ℝ)))

/-- Rectangular version of `fy_pos` (Step B.3): the marginal density `f_y(y)` is strictly
positive for every pdf `f` on `ℝ^n`, every `y ∈ ℝ^m`, and **every** observation matrix
`A : Matrix (Fin m) (Fin n) ℝ` — no rank hypothesis is needed, since only the pointwise
positivity and boundedness of the Gaussian noise density are used. -/
theorem fy_pos_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin m)) : 0 < fyPDFR m n S hS A f y := by
  classical
  have hposintegrand : ∀ h : EuclideanSpace ℝ (Fin n), 0 ≤ noiseDensR m n S hS A y h * f h := by
    intro h
    exact mul_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)) (hf.1 h)
  have hndposF : ∀ h : EuclideanSpace ℝ (Fin n), 0 < noiseDensR m n S hS A y h := fun h =>
    noiseDensR_pos m n S hS A y h
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hndle : ∀ h : EuclideanSpace ℝ (Fin n), noiseDensR m n S hS A y h ≤ c₀ := fun h =>
    noiseDensR_le_const m n S hS A y h
  have hinteg : MeasureTheory.Integrable (fun h => noiseDensR m n S hS A y h * f h) volume := by
    have hprodM :
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDensR m n S hS A y h * f h) volume :=
      ((aemeasurable_noiseDensR m n S hS A y).mul
          ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    have hfint : MeasureTheory.Integrable (fun h => c₀ * f h) volume :=
      MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf hf)
    refine MeasureTheory.Integrable.mono' hfint hprodM (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_eq_self.mpr (hposintegrand h)]
    exact mul_le_mul_of_nonneg_right (hndle h) (hf.1 h)
  have hnonneg : 0 ≤ fyPDFR m n S hS A f y := by
    rw [fyPDFR]
    exact MeasureTheory.integral_nonneg hposintegrand
  by_contra hcon
  have hle : fyPDFR m n S hS A f y ≤ 0 := le_of_not_gt hcon
  have hzero : fyPDFR m n S hS A f y = 0 := le_antisymm hle hnonneg
  have haezero : (fun h => noiseDensR m n S hS A y h * f h) =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hposintegrand)
          hinteg).mp
      hzero
  have hfeq : f =ᵐ[volume] 0 := by
    filter_upwards [haezero] with h hval
    rcases mul_eq_zero.mp hval with h0' | h0'
    · exact absurd h0' (ne_of_gt (hndposF h))
    · exact h0'
  have hintf : ∫ x, f x ∂volume = 0 := by
    rw [MeasureTheory.integral_congr_ae hfeq]
    simp
  rw [hf.2] at hintf
  exact one_ne_zero hintf

/-- Rectangular version of `fy_cont` (Step B.4): the marginal density `f_y` is continuous
in `y ∈ ℝ^m` for every rectangular `A` — no rank hypothesis and no continuity of `f`
needed (dominated convergence with the integrable dominator `c₀ · f`). -/
theorem fy_cont_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) :
    Continuous (fyPDFR m n S hS A f) := by
  classical
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hFm :
    ∀ y : EuclideanSpace ℝ (Fin m),
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDensR m n S hS A y h * f h) volume := by
    intro y
    exact
      ((aemeasurable_noiseDensR m n S hS A y).mul
          ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hbnd :
    ∀ (y : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin n)),
      ‖noiseDensR m n S hS A y h * f h‖ ≤ c₀ * f h := by
    intro y h
    rw [Real.norm_eq_abs,
      abs_eq_self.mpr (mul_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)) (hf.1 h))]
    exact mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) (hf.1 h)
  have hbint : MeasureTheory.Integrable (fun h => c₀ * f h) volume :=
    MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf hf)
  have hcont :
    ∀ h : EuclideanSpace ℝ (Fin n), Continuous (fun y => noiseDensR m n S hS A y h * f h) := by
    intro h
    have hndc : Continuous (fun y => noiseDensR m n S hS A y h) := by
      have hcomp :
        (fun y : EuclideanSpace ℝ (Fin m) => noiseDensR m n S hS A y h) =
          (fun x => multivariateGaussianPDF m (0 : Fin m → ℝ) S hS x) ∘
            (fun y => y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h) := by
        funext y
        exact noiseDensR_eq m n S hS A y h
      rw [hcomp]
      exact
        (multivariateGaussianPDF_continuous m (0 : Fin m → ℝ) S hS).comp
          (by fun_prop :
            Continuous
              (fun y : EuclideanSpace ℝ (Fin m) =>
                y + (Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin m) ((-1 : ℝ) • A)) h))
    exact hndc.mul continuous_const
  unfold fyPDFR
  refine continuous_iff_continuousAt.mpr fun y => ?_
  refine
    MeasureTheory.continuousAt_of_dominated (x₀ := y) (bound := fun h => c₀ * f h)
      (Filter.Eventually.of_forall hFm)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall (hbnd x)) hbint
      (Filter.Eventually.of_forall fun h => (hcont h).continuousAt)

/-- Rectangular version of `fy_min_pos` (Step B.5): on every ball in `ℝ^m` the marginal
density admits a positive lower bound, for every rectangular `A`. -/
theorem fy_min_pos_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f) (r : ℝ)
    (hr : 0 < r) :
    ∃ mm : ℝ, 0 < mm ∧ ∀ y : EuclideanSpace ℝ (Fin m), ‖y‖ ≤ r → mm ≤ fyPDFR m n S hS A f y := by
  classical
  have hcomp : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r) :=
    ProperSpace.isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r).Nonempty :=
    ⟨0, Metric.mem_closedBall_self hr.le⟩
  obtain ⟨y₀, hy₀mem, hy₀min⟩ := hcomp.exists_isMinOn hne ((fy_cont_R m n S hS A f hf).continuousOn)
  have hpos : 0 < fyPDFR m n S hS A f y₀ := fy_pos_R m n S hS A f hf y₀
  refine ⟨fyPDFR m n S hS A f y₀, hpos, ?_⟩
  intro y hy
  have hmem : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r := by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hy
  exact isMinOn_iff.mp hy₀min y hmem

/-- **Track B**: uniform convergence of the rectangular marginal densities over **all** of
`ℝ^m`, for every observation matrix `A : Matrix (Fin m) (Fin n) ℝ` (no rank hypothesis),
under weighted-L¹ convergence of the priors. The hypothesis is phrased with the
`ℝ≥0∞`-valued (upper) integral: the real Bochner integral of a non-integrable nonnegative
function vanishes in Mathlib, so a real-integral hypothesis would be vacuous. The rate
constant `c₀ = ((2π)^{m/2} √det S)⁻¹` is the Gaussian sup, the rectangular analogue of the
square-case rate `|det A|⁻¹`. -/
theorem uniform_convergence_fyR (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (fh : EuclideanSpace ℝ (Fin n) → ℝ) (hfhpdf : IsPdf fh)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfhKpdf : ∀ K, IsPdf (fhK K))
    (hw :
      ∀ ε > 0,
        ∃ K₀ : ℕ,
          ∀ K ≥ K₀,
            ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |fh h - fhK K h|) ∂volume <
              ENNReal.ofReal ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ,
      ∀ K ≥ K₀,
        ∀ y : EuclideanSpace ℝ (Fin m),
          |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| ≤
            ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * ε := by
  classical
  obtain ⟨K₀, hK₀⟩ := hw ε hε
  have h2pi : 0 < (2 * Real.pi) ^ ((m : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := inv_pos.mpr (mul_pos h2pi hSqrtpos)
  refine ⟨K₀, fun K hK y => ?_⟩
  have hwK := hK₀ K hK
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun h => (1 + ‖h‖) * |fh h - fhK K h| with hgdef
  -- measurability, nonnegativity and integrability of the weighted difference
  have hfhm : MeasureTheory.AEStronglyMeasurable fh volume :=
    (integrable_of_isPdf hfhpdf).aestronglyMeasurable
  have hfhKm : MeasureTheory.AEStronglyMeasurable (fhK K) volume :=
    (integrable_of_isPdf (hfhKpdf K)).aestronglyMeasurable
  have hgnneg : ∀ h : EuclideanSpace ℝ (Fin n), 0 ≤ g h := by
    intro h
    exact mul_nonneg (by positivity) (abs_nonneg _)
  have hfm : MeasureTheory.AEStronglyMeasurable g volume := by
    show MeasureTheory.AEStronglyMeasurable (fun h => (1 + ‖h‖) * |fh h - fhK K h|) volume
    fun_prop
  have hintW : MeasureTheory.Integrable g volume := by
    have hmemLp : MeasureTheory.MemLp g 1 volume := by
      rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_one_eq_lintegral_enorm hfm]
      have h2 : ∫⁻ x, ‖g x‖ₑ ∂volume = ∫⁻ x, ENNReal.ofReal (g x) ∂volume := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact Real.enorm_eq_ofReal (hgnneg x)
      rw [h2]
      exact lt_of_lt_of_le hwK le_top
    exact MeasureTheory.memLp_one_iff_integrable.mp hmemLp
  -- integrability of the unweighted difference and of the two `cme`-type integrands
  have hintAbs : MeasureTheory.Integrable (fun h => |fh h - fhK K h|) volume := by
    have hsum : MeasureTheory.Integrable (fun h => fh h + (fhK K) h) volume :=
      (integrable_of_isPdf hfhpdf).add (integrable_of_isPdf (hfhKpdf K))
    have habsM : MeasureTheory.AEStronglyMeasurable (fun h => |fh h - fhK K h|) volume := by
      fun_prop
    refine MeasureTheory.Integrable.mono' hsum habsM (Filter.Eventually.of_forall fun h => ?_)
    show ‖|fh h - fhK K h|‖ ≤ fh h + (fhK K) h
    rw [Real.norm_eq_abs, abs_le]
    have hFK : (0 : ℝ) ≤ fh h := hfhpdf.1 h
    have hF : (0 : ℝ) ≤ (fhK K) h := (hfhKpdf K).1 h
    have habsnn : (0 : ℝ) ≤ |fh h - fhK K h| := abs_nonneg _
    have htri : |fh h - fhK K h| ≤ fh h + (fhK K) h := by
      have h2' := abs_sub (fh h) (fhK K h)
      rwa [abs_of_nonneg hFK, abs_of_nonneg hF] at h2'
    constructor
    · linarith
    · linarith
  have hIfh : MeasureTheory.Integrable (fun h => noiseDensR m n S hS A y h * fh h) volume := by
    have hprodM :
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDensR m n S hS A y h * fh h) volume :=
      ((aemeasurable_noiseDensR m n S hS A y).mul
          ((integrable_of_isPdf hfhpdf).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    have hgint : MeasureTheory.Integrable (fun h => c₀ * fh h) volume :=
      MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf hfhpdf)
    refine MeasureTheory.Integrable.mono' hgint hprodM (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs,
      abs_eq_self.mpr (mul_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)) (hfhpdf.1 h))]
    exact mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) (hfhpdf.1 h)
  have hIfhK :
    MeasureTheory.Integrable (fun h => noiseDensR m n S hS A y h * (fhK K) h) volume := by
    have hprodM :
      MeasureTheory.AEStronglyMeasurable (fun h => noiseDensR m n S hS A y h * (fhK K) h) volume :=
      ((aemeasurable_noiseDensR m n S hS A y).mul
          ((integrable_of_isPdf
              (hfhKpdf K)).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
    have hgint : MeasureTheory.Integrable (fun h => c₀ * (fhK K) h) volume :=
      MeasureTheory.Integrable.smul c₀ (integrable_of_isPdf (hfhKpdf K))
    refine MeasureTheory.Integrable.mono' hgint hprodM (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs,
      abs_eq_self.mpr (mul_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)) ((hfhKpdf K).1 h))]
    exact mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) ((hfhKpdf K).1 h)
  -- the chain: |f_y − f_y^{(K)}| ≤ c₀ ∫ (1+‖h‖) |f − f^{(K)}| ≤ c₀ ε
  have hstep1 :
    |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| ≤
      ∫ h : EuclideanSpace ℝ (Fin n), noiseDensR m n S hS A y h * |fh h - fhK K h| ∂volume := by
    simp only [fyPDFR]
    rw [← MeasureTheory.integral_sub hIfh hIfhK]
    refine
      le_trans
        (MeasureTheory.abs_integral_le_integral_abs (μ := volume) (f :=
          fun h : EuclideanSpace ℝ (Fin n) =>
          noiseDensR m n S hS A y h * fh h - noiseDensR m n S hS A y h * (fhK K) h))
        ?_
    rw [integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)]
    show
      |noiseDensR m n S hS A y h * fh h - noiseDensR m n S hS A y h * (fhK K) h| =
        noiseDensR m n S hS A y h * |fh h - fhK K h|
    rw [← mul_sub, abs_mul, abs_of_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h))]
  have hstep2 :
    ∫ h : EuclideanSpace ℝ (Fin n), noiseDensR m n S hS A y h * |fh h - fhK K h| ∂volume ≤
      ∫ h : EuclideanSpace ℝ (Fin n), c₀ * |fh h - fhK K h| ∂volume := by
    have hf2 : 0 ≤ᵐ[volume] (fun h => noiseDensR m n S hS A y h * |fh h - fhK K h|) :=
      Filter.Eventually.of_forall fun h =>
        mul_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)) (abs_nonneg _)
    have hg2 : MeasureTheory.Integrable (fun h => c₀ * |fh h - fhK K h|) volume :=
      MeasureTheory.Integrable.smul c₀ hintAbs
    have hle2 :
      (fun h => noiseDensR m n S hS A y h * |fh h - fhK K h|) ≤ᵐ[volume]
        (fun h => c₀ * |fh h - fhK K h|) :=
      Filter.Eventually.of_forall fun h =>
        mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) (abs_nonneg _)
    exact integral_mono_of_nonneg hf2 hg2 hle2
  have hstep3 :
    ∫ h : EuclideanSpace ℝ (Fin n), |fh h - fhK K h| ∂volume ≤
      ∫ h : EuclideanSpace ℝ (Fin n), g h ∂volume := by
    have hf3 : 0 ≤ᵐ[volume] (fun h => |fh h - fhK K h|) :=
      Filter.Eventually.of_forall fun h => abs_nonneg _
    have hle3 : (fun h => |fh h - fhK K h|) ≤ᵐ[volume] g := by
      refine Filter.Eventually.of_forall fun h => ?_
      have h1le : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
      calc
        |fh h - fhK K h| = |fh h - fhK K h| * 1 := by ring
        _ ≤ |fh h - fhK K h| * (1 + ‖h‖) := mul_le_mul_of_nonneg_left h1le (abs_nonneg _)
        _ = (1 + ‖h‖) * |fh h - fhK K h| := by ring
    exact integral_mono_of_nonneg hf3 hintW hle3
  have hwK' : ∫ h : EuclideanSpace ℝ (Fin n), g h ∂volume ≤ ε := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgnneg) hfm]
    exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hε) (le_of_lt hwK)
  refine le_trans hstep1 (le_trans hstep2 ?_)
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (le_trans hstep3 hwK') hc₀pos.le

/-! ## Track C: the CME convergence for rectangular `A` (`m < n`)

The square-case mechanisms that fail for `m < n` (the `|det A|⁻¹` change of variables, the
translation `h = h' + A⁻¹y`, and the decay `‖h‖ · f_n(y − A h) ≤ C(y)`) are replaced by
the `c₀`-domination plus a finite-first-moment hypothesis on the prior
`∫ ‖h‖ f(h) dh < ∞` (without which the posterior mean itself may fail to exist), together
with the weighted-L¹ convergence of the priors from Track B. -/

/-- Bridge from the eventually-bounded sup-form to the `Tendsto` form (the generalization
of the ending of `main_theorem`, reusable for any uniform-convergence statement whose
suprema are eventually bounded by `ofReal ε`). -/
theorem tendsto_iSup_ofReal_of_eventually_le {E : Type*} {F : Type*} [NormedAddCommGroup F]
    {s : Set E} (g : ℕ → E → F)
    (h : ∀ ε > 0, ∀ᶠ K in atTop, ⨆ y ∈ s, ENNReal.ofReal ‖g K y‖ ≤ ENNReal.ofReal ε) :
    Tendsto (fun K => ⨆ y ∈ s, ENNReal.ofReal ‖g K y‖) atTop (nhds 0) := by
  show Tendsto (fun K => ⨆ y ∈ s, ENNReal.ofReal ‖g K y‖) atTop (𝓝 (⊥ : ℝ≥0∞))
  rw [nhds_bot_basis.tendsto_right_iff]
  intro a ha
  by_cases htop : a = ⊤
  · subst htop
    refine
      Filter.Eventually.mono (h 1 one_pos) fun K hK =>
        Set.mem_Iio.2 (lt_of_le_of_lt hK ENNReal.ofReal_lt_top)
  · have hε : 0 < a.toReal := ENNReal.toReal_pos (ne_of_gt ha) htop
    refine
      Filter.Eventually.mono (h (a.toReal / 2) (div_pos hε two_pos)) fun K hK =>
        Set.mem_Iio.2
          (lt_of_le_of_lt hK
            ((ENNReal.ofReal_lt_iff_lt_toReal (by linarith) htop).mpr (div_lt_self hε one_lt_two)))

/-- Pointwise norm bound for the rectangular posterior-moment integrand. -/
theorem posterior_norm_le_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin n)) :
    ‖(noiseDensR m n S hS A y h * f h) • h‖ ≤
      ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (‖h‖ * f h) := by
  classical
  have h2pi : 0 < (2 * Real.pi) ^ ((m : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := inv_pos.mpr (mul_pos h2pi hSqrtpos)
  calc
    ‖(noiseDensR m n S hS A y h * f h) • h‖ = ‖h‖ * (noiseDensR m n S hS A y h * f h) := by
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)), abs_of_nonneg (hf.1 h)]
      ring
    _ ≤ ‖h‖ * (c₀ * f h) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) (hf.1 h)) (norm_nonneg _)
    _ = c₀ * (‖h‖ * f h) := by ring

/-- Integrability of the rectangular posterior-moment integrand, given the finite first
moment of the prior. -/
theorem posterior_integrable_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin m))
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * f h) volume) :
    MeasureTheory.Integrable (fun h => (noiseDensR m n S hS A y h * f h) • h) volume := by
  classical
  have hfm :
    MeasureTheory.AEStronglyMeasurable (fun h => (noiseDensR m n S hS A y h * f h) • h) volume :=
    (((aemeasurable_noiseDensR m n S hS A y).mul
            ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)).smul
        (measurable_id.aemeasurable)).aestronglyMeasurable
  have hgint :
    MeasureTheory.Integrable
      (fun h => ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (‖h‖ * f h)) volume :=
    MeasureTheory.Integrable.smul ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ hfmom
  refine
    MeasureTheory.Integrable.mono' hgint hfm
      (Filter.Eventually.of_forall fun h => posterior_norm_le_R m n S hS A f hf y h)

/-- Rectangular version of `posterior_moment_bound`: the posterior moment is bounded by
`c₀ · ∫ ‖h‖ f(h) dh`, **uniformly over all `y ∈ ℝ^m`** — the finite-first-moment
hypothesis on the prior replaces the square-case translation argument. -/
theorem posterior_moment_bound_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin m))
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * f h) volume) :
    ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * f h) • h ∂volume‖ ≤
      ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ *
        ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * f h ∂volume := by
  classical
  have hmono :
    ∫ h : EuclideanSpace ℝ (Fin n), ‖(noiseDensR m n S hS A y h * f h) • h‖ ∂volume ≤
      ∫ h : EuclideanSpace ℝ (Fin n),
        ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (‖h‖ * f h) ∂volume := by
    have hf2 : 0 ≤ᵐ[volume] (fun h => ‖(noiseDensR m n S hS A y h * f h) • h‖) :=
      Filter.Eventually.of_forall fun h => norm_nonneg _
    have hg2 :
      MeasureTheory.Integrable
        (fun h => ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (‖h‖ * f h)) volume :=
      MeasureTheory.Integrable.smul ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ hfmom
    have hle2 :
      (fun h => ‖(noiseDensR m n S hS A y h * f h) • h‖) ≤ᵐ[volume]
        (fun h => ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * (‖h‖ * f h)) :=
      Filter.Eventually.of_forall fun h => posterior_norm_le_R m n S hS A f hf y h
    exact integral_mono_of_nonneg hf2 hg2 hle2
  refine
    le_trans
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume) (f :=
        fun h : EuclideanSpace ℝ (Fin n) => (noiseDensR m n S hS A y h * f h) • h))
      ?_
  rw [← MeasureTheory.integral_const_mul]
  exact hmono

/-- Integrability of the weighted prior difference `(1+‖h‖)·|u − v|` from the `∫⁻`-bound. -/
theorem weighted_diff_integrable (n : ℕ) (u v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : MeasureTheory.Integrable u volume) (hv : MeasureTheory.Integrable v volume)
    (hwK : ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |u h - v h|) ∂volume < ⊤) :
    MeasureTheory.Integrable (fun h => (1 + ‖h‖) * |u h - v h|) volume := by
  classical
  have huM : MeasureTheory.AEStronglyMeasurable u volume := hu.aestronglyMeasurable
  have hvM : MeasureTheory.AEStronglyMeasurable v volume := hv.aestronglyMeasurable
  have hgnneg : ∀ h : EuclideanSpace ℝ (Fin n), 0 ≤ (1 + ‖h‖) * |u h - v h| := fun h =>
    mul_nonneg (by positivity) (abs_nonneg _)
  have hfm : MeasureTheory.AEStronglyMeasurable (fun h => (1 + ‖h‖) * |u h - v h|) volume := by
    fun_prop
  have hmemLp : MeasureTheory.MemLp (fun h => (1 + ‖h‖) * |u h - v h|) 1 volume := by
    rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_one_eq_lintegral_enorm hfm]
    have h2 :
      ∫⁻ x, ‖(fun h => (1 + ‖h‖) * |u h - v h|) x‖ₑ ∂volume =
        ∫⁻ x, ENNReal.ofReal ((1 + ‖x‖) * |u x - v x|) ∂volume := by
      refine lintegral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      exact Real.enorm_eq_ofReal (hgnneg x)
    rw [h2]
    exact lt_of_lt_of_le hwK le_top
  exact MeasureTheory.memLp_one_iff_integrable.mp hmemLp

/-- Integrability of the rectangular posterior-difference integrand, given the weighted-L¹
control of the prior difference. -/
theorem posterior_diff_integrable_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK) (y : EuclideanSpace ℝ (Fin m))
    (hintW :
      MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => (1 + ‖h‖) * |f h - fK h|)
        volume) :
    MeasureTheory.Integrable (fun h => (noiseDensR m n S hS A y h * (fK h - f h)) • h) volume := by
  classical
  have hndM := aemeasurable_noiseDensR m n S hS A y
  have hfhM : MeasureTheory.AEStronglyMeasurable f volume :=
    (integrable_of_isPdf hf).aestronglyMeasurable
  have hfhKM : MeasureTheory.AEStronglyMeasurable fK volume :=
    (integrable_of_isPdf hfK).aestronglyMeasurable
  have hdiffM : AEMeasurable (fun h => noiseDensR m n S hS A y h * (fK h - f h)) volume := by
    have h1 :
      (fun h => noiseDensR m n S hS A y h * (fK h - f h)) =
        (fun h => noiseDensR m n S hS A y h * fK h) -
          (fun h => noiseDensR m n S hS A y h * f h) := by
      funext h
      rw [Pi.sub_apply, mul_sub]
    rw [h1]
    exact (hndM.mul hfhKM.aemeasurable).sub (hndM.mul hfhM.aemeasurable)
  have hvecM :
    MeasureTheory.AEStronglyMeasurable (fun h => (noiseDensR m n S hS A y h * (fK h - f h)) • h)
      volume :=
    (hdiffM.smul (measurable_id.aemeasurable)).aestronglyMeasurable
  have hgint :
    MeasureTheory.Integrable
      (fun h => ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ * ((1 + ‖h‖) * |f h - fK h|))
      volume :=
    MeasureTheory.Integrable.smul ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ hintW
  have hnormle : ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ 1 + ‖h‖ := fun h => by
    linarith [norm_nonneg h]
  refine MeasureTheory.Integrable.mono' hgint hvecM (Filter.Eventually.of_forall fun h => ?_)
  have h2pi : 0 < (2 * Real.pi) ^ ((m : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := inv_pos.mpr (mul_pos h2pi hSqrtpos)
  calc
    ‖(noiseDensR m n S hS A y h * (fK h - f h)) • h‖ =
        noiseDensR m n S hS A y h * |fK h - f h| * ‖h‖ :=
      by
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h))]
    _ = (noiseDensR m n S hS A y h * ‖h‖) * |fK h - f h| := by ring
    _ ≤ (c₀ * (1 + ‖h‖)) * |fK h - f h| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (noiseDensR_le_const m n S hS A y h) (hnormle h) (norm_nonneg _) hc₀pos.le)
        (abs_nonneg (fK h - f h))
    _ = c₀ * ((1 + ‖h‖) * |f h - fK h|) := by rw [mul_assoc, abs_sub_comm (fK h) (f h)]

/-- Integrability of the rectangular `cme` integrand, given the finite first moment of the
prior (which makes the domination `(c₀/f_y) · ‖h‖ f(h)` integrable). -/
theorem cme_integrable_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (y : EuclideanSpace ℝ (Fin m))
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * f h) volume) :
    MeasureTheory.Integrable
      (fun h => ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h) volume := by
  classical
  have hfypos : 0 < fyPDFR m n S hS A f y := fy_pos_R m n S hS A f hf y
  have hndM := aemeasurable_noiseDensR m n S hS A y
  have hprod : AEMeasurable (fun h => noiseDensR m n S hS A y h * f h) volume :=
    hndM.mul ((integrable_of_isPdf hf).aestronglyMeasurable.aemeasurable)
  have hsM :
    AEMeasurable (fun h => (noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) volume := by
    have h1 :
      AEMeasurable (fun h => (1 / fyPDFR m n S hS A f y) * (noiseDensR m n S hS A y h * f h))
        volume :=
      hprod.const_mul (1 / fyPDFR m n S hS A f y)
    have h2 :
      (fun h => (noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) = fun h =>
        (1 / fyPDFR m n S hS A f y) * (noiseDensR m n S hS A y h * f h) := by
      funext h
      ring
    rw [h2]
    exact h1
  have hvecM :
    MeasureTheory.AEStronglyMeasurable
      (fun h => ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h) volume :=
    (hsM.smul (measurable_id.aemeasurable)).aestronglyMeasurable
  have hgint :
    MeasureTheory.Integrable
      (fun h =>
        (((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ / fyPDFR m n S hS A f y) * (‖h‖ * f h))
      volume :=
    MeasureTheory.Integrable.smul
      (((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ / fyPDFR m n S hS A f y) hfmom
  refine MeasureTheory.Integrable.mono' hgint hvecM (Filter.Eventually.of_forall fun h => ?_)
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  calc
    ‖((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h‖ =
        ‖h‖ * ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) :=
      by
      rw [norm_smul, norm_div, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h)), abs_of_nonneg (hf.1 h),
        abs_of_nonneg (le_of_lt hfypos)]
      ring
    _ ≤ ‖h‖ * ((c₀ / fyPDFR m n S hS A f y) * f h) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h2 : noiseDensR m n S hS A y h * f h ≤ c₀ * f h :=
        mul_le_mul_of_nonneg_right (noiseDensR_le_const m n S hS A y h) (hf.1 h)
      have h3 :
        (noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y ≤
          (c₀ * f h) / fyPDFR m n S hS A f y :=
        (div_le_div_iff_of_pos_right hfypos).mpr h2
      exact h3.trans (le_of_eq (by ring))
    _ = (c₀ / fyPDFR m n S hS A f y) * (‖h‖ * f h) := by ring

/-- Rectangular version of `cme_decomp` (Step C.1): the two-term decomposition of the
`cmeR` difference. The finite-first-moment hypothesis `hfmom` makes the two `cme`
integrand candidates integrable; `hintW` (the weighted-L¹ control of the prior
difference) makes the `f_y^{(K)}`-side integrable. -/
theorem cme_decomp_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsPdf f)
    (fK : EuclideanSpace ℝ (Fin n) → ℝ) (hfK : IsPdf fK) (y : EuclideanSpace ℝ (Fin m))
    (hfyK : fyPDFR m n S hS A fK y ≠ 0) (hfy : fyPDFR m n S hS A f y ≠ 0)
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * f h) volume)
    (hintW :
      MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => (1 + ‖h‖) * |f h - fK h|)
        volume) :
    cmeR m n S hS A fK y - cmeR m n S hS A f y =
      (1 / fyPDFR m n S hS A fK y) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * (fK h - f h)) • h ∂volume +
        ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
            (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) •
          ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * f h) • h ∂volume := by
  classical
  have hfhM : MeasureTheory.AEStronglyMeasurable f volume :=
    (integrable_of_isPdf hf).aestronglyMeasurable
  have hfhKM : MeasureTheory.AEStronglyMeasurable fK volume :=
    (integrable_of_isPdf hfK).aestronglyMeasurable
  -- the first moment of `fK`, controlled by the weighted-L¹ hypothesis and `hfmom`
  have hfmomK :
    MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * fK h) volume := by
    have h1 : MeasureTheory.Integrable (fun h => ‖h‖ * |f h - fK h|) volume := by
      refine MeasureTheory.Integrable.mono' hintW ?_ (Filter.Eventually.of_forall fun h => ?_)
      · exact
          ((Continuous.aemeasurable
                  (by fun_prop : Continuous (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖))).mul
              ((by fun_prop :
                  MeasureTheory.AEStronglyMeasurable (fun h => |f h - fK h|)
                    volume).aemeasurable)).aestronglyMeasurable
      · show ‖‖h‖ * |f h - fK h|‖ ≤ (1 + ‖h‖) * |f h - fK h|
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))]
        exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg h]) (abs_nonneg _)
    have hsum : MeasureTheory.Integrable (fun h => ‖h‖ * |f h - fK h| + ‖h‖ * f h) volume :=
      h1.add hfmom
    have hfKm : MeasureTheory.AEStronglyMeasurable (fun h => ‖h‖ * fK h) volume :=
      ((Continuous.aemeasurable
              (by fun_prop : Continuous (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖))).mul
          hfhKM.aemeasurable).aestronglyMeasurable
    refine MeasureTheory.Integrable.mono' hsum hfKm (Filter.Eventually.of_forall fun h => ?_)
    show ‖‖h‖ * fK h‖ ≤ ‖h‖ * |f h - fK h| + ‖h‖ * f h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg h) (hfK.1 h))]
    have hmid : ‖h‖ * (|f h - fK h| + f h) = ‖h‖ * |f h - fK h| + ‖h‖ * f h := by rw [mul_add]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hmid.le
    · have h2 := le_abs_self (fK h - f h)
      have h3 := abs_sub_comm (fK h) (f h)
      linarith
  have hI1 :
    MeasureTheory.Integrable
      (fun h => ((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h) volume :=
    cme_integrable_R m n S hS A fK hfK y hfmomK
  have hI2 :
    MeasureTheory.Integrable
      (fun h => ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h) volume :=
    cme_integrable_R m n S hS A f hf y hfmom
  have hIa := posterior_diff_integrable_R m n S hS A f hf fK hfK y hintW
  have hIb := posterior_integrable_R m n S hS A f hf y hfmom
  -- the difference-of-integrals identity (`MeasureTheory.integral_sub`)
  have hstep1 :
    ∫ h : EuclideanSpace ℝ (Fin n),
        (((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h -
          ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h) ∂volume =
      ∫ h : EuclideanSpace ℝ (Fin n),
          ((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h ∂volume -
        ∫ h : EuclideanSpace ℝ (Fin n),
          ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h ∂volume :=
    MeasureTheory.integral_sub hI1 hI2
  calc
    cmeR m n S hS A fK y - cmeR m n S hS A f y =
        ∫ h : EuclideanSpace ℝ (Fin n),
            ((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h ∂volume -
          ∫ h : EuclideanSpace ℝ (Fin n),
            ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h ∂volume :=
      by
      unfold cmeR
      rfl
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          (((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h -
            ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h) ∂volume :=
      hstep1.symm
    _ =
        ∫ h : EuclideanSpace ℝ (Fin n),
          ((1 / fyPDFR m n S hS A fK y) • ((noiseDensR m n S hS A y h * (fK h - f h)) • h) +
            ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
                (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) •
              ((noiseDensR m n S hS A y h * f h) • h)) ∂volume :=
      by
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      show
        ((noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y) • h -
            ((noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y) • h =
          (1 / fyPDFR m n S hS A fK y) • ((noiseDensR m n S hS A y h * (fK h - f h)) • h) +
            ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
                (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) •
              ((noiseDensR m n S hS A y h * f h) • h)
      have hscal :
        (noiseDensR m n S hS A y h * fK h) / fyPDFR m n S hS A fK y -
            (noiseDensR m n S hS A y h * f h) / fyPDFR m n S hS A f y =
          (1 / fyPDFR m n S hS A fK y) * (noiseDensR m n S hS A y h * (fK h - f h)) +
            ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
                (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) *
              (noiseDensR m n S hS A y h * f h) := by
        field_simp
        ring
      rw [← sub_smul, hscal, add_smul, ← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul]
    _ =
        (1 / fyPDFR m n S hS A fK y) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * (fK h - f h)) • h ∂volume +
          ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
              (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * f h) • h ∂volume :=
      by
      have hIa' :
        MeasureTheory.Integrable
          (fun h => (1 / fyPDFR m n S hS A fK y) • ((noiseDensR m n S hS A y h * (fK h - f h)) • h))
          volume :=
        (MeasureTheory.Integrable.smul (1 / fyPDFR m n S hS A fK y) hIa).congr
          (Filter.Eventually.of_forall fun h => by simp)
      have hIb' :
        MeasureTheory.Integrable
          (fun h =>
            ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
                (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y)) •
              ((noiseDensR m n S hS A y h * f h) • h))
          volume :=
        (MeasureTheory.Integrable.smul
              ((fyPDFR m n S hS A f y - fyPDFR m n S hS A fK y) /
                (fyPDFR m n S hS A fK y * fyPDFR m n S hS A f y))
              hIb).congr
          (Filter.Eventually.of_forall fun h => by simp)
      rw [integral_add hIa' hIb', integral_smul _ _, integral_smul _ _]

/-- **The rectangular main theorem (Track C)**: for `m < n` (underdetermined model
`y = A h + n` with an *arbitrary* observation matrix `A : Matrix (Fin m) (Fin n) ℝ`), and
priors `f^{(K)} → f` converging in the weighted-L¹ sense together with a finite first
moment of the limit prior, the conditional mean estimates `ĥ^{(K)}(y)` converge to `ĥ(y)`
uniformly on every ball in `ℝ^m`. -/
theorem cme_uniform_balls_R
    -- Let m, n be natural numbers.
    (m n : ℕ)
    -- Let S be a matrix in R^{m × m}.
    (S : Matrix (Fin m) (Fin m) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in R^{m × n}.
    (A : Matrix (Fin m) (Fin n) ℝ)
    -- Let fh be a function from R^n to R.
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fh be a PDF.
    (hfhpdf : IsPdf fh)
    -- Let fh have finite first moment.
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * fh h) volume)
    -- For every K, let fhK be a function from R^n to R.
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fhK be a PDF.
    (hfhKpdf : ∀ K, IsPdf (fhK K))
    -- Weighted L¹ convergence of fhK to fh.
    (hw :
      ∀ ε > 0,
        ∃ K₀ : ℕ,
          ∀ K ≥ K₀,
            ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |fh h - fhK K h|) ∂volume < ENNReal.ofReal ε)
    -- Let r > 0 be a radius.
    (r : ℝ) (hr : 0 < r) :
    -- Then we have locally uniform convergence.
    Tendsto
      (fun K =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y‖)
      atTop (nhds 0) := by
  classical
  -- the marginal lower bound for `fh` on the ball
  obtain ⟨m', hm'pos, hmin⟩ := fy_min_pos_R m n S hS A fh hfhpdf r hr
  have h2pi : 0 < (2 * Real.pi) ^ ((m : ℝ) / 2) := by positivity
  have hSqrtpos : 0 < Real.sqrt S.det := Real.sqrt_pos.mpr hS.det_pos
  set c₀ : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2) * Real.sqrt S.det)⁻¹ with hc₀def
  have hc₀pos : 0 < c₀ := inv_pos.mpr (mul_pos h2pi hSqrtpos)
  -- the first moment of the limit prior
  have hMfnneg : 0 ≤ ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume :=
    MeasureTheory.integral_nonneg fun h => mul_nonneg (norm_nonneg _) (hfhpdf.1 h)
  -- the per-unit-`w` envelope
  set M₁ : ℝ := m' / 2 with hM₁def
  have hM₁pos : 0 < M₁ := by linarith
  have hApos : 0 < (1 / M₁) * c₀ := mul_pos (div_pos one_pos hM₁pos) hc₀pos
  have hBnneg : 0 ≤ (c₀ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume) :=
    mul_nonneg (div_nonneg hc₀pos.le (mul_pos hM₁pos hm'pos).le) (mul_nonneg hc₀pos.le hMfnneg)
  set D : ℝ :=
    (1 / M₁) * c₀ +
      (c₀ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume) with
    hDdef
  have hDpos : 0 < D := by linarith [hApos, hBnneg, hDdef]
  -- the machinery: for each `ε' > 0`, eventually the sup is at most `ofReal ε'`
  have hmach :
    ∀ ε' > 0,
      ∀ᶠ K in atTop,
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
            ENNReal.ofReal ‖cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y‖ ≤
          ENNReal.ofReal ε' := by
    intro ε' hε'
    -- the budget: a positive quantity below both `ε' / D` and `m' / (2 * c₀)`
    -- (harmonic-type: `Bud * Bnd / (Bud + Bnd)` avoids `min`, whose API is unusable here)
    set Bud : ℝ := ε' / D with hBuddef
    set Bnd : ℝ := m' / (2 * c₀) with hBnddef
    have hBudpos : 0 < Bud := div_pos hε' hDpos
    have hBndpos : 0 < Bnd := div_pos hm'pos (mul_pos two_pos hc₀pos)
    set ε₂ : ℝ := Bud * Bnd / (Bud + Bnd) with hε₂def
    have hε₂pos : 0 < ε₂ := div_pos (mul_pos hBudpos hBndpos) (add_pos hBudpos hBndpos)
    have hε₂leBud : ε₂ ≤ Bud := by
      rw [hε₂def]
      refine (div_le_iff₀ (add_pos hBudpos hBndpos)).mpr ?_
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hBudpos.le) hBudpos.le
    have hε₂leBnd : ε₂ ≤ Bnd := by
      rw [hε₂def, mul_comm]
      refine (div_le_iff₀ (add_pos hBudpos hBndpos)).mpr ?_
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hBndpos.le) hBndpos.le
    obtain ⟨K₀₁, hK₀₁⟩ := hw ε₂ hε₂pos
    obtain ⟨K₀₂, hK₀₂⟩ := uniform_convergence_fyR m n S hS A fh hfhpdf fhK hfhKpdf hw ε₂ hε₂pos
    filter_upwards [Filter.eventually_ge_atTop (max K₀₁ K₀₂)] with K hK
    have hK₁ : K ≥ K₀₁ := le_trans (le_max_left _ _) hK
    have hK₂ : K ≥ K₀₂ := le_trans (le_max_right _ _) hK
    -- the real weighted bound
    have hwK := hK₀₁ K hK₁
    have hfhm : MeasureTheory.AEStronglyMeasurable fh volume :=
      (integrable_of_isPdf hfhpdf).aestronglyMeasurable
    have hfhKm : MeasureTheory.AEStronglyMeasurable (fhK K) volume :=
      (integrable_of_isPdf (hfhKpdf K)).aestronglyMeasurable
    have hintW : MeasureTheory.Integrable (fun h => (1 + ‖h‖) * |fh h - fhK K h|) volume :=
      weighted_diff_integrable n fh (fhK K) (integrable_of_isPdf hfhpdf)
        (integrable_of_isPdf (hfhKpdf K)) (lt_of_lt_of_le hwK le_top)
    -- the real weighted integral is at most `ε₂`
    have hwReal : ∫ h : EuclideanSpace ℝ (Fin n), (1 + ‖h‖) * |fh h - fhK K h| ∂volume ≤ ε₂ := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun h => mul_nonneg (by positivity) (abs_nonneg _))
          (by fun_prop :
            MeasureTheory.AEStronglyMeasurable (fun h => (1 + ‖h‖) * |fh h - fhK K h|) volume)]
      exact ENNReal.toReal_le_of_le_ofReal (le_of_lt hε₂pos) (le_of_lt hwK)
    have hΔfy :
      ∀ y : EuclideanSpace ℝ (Fin m),
        |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| ≤ c₀ * ε₂ :=
      fun y => hK₀₂ K hK₂ y
    refine iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal ?_
    have hy' : ‖y‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
      exact hy
    have hminy : m' ≤ fyPDFR m n S hS A fh y := hmin y hy'
    have hΔy := hΔfy y
    -- the `f_y^{(K)}` lower bound `M₁ = m'/2`
    have hc₀ε₂le : c₀ * ε₂ ≤ m' / 2 := by
      have h1 : c₀ * ε₂ ≤ c₀ * Bnd := mul_le_mul_of_nonneg_left hε₂leBnd hc₀pos.le
      calc
        c₀ * ε₂ ≤ c₀ * Bnd := h1
        _ = c₀ * (m' / (2 * c₀)) := rfl
        _ = m' / 2 := by field_simp
    have hfyKlb : m' / 2 ≤ fyPDFR m n S hS A (fhK K) y := by
      have h1 :
        fyPDFR m n S hS A fh y - |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| ≤
          fyPDFR m n S hS A (fhK K) y := by
        have hw2 :
          fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y ≤
            |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| :=
          le_abs_self _
        linarith
      linarith [h1, hΔy, hminy, hc₀ε₂le]
    have hfyKpos : 0 < fyPDFR m n S hS A (fhK K) y := lt_of_lt_of_le hM₁pos hfyKlb
    have hfypos : 0 < fyPDFR m n S hS A fh y := lt_of_lt_of_le hm'pos hminy
    have hfyKne : fyPDFR m n S hS A (fhK K) y ≠ 0 := ne_of_gt hfyKpos
    have hfyne : fyPDFR m n S hS A fh y ≠ 0 := ne_of_gt hfypos
    -- the decomposition and the two rates
    have hdec := cme_decomp_R m n S hS A fh hfhpdf (fhK K) (hfhKpdf K) y hfyKne hfyne hfmom hintW
    have hT1 :
      ‖(1 / fyPDFR m n S hS A (fhK K) y) •
            ∫ h : EuclideanSpace ℝ (Fin n),
              (noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h ∂volume‖ ≤
        ε₂ * ((1 / M₁) * c₀) := by
      have hscal : 0 ≤ 1 / fyPDFR m n S hS A (fhK K) y := le_of_lt (div_pos one_pos hfyKpos)
      have hpt :
        ∀ h : EuclideanSpace ℝ (Fin n),
          ‖(noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h‖ ≤
            c₀ * (‖h‖ * |fh h - (fhK K) h|) := by
        intro h
        calc
          ‖(noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h‖ =
              (noiseDensR m n S hS A y h * ‖h‖) * |(fhK K) h - fh h| :=
            by
            rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (le_of_lt (noiseDensR_pos m n S hS A y h))]
            ring
          _ ≤ (c₀ * ‖h‖) * |(fhK K) h - fh h| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (noiseDensR_le_const m n S hS A y h) le_rfl (norm_nonneg _) hc₀pos.le)
              (abs_nonneg ((fhK K) h - fh h))
          _ = c₀ * (‖h‖ * |fh h - (fhK K) h|) := by
            rw [abs_sub_comm ((fhK K) h) (fh h)]
            ring
      have hintAbs : MeasureTheory.Integrable (fun h => ‖h‖ * |fh h - fhK K h|) volume := by
        have habsM :
          MeasureTheory.AEStronglyMeasurable (fun h => ‖h‖ * |fh h - fhK K h|) volume := by fun_prop
        refine MeasureTheory.Integrable.mono' hintW habsM (Filter.Eventually.of_forall fun h => ?_)
        show ‖‖h‖ * |fh h - fhK K h|‖ ≤ (1 + ‖h‖) * |fh h - fhK K h|
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))]
        exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg h]) (abs_nonneg (fh h - fhK K h))
      calc
        ‖(1 / fyPDFR m n S hS A (fhK K) y) •
                ∫ h : EuclideanSpace ℝ (Fin n),
                  (noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h ∂volume‖ =
            (1 / fyPDFR m n S hS A (fhK K) y) *
              ‖∫ h : EuclideanSpace ℝ (Fin n),
                  (noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h ∂volume‖ :=
          by rw [norm_smul, Real.norm_eq_abs, abs_eq_self.mpr hscal]
        _ ≤
            (1 / fyPDFR m n S hS A (fhK K) y) *
              ∫ h : EuclideanSpace ℝ (Fin n),
                ‖(noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h‖ ∂volume :=
          mul_le_mul_of_nonneg_left
            (MeasureTheory.norm_integral_le_integral_norm (μ := volume) (f :=
              fun h : EuclideanSpace ℝ (Fin n) =>
              (noiseDensR m n S hS A y h * ((fhK K) h - fh h)) • h))
            hscal
        _ ≤
            (1 / fyPDFR m n S hS A (fhK K) y) *
              ∫ h : EuclideanSpace ℝ (Fin n), c₀ * (‖h‖ * |fh h - fhK K h|) ∂volume :=
          mul_le_mul_of_nonneg_left
            (integral_mono_of_nonneg (Filter.Eventually.of_forall fun h => norm_nonneg _)
              (MeasureTheory.Integrable.smul c₀ hintAbs)
              (Filter.Eventually.of_forall fun h => hpt h))
            hscal
        _ ≤
            (1 / fyPDFR m n S hS A (fhK K) y) *
              (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * |fh h - fhK K h| ∂volume) :=
          by rw [MeasureTheory.integral_const_mul]
        _ ≤ (1 / M₁) * (c₀ * ε₂) := by
          have h1 : 1 / fyPDFR m n S hS A (fhK K) y ≤ 1 / M₁ :=
            (div_le_div_iff_of_pos_left zero_lt_one hfyKpos hM₁pos).mpr hfyKlb
          have h2 :
            ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * |fh h - fhK K h| ∂volume ≤
              ∫ h : EuclideanSpace ℝ (Fin n), (1 + ‖h‖) * |fh h - fhK K h| ∂volume := by
            have hf2 : 0 ≤ᵐ[volume] (fun h => ‖h‖ * |fh h - fhK K h|) :=
              Filter.Eventually.of_forall fun h => mul_nonneg (norm_nonneg _) (abs_nonneg _)
            have hle2 :
              (fun h => ‖h‖ * |fh h - fhK K h|) ≤ᵐ[volume]
                (fun h => (1 + ‖h‖) * |fh h - fhK K h|) :=
              Filter.Eventually.of_forall fun h =>
                mul_le_mul_of_nonneg_right (by linarith [norm_nonneg h]) (abs_nonneg _)
            exact integral_mono_of_nonneg hf2 hintW hle2
          have hwReal2 : ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * |fh h - fhK K h| ∂volume ≤ ε₂ :=
            le_trans h2 hwReal
          have hcap :
            c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * |fh h - fhK K h| ∂volume ≤ c₀ * ε₂ :=
            mul_le_mul_of_nonneg_left hwReal2 hc₀pos.le
          exact mul_le_mul h1 hcap (by positivity) (le_of_lt (div_pos one_pos hM₁pos))
        _ = ε₂ * ((1 / M₁) * c₀) := by ring
    have hT2 :
      ‖((fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y) /
              (fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y)) •
            ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * fh h) • h ∂volume‖ ≤
        ε₂ * ((c₀ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume)) := by
      have hBpos : 0 < fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y :=
        mul_pos hfyKpos hfypos
      have hJ := posterior_moment_bound_R m n S hS A fh hfhpdf y hfmom
      calc
        ‖((fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y) /
                  (fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y)) •
                ∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * fh h) • h ∂volume‖ =
            |fyPDFR m n S hS A fh y - fyPDFR m n S hS A (fhK K) y| /
                (fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y) *
              ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * fh h) • h ∂volume‖ :=
          by rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hBpos]
        _ ≤
            (c₀ * ε₂ / (fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y)) *
              ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * fh h) • h ∂volume‖ :=
          mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right hBpos).mpr hΔy) (norm_nonneg _)
        _ ≤
            (c₀ * ε₂ / (M₁ * m')) *
              ‖∫ h : EuclideanSpace ℝ (Fin n), (noiseDensR m n S hS A y h * fh h) • h ∂volume‖ :=
          by
          have hBle : M₁ * m' ≤ fyPDFR m n S hS A (fhK K) y * fyPDFR m n S hS A fh y :=
            mul_le_mul hfyKlb hminy hm'pos.le hfyKpos.le
          exact
            mul_le_mul_of_nonneg_right
              ((div_le_div_iff_of_pos_left (mul_pos hc₀pos hε₂pos) hBpos
                    (mul_pos hM₁pos hm'pos)).mpr
                hBle)
              (norm_nonneg _)
        _ ≤ (c₀ * ε₂ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume) :=
          mul_le_mul_of_nonneg_left hJ
            (div_nonneg (le_of_lt (mul_pos hc₀pos hε₂pos)) (le_of_lt (mul_pos hM₁pos hm'pos)))
        _ = ε₂ * ((c₀ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume)) :=
          by ring
    -- the sum
    have hnormle : ‖cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y‖ ≤ ε' := by
      rw [norm_sub_rev, hdec]
      refine le_trans (norm_add_le _ _) ?_
      have hDsplit :
        ε₂ * D =
          ε₂ * ((1 / M₁) * c₀) +
            ε₂ *
              ((c₀ / (M₁ * m')) * (c₀ * ∫ h : EuclideanSpace ℝ (Fin n), ‖h‖ * fh h ∂volume)) := by
        rw [hDdef]; ring
      have hε₂D : ε₂ * D ≤ ε' := by
        -- `ε₂ ≤ Bud = ε' / D`
        have hmin1 : ε₂ ≤ ε' / D := hε₂leBud
        have h2 : ε₂ * D ≤ (ε' / D) * D := mul_le_mul_of_nonneg_right hmin1 (le_of_lt hDpos)
        rw [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h2
        exact h2
      linarith [hT1, hT2, hDsplit, hε₂D]
    exact hnormle
  -- conclude via the Iio-basis helper
  refine
    tendsto_iSup_ofReal_of_eventually_le
      (fun K y => cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y) hmach

/-- Epsilon–delta form of `cme_uniform_balls_R`: for every `ε > 0` there is a threshold
beyond which `‖ĥ^{(K)}(y) − ĥ(y)‖ ≤ ε` holds for all `y` in the ball simultaneously. -/
theorem cme_uniform_balls_eps_R (m n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosDef)
    (A : Matrix (Fin m) (Fin n) ℝ) (fh : EuclideanSpace ℝ (Fin n) → ℝ) (hfhpdf : IsPdf fh)
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * fh h) volume)
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hfhKpdf : ∀ K, IsPdf (fhK K))
    (hw :
      ∀ ε > 0,
        ∃ K₀ : ℕ,
          ∀ K ≥ K₀,
            ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |fh h - fhK K h|) ∂volume <
              ENNReal.ofReal ε)
    (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ,
      ∀ K ≥ K₀,
        ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ‖cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y‖ ≤ ε :=
  tendsto_iSup_norm_eps (fun K y => cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y)
    (cme_uniform_balls_R m n S hS A fh hfhpdf hfmom fhK hfhKpdf hw r hr) ε hε
