import Mathlib

open MeasureTheory Matrix Topology Filter
open scoped Matrix

noncomputable def multivariateGaussianPDF (n : ℕ) (m : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (_ : C.PosDef) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let d := x - m
  let quadForm := (mulVec (C⁻¹) d) ⬝ᵥ d
  let normalization := ( (2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (C.det) )⁻¹
  normalization * Real.exp (- (quadForm / 2))

lemma gaussian_affine_pdf_integral_eq_one
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A.det)
    (Sigma : Matrix (Fin N) (Fin N) ℝ)
    (hSigma : Sigma.PosDef)
    (y : EuclideanSpace ℝ (Fin N))
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : f = multivariateGaussianPDF N (fun _ => 0) Sigma hSigma) :
    (∫ h : EuclideanSpace ℝ (Fin N),
      f (y - WithLp.toLp 2 (A *ᵥ h.ofLp)) /
        Real.sqrt (Matrix.det (A⁻¹ * A⁻¹.transpose)) ∂volume) = 1 := by
  sorry

lemma gaussian_affine_pdf_second_moment
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A.det)
    (Sigma : Matrix (Fin N) (Fin N) ℝ)
    (hSigma : Sigma.PosDef)
    (y : EuclideanSpace ℝ (Fin N))
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : f = multivariateGaussianPDF N (fun _ => 0) Sigma hSigma) :
    (∫ h : EuclideanSpace ℝ (Fin N),
      ‖h‖ ^ 2 *
        (f (y - WithLp.toLp 2 (A *ᵥ h.ofLp)) /
          Real.sqrt (Matrix.det (A⁻¹ * A⁻¹.transpose))) ∂volume)
      =
      ‖A⁻¹.mulVec y‖ ^ 2 +
        Matrix.trace (A⁻¹ * Sigma * A⁻¹.transpose) := by
  sorry

theorem gaussian_integral_bound
    {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : IsUnit A.det)
    (Sigma : Matrix (Fin N) (Fin N) ℝ)
    (hSigma : Sigma.PosDef)
    (y : EuclideanSpace ℝ (Fin N))
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : f = multivariateGaussianPDF N (fun _ => 0) Sigma hSigma) :
    (∫ h : EuclideanSpace ℝ (Fin N),
         ‖h‖ * f (y - WithLp.toLp 2 (A *ᵥ h.ofLp)) ∂volume
       ≤
       Real.sqrt (Matrix.det (A⁻¹ * A⁻¹.transpose)) *
       Real.sqrt (
         ‖A⁻¹.mulVec y‖ ^ 2 +
         Matrix.trace (A⁻¹ * Sigma * A⁻¹.transpose)
       )) := by
  sorry
