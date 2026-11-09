import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped Matrix

-- The custom PDF definition
noncomputable def multivariateGaussianPDF (n : ℕ) (mean : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ) (_ : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let d := x - mean
  let quadForm := (mulVec (Cov⁻¹) d) ⬝ᵥ d
  let normalization := ( (2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (Cov.det) )⁻¹
  normalization * Real.exp (- (quadForm / 2))

theorem integral_norm_gaussian_bounded (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
  (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
  (y : EuclideanSpace ℝ (Fin n)) :
  ∃ (C : ℝ), ∫ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ *
    multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) *
    (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume ≤ C := by
  have h_main : ∃ (C : ℝ), ∫ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ *
    multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) *
    (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume ≤ C := by
    classical
    -- Step 1: The measure with density `multivariateGaussianPDF n 0 S hS` is `multivariateGaussian 0 S`
    have h_density : (volume.withDensity (fun x : EuclideanSpace ℝ (Fin n) ↦ ENNReal.ofReal (multivariateGaussianPDF n (0 : Fin n → ℝ) S hS x))) = ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S := by
      sorry
    \

    -- Step 2: The integral equals the expectation of ‖A⁻¹(y - X)‖ under N(0, S)
    have h_integral_eq : ∫ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) * (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume
      = ∫ (x : EuclideanSpace ℝ (Fin n)), ‖(A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec ((y : Fin n → ℝ) - x)‖ ∂ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S := by
      rw [h_density]
      sorry
    \

    -- Step 3: The pushforward of N(0, S) by x ↦ A⁻¹(y - x) is N(A⁻¹y, A⁻¹S(A⁻¹)ᵀ)
    have h_pushforward : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map (fun x : EuclideanSpace ℝ (Fin n) ↦ WithLp.toLp 2 ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec ((y : Fin n → ℝ) - x))) = ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * (A⁻¹)ᵀ) := by
      sorry
    \

    -- Step 4: The integral equals the first moment of N(A⁻¹y, A⁻¹S(A⁻¹)ᵀ)
    have h_integral_eq_moment : ∫ (x : EuclideanSpace ℝ (Fin n)), ‖(A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec ((y : Fin n → ℝ) - x)‖ ∂ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S = ∫ (z : EuclideanSpace ℝ (Fin n)), ‖z‖ ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * (A⁻¹)ᵀ) := by
      sorry
    \

    -- Step 5: The Gaussian measure N(A⁻¹y, A⁻¹S(A⁻¹)ᵀ) has finite first moment by Fernique's theorem
    have h_finite_moment : ∃ (C : ℝ), ∫ (z : EuclideanSpace ℝ (Fin n)), ‖z‖ ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * (A⁻¹)ᵀ) ≤ C := by
      sorry
    \

    -- Combine all steps
    obtain ⟨C, hC⟩ := h_finite_moment
    have h_final : ∫ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) * (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume ≤ C := by
      calc
        ∫ (h : EuclideanSpace ℝ (Fin n)), ‖h‖ * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ))) * (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume
          = ∫ (x : EuclideanSpace ℝ (Fin n)), ‖(A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec ((y : Fin n → ℝ) - x)‖ ∂ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S := by rw [h_integral_eq]
        _ = ∫ (z : EuclideanSpace ℝ (Fin n)), ‖z‖ ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ).mulVec (y : Fin n → ℝ))) (A⁻¹ * S * (A⁻¹)ᵀ) := by rw [h_integral_eq_moment]
        _ ≤ C := hC
    exact ⟨C, h_final⟩

  exact h_main