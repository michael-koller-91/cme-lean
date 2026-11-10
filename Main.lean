module

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.Jacobian

open MeasureTheory Matrix Topology Filter ProbabilityTheory
open scoped Matrix

noncomputable def multivariateGaussianPDF (n : ℕ) (mean : Fin n → ℝ) (Cov : Matrix (Fin n) (Fin n) ℝ) (_ : Cov.PosDef) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let d := x - mean
  let quadForm := (mulVec (Cov⁻¹) d) ⬝ᵥ d
  let normalization := ( (2 * Real.pi) ^ ((n : ℝ) / 2) * Real.sqrt (Cov.det) )⁻¹
  normalization * Real.exp (- (quadForm / 2))

theorem integral_norm_gaussian_bounded
  (n : ℕ)
  (S : Matrix (Fin n) (Fin n) ℝ)
  (hS : S.PosDef)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (hA : IsUnit A.det)
  (y : EuclideanSpace ℝ (Fin n))
  :
  ∃ (C : ℝ), ∫ (h : EuclideanSpace ℝ (Fin n)),
    ‖h‖
    * multivariateGaussianPDF n (0 : Fin n → ℝ) S hS (WithLp.toLp 2 ((y : Fin n → ℝ) - A.mulVec (h : Fin n → ℝ)))
    * (1 / Real.sqrt ( (A⁻¹ * A⁻¹ᵀ).det )) ∂volume
    ≤ C
  := by
  sorry
