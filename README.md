# CME Lean

This is a Lean 4 (Mathlib) formalization of **Theorem 2** of the paper

> M. Koller, B. Fesl, N. Turan, and W. Utschick, "An Asymptotically MSE-Optimal
> Estimator Based on Gaussian Mixture Models," *IEEE Transactions on Signal
> Processing*, 2022.

[IEEE Explore](https://ieeexplore.ieee.org/document/9842343)
[arXiv](https://arxiv.org/abs/2112.12499)

The theorem establishes **locally uniform convergence** of the conditional mean
estimates (CMEs): for the linear Gaussian measurement model `y = A h + n` with
invertible `A`, the CMEs computed from a sequence of prior densities converging
uniformly to a continuous prior converge to the true CME, uniformly on every
closed ball in `ℝ^n`.

## Verify / Build
```console
lake build
```

## Main Results

All proofs and definitions are contained in [Main.lean](./Main.lean).

### Theorem for Invertible Matrix A

The main result for invertible matrices is called `main_theorem` in [Main.lean](./Main.lean):
```Lean
theorem main_theorem
    -- Let n be a natural number.
    (n : ℕ)
    -- Let S be a matrix in ℝ^{n × n}.
    (S : Matrix (Fin n) (Fin n) ℝ)
    -- Let S be positive definite. (S is the noise covariance matrix.)
    (hS : S.PosDef)
    -- Let A be a matrix in ℝ^{n × n}.
    (A : Matrix (Fin n) (Fin n) ℝ)
    -- Let A be invertible.
    (hA : IsUnit A.det)
    -- Let fh be a function from ℝ^n to ℝ.
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fh be a PDF.
    (hfhpdf : IsPdf fh)
    -- Let fh be continuous.
    (hfhcont : Continuous fh)
    -- For every K, let fhK be a function from ℝ^n to ℝ.
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
          atTop (nhds 0)
```

The maybe more familiar epsilon-delta formulation of locally uniform convergence is stated in the corollary `cme_uniform_balls_eps`.

Pointwise convergence of the CME is an immediate consequence of the main theorem and can be found as `cme_pointwise_convergence`.

A generalization of the main theorem to arbitrary compact sets is given by `cme_uniform_compact` (with epsilon-delta formulation `cme_uniform_compact_eps`).

### Theorem for General Matrix A

The main result for general matrices is called `cme_uniform_balls_R` in [Main.lean](./Main.lean):
```Lean
theorem cme_uniform_balls_R
    -- Let m, n be natural numbers.
    (m n : ℕ)
    -- Let S be a matrix in ℝ^{m × m}.
    (S : Matrix (Fin m) (Fin m) ℝ)
    -- Let S be positive definite.
    (hS : S.PosDef)
    -- Let A be a matrix in ℝ^{m × n}.
    (A : Matrix (Fin m) (Fin n) ℝ)
    -- Let fh be a function from ℝ^n to ℝ.
    (fh : EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fh be a PDF.
    (hfhpdf : IsPdf fh)
    -- Let fh have finite first moment.
    (hfmom : MeasureTheory.Integrable (fun h : EuclideanSpace ℝ (Fin n) => ‖h‖ * fh h) volume)
    -- For every K, let fhK be a function from ℝ^n to ℝ.
    (fhK : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    -- Let fhK be a PDF.
    (hfhKpdf : ∀ K, IsPdf (fhK K))
    -- Let fhK converge to fh in the weighted L¹ sense.
    (hw :
      ∀ ε > 0,
        ∃ K₀ : ℕ,
          ∀ K ≥ K₀,
            ∫⁻ h : EuclideanSpace ℝ (Fin n), ENNReal.ofReal ((1 + ‖h‖) * |fh h - fhK K h|) ∂volume <
              ENNReal.ofReal ε)
    -- Let r > 0 be a radius.
    (r : ℝ) (hr : 0 < r) :
    -- Then we have locally uniform convergence.
    Tendsto
      (fun K =>
        ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r,
          ENNReal.ofReal ‖cmeR m n S hS A fh y - cmeR m n S hS A (fhK K) y‖)
      atTop (nhds 0)
```

## Miscellaneous Notes

```console
lean-fmt format
lake env lean AxiomCheck.lean
```
