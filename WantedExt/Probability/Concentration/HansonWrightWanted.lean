/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hanson–Wright concentration

The dimension-independent constant uses the sub-Gaussian MGF convention.
The two scales are the squared Hilbert–Schmidt norm and Euclidean operator
norm, respectively. A nonzero operator avoids division by zero; the zero
operator has an identically zero centered quadratic form.
Source: Rudelson and Vershynin (2013), Theorem 1.1,
https://arxiv.org/abs/1306.2872. Equivalent sub-Gaussian norm conventions
change only the universal constant.
-/
@[expose] public section
open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace HansonWright

/-- A dimension-independent two-sided quadratic-form tail bound. -/
theorem_wanted concentration :
    ∃ c : ℝ, 0 < c ∧ ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (n : ℕ) (X : Fin n → Ω → ℝ) (K : ℝ≥0),
      0 < K → iIndepFun X μ →
      (∀ i, HasSubgaussianMGF (X i) (K ^ 2) μ) →
      ∀ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        A ≠ 0 → ∀ t : ℝ, 0 < t →
          let Q := fun ω =>
            inner ℝ (WithLp.toLp 2 (fun i => X i ω))
              (A (WithLp.toLp 2 (fun i => X i ω)))
          μ.real {ω | t ≤ |Q ω - ∫ z, Q z ∂μ|} ≤
            2 * Real.exp (-c * min
              (t ^ 2 / ((K : ℝ) ^ 4 *
                ∑ i, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ ^ 2))
              (t / ((K : ℝ) ^ 2 * ‖A‖)))
end HansonWright
