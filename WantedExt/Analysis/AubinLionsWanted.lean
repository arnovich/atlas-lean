/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Aubin–Lions compactness, finite time exponent

A compact embedding `X → B` and continuous embedding `B → Y` turn uniform
`Lᵖ(X)` bounds and `L¹(Y)` bounds on distributional time derivatives into
subsequential strong convergence in `Lᵖ(B)`, for `1 ≤ p < ∞`.
No reflexivity is required in this version. The derivative identity is tested
against smooth scalar functions supported strictly inside the time interval.
Source: J. Simon, Compact sets in the space Lp(0,T;B), Ann. Mat. Pura Appl.
146 (1987), Corollary 4, https://doi.org/10.1007/BF01762360.
-/
@[expose] public section
open scoped NNReal ENNReal
open MeasureTheory Set Filter
open scoped Topology
namespace AubinLions

/-- The finite-exponent Aubin–Lions–Simon compactness criterion. -/
theorem_wanted subsequence_converges
    {X B Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (i : X →L[ℝ] B) (j : B →L[ℝ] Y)
    (hi : Function.Injective i) (hj : Function.Injective j)
    (hcompact : IsCompactOperator i) (T p : ℝ) (hT : 0 < T) (hp : 1 ≤ p)
    (u : ℕ → ℝ → X) (v : ℕ → ℝ → Y)
    (hu : ∀ n, MemLp (u n) (ENNReal.ofReal p) (volume.restrict (Ioc 0 T)))
    (hv : ∀ n, Integrable (v n) (volume.restrict (Ioc 0 T)))
    (hweak : ∀ n (φ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo 0 T →
      (∫ t in Ioc 0 T, deriv φ t • j (i (u n t))) =
        -(∫ t in Ioc 0 T, φ t • v n t))
    (hbound : ∃ C : ℝ≥0, ∀ n,
      eLpNorm (u n) (ENNReal.ofReal p) (volume.restrict (Ioc 0 T)) ≤ C ∧
      eLpNorm (v n) 1 (volume.restrict (Ioc 0 T)) ≤ C) :
    ∃ (l : ℕ → ℕ) (w : ℝ → B), StrictMono l ∧
      MemLp w (ENNReal.ofReal p) (volume.restrict (Ioc 0 T)) ∧
      Tendsto (fun n => eLpNorm (fun t => i (u (l n) t) - w t)
        (ENNReal.ofReal p) (volume.restrict (Ioc 0 T))) atTop (𝓝 0)
end AubinLions
