/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Nagumo's invariance theorem

The closed set need not be convex or have smooth boundary. Tangency uses
positive time increments (the Bouligand contingent cone), not the two-sided
`tangentConeAt ℝ`. Invariance is asserted only while a solution exists.
Source: M. Nagumo, Über die Lage der Integralkurven gewöhnlicher
Differentialgleichungen, Proc. Phys.-Math. Soc. Japan 24 (1942), 551–559.
See also Ghorbal et al., A Hierarchy of Proof Rules for Checking Positive
Invariance, https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf.
-/
@[expose] public section
open Set
namespace Nagumo

/-- Positive-time contingent tangency at a point of an arbitrary closed set. -/
def IsContingent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) (x v : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
    ∃ h : ℝ, 0 < h ∧ h < δ ∧ ∃ y ∈ s, ‖y - x - h • v‖ ≤ ε * h

/-- Nagumo's criterion for a locally Lipschitz autonomous vector field. -/
theorem_wanted invariant_iff_contingent {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E) (hf : LocallyLipschitz f) (s : Set E) (hs : IsClosed s) :
    (∀ x ∈ s, IsContingent s x (f x)) ↔
      ∀ (T : ℝ), 0 < T → ∀ u : ℝ → E,
        (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f (u t)) (Icc 0 T) t) →
        u 0 ∈ s → ∀ t ∈ Icc 0 T, u t ∈ s
end Nagumo
