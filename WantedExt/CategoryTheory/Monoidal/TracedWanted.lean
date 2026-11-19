/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Batteries.Util.ProofWanted
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Traced symmetric monoidal categories

The trace structure records naturality, dinaturality, both vanishing axioms,
superposing and yanking, with associators and unitors explicit. The wanted
construction equips a symmetric rigid (compact closed) category with this
structure; no trace is asserted to exist on an arbitrary symmetric category.
Source: Joyal, Street and Verity, Traced monoidal categories (1996),
https://doi.org/10.1017/S0305004100074338, specialized to the symmetric case.
-/
@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory
open scoped MonoidalCategory

/-- A trace satisfying the Joyal–Street–Verity symmetric trace axioms. -/
structure SymmetricTrace (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] where
  /-- Feedback over the right tensor factor. -/
  trace : ∀ {X Y U : C}, (X ⊗ U ⟶ Y ⊗ U) → (X ⟶ Y)
  /-- Naturality in the input and output objects. -/
  naturality : ∀ {X X' Y Y' U : C} (f : X ⊗ U ⟶ Y ⊗ U)
    (g : X' ⟶ X) (h : Y ⟶ Y'),
    trace ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) = g ≫ trace f ≫ h
  /-- Sliding a morphism around the feedback loop. -/
  dinaturality : ∀ {X Y U V : C} (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U),
    trace (f ≫ (𝟙 Y ⊗ₘ g)) = trace ((𝟙 X ⊗ₘ g) ≫ f)
  /-- Tracing over the tensor unit removes the unitors. -/
  vanishing_unit : ∀ {X Y : C} (f : X ⊗ 𝟙_ C ⟶ Y ⊗ 𝟙_ C),
    trace f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom
  /-- Tracing two factors agrees with tracing them successively. -/
  vanishing_tensor : ∀ {X Y U V : C} (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)),
    trace f = trace (trace ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv))
  /-- A morphism on an untouched factor may be superposed. -/
  superposing : ∀ {X Y U W Z : C} (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z),
    trace ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) = g ⊗ₘ trace f
  /-- Feedback through the symmetry is the identity. -/
  yanking : ∀ X : C, trace (β_ X X).hom = 𝟙 X

/-- The canonical trace induced by duality in a compact closed category. -/
def_wanted symmetricTraceOfRigid (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] [RigidCategory C] :
    SymmetricTrace C
end CategoryTheory
