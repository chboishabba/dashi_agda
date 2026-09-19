module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceSetoidQuotientWeldExact where

------------------------------------------------------------------------
-- EXACT PROJECTIVE RESCALING SETOID -> LITERAL CP^n QUOTIENT INTERFACE
------------------------------------------------------------------------

open import Agda.Primitive using (Setω; lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.QuotientSetoidSurface as Quotient
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP

projectiveRescalingEquivalence :
  ∀ {field} →
  (laws : CP.ProjectiveMultiplicativeLaws field) →
  {dimension : Nat} →
  Quotient.IsEquivalence
    (CP.ProjectiveRescaling
      {field = field}
      {dimension = dimension})
projectiveRescalingEquivalence laws = record
  { Quotient.refl≈ = CP.rescalingReflexive laws
  ; Quotient.sym≈ = CP.rescalingSymmetric laws
  ; Quotient.trans≈ = CP.rescalingTransitive laws
  }

projectiveRescalingSetoid :
  ∀ {field} →
  (laws : CP.ProjectiveMultiplicativeLaws field) →
  {dimension : Nat} →
  Quotient.SetoidSurface lzero lzero
projectiveRescalingSetoid laws = record
  { Quotient.Carrier = CP.HomogeneousVector _ _
  ; Quotient._≈_ = CP.ProjectiveRescaling
  ; Quotient.isEquivalence =
      projectiveRescalingEquivalence laws
  }

record ExactProjectiveRescalingQuotient
    (field : CP.ComplexFieldPresentation)
    (laws : CP.ProjectiveMultiplicativeLaws field)
    (dimension : Nat) : Setω where
  field
    quotient :
      Quotient.SetoidQuotientSurface
        (projectiveRescalingSetoid laws {dimension})
        lzero

    quotientReflectsRescaling :
      (left right : CP.HomogeneousVector field dimension) →
      Quotient.quotientClass quotient left
      ≡ Quotient.quotientClass quotient right →
      CP.ProjectiveRescaling left right

open ExactProjectiveRescalingQuotient public

literalProjectiveSpaceFromQuotient :
  ∀ {field laws dimension} →
  ExactProjectiveRescalingQuotient field laws dimension →
  CP.LiteralComplexProjectiveSpace field dimension
literalProjectiveSpaceFromQuotient exact = record
  { CP.Point = Quotient.QuotientCarrier (quotient exact)
  ; CP.classOf = Quotient.quotientClass (quotient exact)
  ; CP.sameClassIffRescaling =
      quotientReflectsRescaling exact
  ; CP.rescalingGivesSameClass =
      λ left right rescaling →
        Quotient.quotientSound (quotient exact) rescaling
  }

record ProjectiveSpaceSetoidQuotientWeldBoundary : Set where
  constructor projective-space-setoid-quotient-weld-boundary
  field
    genericQuotientAuthorityReused : Bool
    literalRescalingSemanticsPaid : Bool
    concreteRescalingEquivalencePaid : Bool
    setoidQuotientToLiteralProjectiveSpaceCompilerPaid : Bool
    concreteProjectiveQuotientInhabitantPaid : Bool
    smoothProjectiveIdentificationPaid : Bool
    singularDeRhamComparisonPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveSpaceSetoidQuotientWeldBoundary :
  ProjectiveSpaceSetoidQuotientWeldBoundary
canonicalProjectiveSpaceSetoidQuotientWeldBoundary =
  projective-space-setoid-quotient-weld-boundary
    true true true true false false false false
