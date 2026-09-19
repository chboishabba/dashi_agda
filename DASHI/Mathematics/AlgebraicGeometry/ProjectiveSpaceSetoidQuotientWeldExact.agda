module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceSetoidQuotientWeldExact where

------------------------------------------------------------------------
-- PROJECTIVE RESCALING SETOID -> LITERAL CP^n QUOTIENT INTERFACE
--
-- DASHI already owns a non-cubical quotient-by-setoid authority surface.
-- This module specializes it to homogeneous-vector rescaling.  Once an exact
-- rescaling equivalence and a quotient surface that reflects equivalence are
-- supplied, the earlier LiteralComplexProjectiveSpace object is constructed
-- definitionally.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω; lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.QuotientSetoidSurface as Quotient
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP

projectiveRescalingSetoid :
  ∀ {field dimension} →
  Quotient.IsEquivalence
    (CP.ProjectiveRescaling
      {field = field}
      {dimension = dimension}) →
  Quotient.SetoidSurface lzero lzero
projectiveRescalingSetoid {field} {dimension} equivalence = record
  { Quotient.Carrier = CP.HomogeneousVector field dimension
  ; Quotient._≈_ = CP.ProjectiveRescaling
  ; Quotient.isEquivalence = equivalence
  }

record ExactProjectiveRescalingQuotient
    (field : CP.ComplexFieldPresentation)
    (dimension : Nat) : Setω where
  field
    rescalingEquivalence :
      Quotient.IsEquivalence
        (CP.ProjectiveRescaling
          {field = field}
          {dimension = dimension})

    quotient :
      Quotient.SetoidQuotientSurface
        (projectiveRescalingSetoid rescalingEquivalence)
        lzero

    quotientReflectsRescaling :
      (left right : CP.HomogeneousVector field dimension) →
      Quotient.quotientClass quotient left
      ≡ Quotient.quotientClass quotient right →
      CP.ProjectiveRescaling left right

open ExactProjectiveRescalingQuotient public

literalProjectiveSpaceFromQuotient :
  ∀ {field dimension} →
  ExactProjectiveRescalingQuotient field dimension →
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

literalProjectiveClassSound :
  ∀ {field dimension}
    (exact : ExactProjectiveRescalingQuotient field dimension)
    (left right : CP.HomogeneousVector field dimension) →
  CP.ProjectiveRescaling left right →
  CP.classOf (literalProjectiveSpaceFromQuotient exact) left
  ≡ CP.classOf (literalProjectiveSpaceFromQuotient exact) right
literalProjectiveClassSound exact left right rescaling =
  Quotient.quotientSound (quotient exact) rescaling

literalProjectiveClassReflects :
  ∀ {field dimension}
    (exact : ExactProjectiveRescalingQuotient field dimension)
    (left right : CP.HomogeneousVector field dimension) →
  CP.classOf (literalProjectiveSpaceFromQuotient exact) left
  ≡ CP.classOf (literalProjectiveSpaceFromQuotient exact) right →
  CP.ProjectiveRescaling left right
literalProjectiveClassReflects exact =
  quotientReflectsRescaling exact

record ProjectiveSpaceSetoidQuotientWeldBoundary : Set where
  constructor projective-space-setoid-quotient-weld-boundary
  field
    genericQuotientAuthorityReused : Bool
    setoidQuotientToLiteralProjectiveSpaceCompilerPaid : Bool
    concreteRescalingEquivalencePaid : Bool
    concreteProjectiveQuotientInhabitantPaid : Bool
    smoothProjectiveIdentificationPaid : Bool
    singularDeRhamComparisonPaid : Bool
    generalHodgeConjecturePaid : Bool

canonicalProjectiveSpaceSetoidQuotientWeldBoundary :
  ProjectiveSpaceSetoidQuotientWeldBoundary
canonicalProjectiveSpaceSetoidQuotientWeldBoundary =
  projective-space-setoid-quotient-weld-boundary
    true true false false false false false
