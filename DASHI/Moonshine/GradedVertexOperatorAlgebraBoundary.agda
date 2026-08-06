module DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition,
-- University Lecture Series 10, American Mathematical Society, 1998.
-- The AMS edition is identified by ISBN/product metadata; no DOI is asserted.
--
-- Richard E. Borcherds,
-- "Monstrous moonshine and monstrous Lie superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Separate a graded representation from a graded vertex operator algebra.
-- The existing Moonshine.GradedRepresentation API supplies group actions and
-- grade-wise traces, but not vacuum, conformal vector, vertex modes,
-- lower-truncation, creation, translation, Jacobi or Virasoro laws.
--
-- This module states those VOA obligations explicitly, adds exact graded-trace
-- coefficient laws, and proves the identity coefficient equals the grade
-- dimension whenever the identity-trace law is supplied.  It does not
-- construct V^natural, prove rationality/C2-cofiniteness, modularity of
-- characters, or the genus-zero theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.GradedRepresentation as GR

record GradedVertexOperatorAlgebra (K : Set) : Setω where
  field
    Homogeneous : Nat → Set
    TotalCarrier : Set
    injectGrade : ∀ grade → Homogeneous grade → TotalCarrier

    zero : TotalCarrier
    add : TotalCarrier → TotalCarrier → TotalCarrier
    scalarMultiply : K → TotalCarrier → TotalCarrier

    vacuum : Homogeneous 0
    conformalVector : Homogeneous 2
    vertexMode : TotalCarrier → Int → TotalCarrier → TotalCarrier
    translationOperator : TotalCarrier → TotalCarrier

    additiveLinearLaws : Set
    scalarLinearLaws : Set
    lowerTruncation : Set
    vacuumFieldIdentity : Set
    creationIdentity : Set
    translationCovariance : Set
    jacobiIdentity : Set
    virasoroRelations : Set
    gradingCompatibility : Set

open GradedVertexOperatorAlgebra public

record GradedDimensionData (K : Set)
    (voa : GradedVertexOperatorAlgebra K) : Set₁ where
  field
    finiteDimension : Nat → Nat
    dimensionCertified : ∀ grade → Set

record VOACharacterData (K : Set)
    (voa : GradedVertexOperatorAlgebra K) : Set₁ where
  field
    centralCharge : K
    coefficient : Nat → K
    characterSeriesCarrier : Set
    coefficientIsShiftedGradeDimension : ∀ grade → Set

record VOAWithGroupAction (G K : Set) : Setω where
  field
    group : GR.Group G
    voa : GradedVertexOperatorAlgebra K
    gradedRepresentation : GR.GradedRepresentation G K group
    homogeneousCarrierAgreement : ∀ grade → Set
    groupActionPreservesVacuum : Set
    groupActionPreservesConformalVector : Set
    groupActionIntertwinesVertexModes : Set

open VOAWithGroupAction public

record ExactGradedTrace
    {G K : Set}
    (actionData : VOAWithGroupAction G K) : Setω where
  field
    traceCoefficient : G → Nat → K
    coefficientIsRepresentationTrace : ∀ element grade →
      traceCoefficient element grade
      ≡ GR.trace
          (GR.grade (gradedRepresentation actionData) grade)
          (GR.action
            (GR.grade (gradedRepresentation actionData) grade)
            element)

open ExactGradedTrace public

record IdentityTraceDimensionLaw
    {G K : Set}
    (actionData : VOAWithGroupAction G K)
    (traceData : ExactGradedTrace actionData) : Set₁ where
  field
    gradeDimensionAsScalar : Nat → K
    identityEndTraceIsDimension : ∀ grade →
      GR.trace
        (GR.grade (gradedRepresentation actionData) grade)
        (GR.identityEnd
          (GR.grade (gradedRepresentation actionData) grade))
      ≡ gradeDimensionAsScalar grade

open IdentityTraceDimensionLaw public

identityTraceCoefficientIsDimension :
  ∀ {G K} (actionData : VOAWithGroupAction G K)
    (traceData : ExactGradedTrace actionData)
    (dimensionLaw : IdentityTraceDimensionLaw actionData traceData)
    grade →
  traceCoefficient traceData (GR.identity (group actionData)) grade
  ≡ gradeDimensionAsScalar dimensionLaw grade
identityTraceCoefficientIsDimension actionData traceData dimensionLaw grade =
  let
    representation = GR.grade (gradedRepresentation actionData) grade
  in
  transEquality
    (coefficientIsRepresentationTrace traceData
      (GR.identity (group actionData)) grade)
    (transEquality
      (congTrace representation
        (GR.actionIdentity representation))
      (identityEndTraceIsDimension dimensionLaw grade))
  where
    transEquality : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transEquality refl second = second

    congTrace : ∀ {G K : Set}
      (representation : GR.FiniteDimensionalRepresentation G K (group actionData))
      {left right} → left ≡ right →
      GR.trace representation left ≡ GR.trace representation right
    congTrace representation refl = refl

data MoonshineAlgebraicLayer : Set where
  gradedRepresentationLayer : MoonshineAlgebraicLayer
  gradedVOALayer : MoonshineAlgebraicLayer
  monsterVOAConstructionLayer : MoonshineAlgebraicLayer
  modularCharacterLayer : MoonshineAlgebraicLayer
  genusZeroLayer : MoonshineAlgebraicLayer

gradedRepresentationIsNotVOA :
  gradedRepresentationLayer ≡ gradedVOALayer → ⊥
gradedRepresentationIsNotVOA ()

voaAxiomsDoNotByThemselvesGiveGenusZero :
  gradedVOALayer ≡ genusZeroLayer → ⊥
voaAxiomsDoNotByThemselvesGiveGenusZero ()
