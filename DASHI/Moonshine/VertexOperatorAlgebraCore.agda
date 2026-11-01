module DASHI.Moonshine.VertexOperatorAlgebraCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.JCoefficientCharacterBridge as JCB

------------------------------------------------------------------------
-- Minimal but honest VOA core.
--
-- This file does not claim construction of the moonshine module V^natural.
-- It introduces the typed owner that the existing graded-representation and
-- j-coefficient lanes were previously missing.

record GradedModule : Setω where
  field
    Scalar : Set
    Carrier : Set
    gradePiece : Nat → Set
    includeGrade : ∀ n → gradePiece n → Carrier
    zero : Carrier
    _+_ : Carrier → Carrier → Carrier
    _·_ : Scalar → Carrier → Carrier

open GradedModule public

record VertexOperatorData (M : GradedModule) : Setω where
  field
    vacuum : GradedModule.Carrier M
    conformalVector : GradedModule.Carrier M
    mode :
      GradedModule.Carrier M →
      ℤ →
      GradedModule.Carrier M →
      GradedModule.Carrier M
    translation :
      GradedModule.Carrier M →
      GradedModule.Carrier M

open VertexOperatorData public

record LowerTruncation
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    truncationBound :
      GradedModule.Carrier M →
      GradedModule.Carrier M →
      Nat
    modeVanishesAboveBound :
      (a b : GradedModule.Carrier M) → Set

record VacuumAxioms
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    vacuumFieldIdentity : Set
    creationProperty : Set
    translationKillsVacuum : Set

record TranslationAxiom
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    translationCovariance : Set

record LocalityAxiom
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    localityExponent :
      GradedModule.Carrier M →
      GradedModule.Carrier M →
      Nat
    mutuallyLocal :
      (a b : GradedModule.Carrier M) → Set

record JacobiAxiom
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    borcherdsJacobiIdentity : Set

record ConformalAxioms
  (M : GradedModule)
  (Y : VertexOperatorData M) : Setω where
  field
    virasoroModes : ℤ → GradedModule.Carrier M → GradedModule.Carrier M
    centralCharge : GradedModule.Scalar M
    virasoroCommutator : Set
    gradingFromL0 : Set
    translationIsLMinusOne : Set

record VertexOperatorAlgebra : Setω where
  field
    gradedModule : GradedModule
    vertexData : VertexOperatorData gradedModule
    lowerTruncation : LowerTruncation gradedModule vertexData
    vacuumAxioms : VacuumAxioms gradedModule vertexData
    translationAxiom : TranslationAxiom gradedModule vertexData
    localityAxiom : LocalityAxiom gradedModule vertexData
    jacobiAxiom : JacobiAxiom gradedModule vertexData
    conformalAxioms : ConformalAxioms gradedModule vertexData

open VertexOperatorAlgebra public

------------------------------------------------------------------------
-- Automorphism and graded-character owners.

record VOAGroupAction
  (G : Set)
  (group : GR.Group G)
  (V : VertexOperatorAlgebra) : Setω where
  field
    act : G → GradedModule.Carrier (gradedModule V) → GradedModule.Carrier (gradedModule V)
    preservesVacuum : Set
    preservesConformalVector : Set
    preservesModes : Set
    actionIdentity : Set
    actionComposition : Set

record VOAGradedCharacter
  (G K : Set)
  (group : GR.Group G)
  (V : VertexOperatorAlgebra) : Setω where
  field
    gradedRepresentation : GR.GradedRepresentation G K group
    action : VOAGroupAction G group V
    characterMatchesVOAGrades : Set

------------------------------------------------------------------------
-- Moonshine-facing bridge.
--
-- Existing exact character-table and first-coefficient work remains separate
-- authority. This bridge only states the additional VOA structure and
-- compatibility needed before one may promote a moonshine-module claim.

record MoonshineVOABridge
  (G K : Set)
  (group : GR.Group G) : Setω where
  field
    voa : VertexOperatorAlgebra
    monsterGradedRepresentation : GR.GradedRepresentation G K group
    monsterAction : VOAGroupAction G group voa
    gradedCharacter : VOAGradedCharacter G K group voa
    firstCoefficientBridge : JCB.FirstMoonshineCoefficientBridge

    vacuumGradeIsZero : Set
    conformalVectorGradeIsTwo : Set
    firstPositiveGradeMatches196883 : Set
    gradedTraceMatchesMcKayThompson : Set
    hauptmodulProperty : Set
    genusZeroProperty : Set

------------------------------------------------------------------------
-- Honest promotion boundary.

record MoonshineVOAPromotionBoundary : Setω where
  field
    moonshineVOAConstructed : Set
    monsterActionConstructed : Set
    twistedModulesConstructed : Set
    modularityProved : Set
    genusZeroProved : Set
    noPromotionWithoutAllFive : Set
