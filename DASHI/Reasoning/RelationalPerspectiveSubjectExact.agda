module DASHI.Reasoning.RelationalPerspectiveSubjectExact where

------------------------------------------------------------------------
-- RELATIONAL PERSPECTIVE SUBJECT NON-COLLAPSE
--
-- DASHI CONTRIBUTION
--
-- Cross-weld existing Lacan/Irigaray/four-view/argument-response owners into
-- one bounded subject-level firewall.  Source authors motivate vocabulary;
-- the finite non-identifications below are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LacanIrigaray
import DASHI.Governance.SexedHistoricalProductiveDialecticalFibreJoinExact as Join
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response

data PerspectiveSubject : Set where
  selfSubject : PerspectiveSubject
  otherSubject : PerspectiveSubject

data PerspectiveModel : Set where
  selfModel : PerspectiveModel
  modelOfOther : PerspectiveModel

data TransparentAccess : Set where
data ModelIsSubject : Set where
data OtherIsGeometricAntipodeOfSelf : Set where
data CounterpositionIsLogicalNegation : Set where
data IntegrationIsHomogenisation : Set where
data CoConstitutionOwnsOtherMeaning : Set where
data HighPerspectiveMultiplicityIsTotalSelfRepresentation : Set where

modelIsNotSubject : ModelIsSubject → ⊥
modelIsNotSubject ()

perspectiveModelDoesNotCreateTransparentAccess :
  TransparentAccess → ⊥
perspectiveModelDoesNotCreateTransparentAccess ()

otherIsNotGeometricAntipode :
  OtherIsGeometricAntipodeOfSelf → ⊥
otherIsNotGeometricAntipode ()

counterpositionIsNotLogicalNegation :
  CounterpositionIsLogicalNegation → ⊥
counterpositionIsNotLogicalNegation ()

integrationIsNotHomogenisation :
  IntegrationIsHomogenisation → ⊥
integrationIsNotHomogenisation ()

coConstitutionDoesNotOwnOtherMeaning :
  CoConstitutionOwnsOtherMeaning → ⊥
coConstitutionDoesNotOwnOtherMeaning ()

highPerspectiveMultiplicityDoesNotCreateTotalSelfRepresentation :
  HighPerspectiveMultiplicityIsTotalSelfRepresentation → ⊥
highPerspectiveMultiplicityDoesNotCreateTotalSelfRepresentation ()

existingIrigarayLacanNonRelabelling =
  LacanIrigaray.noTernaryRelabellingPreservesGrammar

existingProductiveJoinNotGuaranteedSynthesis =
  Join.productiveJoinIsNotGuaranteedByDialecticalOpposition

existingCoConstitutionOwnershipFirewall =
  Join.coConstitutionDoesNotCreateOwnershipOfOtherMeaning

existingAlternativeExplanationNotAntipode =
  Response.alternativeExplanationIsNotGeometricAntipode

record RelationalPerspectiveSubjectBoundary : Set where
  constructor relational-perspective-subject-boundary
  field
    selfModelEqualsSelf : Bool
    modelOfOtherEqualsOther : Bool
    otherEqualsAntipodeOfSelf : Bool
    counterpositionEqualsLogicalNegation : Bool
    integrationEqualsHomogenisation : Bool
    coConstitutionMeansOwnership : Bool
    manyPerspectiveModelsGiveTransparentAccess : Bool
    manyPerspectiveModelsGiveTotalSelfRepresentation : Bool

canonicalRelationalPerspectiveSubjectBoundary :
  RelationalPerspectiveSubjectBoundary
canonicalRelationalPerspectiveSubjectBoundary =
  relational-perspective-subject-boundary
    false false false false false false false false
