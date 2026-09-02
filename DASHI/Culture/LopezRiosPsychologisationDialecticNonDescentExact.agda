module DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact where

open import DASHI.Core.Prelude

import DASHI.Core.ContextualDialecticRoleExact as Role
import DASHI.Reasoning.DialecticInvariantGeometry as Dialectic
import DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- PSYCHOLOGISATION AS A NON-DESCENT / REIFICATION FAILURE
--
-- Source claim boundary:
--   Lopez-Rios motivates the distinction between structural determination and
--   psychologising individualisation. The exact carrier, observers, collision
--   witness, and non-descent theorem below are DASHI extensions.
--
-- Repo cross-pollination:
--   ContextualDialecticRoleExact already proves that a role may vary with the
--   comparison frame and therefore cannot, in general, be replaced by an
--   intrinsic entity role. DialecticInvariantGeometry independently keeps
--   stance-indexed observations, common invariant, and projection distinct.
------------------------------------------------------------------------

data StructuralFrame : Set where
  exploitativeLabourFrame
  nonExploitativeLabourFrame
  : StructuralFrame

data Person : Set where
  samePerson : Person

data IndividualObservation : Set where
  distressObserved : IndividualObservation

data StructuralDependency : Set where
  exploitativeDependency
  otherDependency
  : StructuralDependency

individualObservation : StructuralFrame → Person → IndividualObservation
individualObservation exploitativeLabourFrame samePerson = distressObserved
individualObservation nonExploitativeLabourFrame samePerson = distressObserved

structuralDependency : StructuralFrame → Person → StructuralDependency
structuralDependency exploitativeLabourFrame samePerson = exploitativeDependency
structuralDependency nonExploitativeLabourFrame samePerson = otherDependency

sameIndividualObservation :
  individualObservation exploitativeLabourFrame samePerson ≡
  individualObservation nonExploitativeLabourFrame samePerson
sameIndividualObservation = refl

structuralDependenciesDiffer :
  structuralDependency exploitativeLabourFrame samePerson ≡
  structuralDependency nonExploitativeLabourFrame samePerson → ⊥
structuralDependenciesDiffer ()

------------------------------------------------------------------------
-- A consumer descends through the individual observer iff equal observations
-- force equal consumer-relevant structural dependencies.
------------------------------------------------------------------------

IndividualObserverSupportsStructuralDescent : Set
IndividualObserverSupportsStructuralDescent =
  (left right : StructuralFrame) →
  (person : Person) →
  individualObservation left person ≡ individualObservation right person →
  structuralDependency left person ≡ structuralDependency right person

individualObserverDoesNotSupportStructuralDescent :
  IndividualObserverSupportsStructuralDescent → ⊥
individualObserverDoesNotSupportStructuralDescent descends =
  structuralDependenciesDiffer
    (descends
      exploitativeLabourFrame
      nonExploitativeLabourFrame
      samePerson
      sameIndividualObservation)

------------------------------------------------------------------------
-- Psychologisation is not identified with psychological description itself.
-- It is the stronger move of treating an individual observation as sufficient
-- for a structural causal consumer despite a live collision witness.
------------------------------------------------------------------------

record PsychologisingCollapse : Set where
  constructor psychologising-collapse
  field
    claimedDescent : IndividualObserverSupportsStructuralDescent

open PsychologisingCollapse public

psychologisingCollapseBlocked : PsychologisingCollapse → ⊥
psychologisingCollapseBlocked collapse =
  individualObserverDoesNotSupportStructuralDescent (claimedDescent collapse)

record PsychologicalDescription : Set where
  constructor psychological-description
  field
    frame : StructuralFrame
    person : Person
    observation : IndividualObservation
    observationCorrect : observation ≡ individualObservation frame person

canonicalPsychologicalDescription : PsychologicalDescription
canonicalPsychologicalDescription =
  psychological-description
    exploitativeLabourFrame
    samePerson
    distressObserved
    refl

------------------------------------------------------------------------
-- Dialectical-role cross-pollination.
-- The same entity occupies different roles under different frames; importing
-- that role into an intrinsic property is already generically blocked by the
-- repo's contextual-role theorem.
------------------------------------------------------------------------

structuralRoleSystem : Role.ContextualRoleSystem StructuralFrame Person
Role.roleIn structuralRoleSystem exploitativeLabourFrame samePerson = Role.counterRole
Role.roleIn structuralRoleSystem nonExploitativeLabourFrame samePerson = Role.initialRole

structuralRoleChanges : Role.RoleChangeWitness structuralRoleSystem
structuralRoleChanges =
  Role.role-change-witness
    samePerson
    exploitativeLabourFrame
    nonExploitativeLabourFrame
    (λ ())

noIntrinsicIndividualRoleExplainsBothStructuralFrames :
  (intrinsic : Person → Role.DialecticRole) →
  ((frame : StructuralFrame) (person : Person) →
    Role.roleIn structuralRoleSystem frame person ≡ intrinsic person) →
  ⊥
noIntrinsicIndividualRoleExplainsBothStructuralFrames =
  Role.roleChangeBlocksIntrinsicRole structuralRoleChanges

------------------------------------------------------------------------
-- Retain the source atlas and dialectic projection boundary explicitly.
------------------------------------------------------------------------

sourceAtlasRetained : Sources.lopezRiosSourceAtlas ≡ Sources.lopezRiosSourceAtlas
sourceAtlasRetained = refl

dialecticProjectionBoundaryRetained :
  {X : Set} →
  Dialectic.ProjectionAlgebra X →
  Dialectic.ProjectionAlgebra X
dialecticProjectionBoundaryRetained projection = projection

------------------------------------------------------------------------
-- No-promotion boundary.
------------------------------------------------------------------------

data PsychologicalDescriptionImpliesPsychologisation : Set where
data SameDistressImpliesSameStructuralCause : Set where
data LopezRiosStatedThisExactNonDescentTheorem : Set where

psychologicalDescriptionDoesNotByItselfMeanPsychologisation :
  PsychologicalDescriptionImpliesPsychologisation → ⊥
psychologicalDescriptionDoesNotByItselfMeanPsychologisation ()

sameDistressDoesNotLicenseSameStructuralCause :
  SameDistressImpliesSameStructuralCause → ⊥
sameDistressDoesNotLicenseSameStructuralCause ()

nonDescentTheoremIsDASHIExtension :
  LopezRiosStatedThisExactNonDescentTheorem → ⊥
nonDescentTheoremIsDASHIExtension ()

record LopezRiosPsychologisationDialecticBoundary : Set where
  constructor lopez-rios-psychologisation-dialectic-boundary
  field
    sameIndividualObservationCanHideStructuralDifference : Bool
    structuralConsumerNeedNotDescendThroughIndividualObserver : Bool
    psychologicalDescriptionAloneIsPsychologisation : Bool
    contextualDialecticRoleMayVaryWithStructuralFrame : Bool
    dialecticRoleIsIntrinsicIndividualProperty : Bool
    exactNonDescentTheoremAttributedToLopezRios : Bool

canonicalLopezRiosPsychologisationDialecticBoundary :
  LopezRiosPsychologisationDialecticBoundary
canonicalLopezRiosPsychologisationDialecticBoundary =
  lopez-rios-psychologisation-dialectic-boundary
    true true false true false false
