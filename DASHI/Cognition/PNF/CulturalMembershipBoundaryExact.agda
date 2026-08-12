module DASHI.Cognition.PNF.CulturalMembershipBoundaryExact where

------------------------------------------------------------------------
-- CULTURAL MEMBERSHIP BOUNDARIES / PROVENANCE-SENSITIVE ACTION
--
-- Mathematical motivation:
--   Michèle Lamont and Virág Molnár,
--   "The Study of Boundaries in the Social Sciences",
--   Annual Review of Sociology 28 (2002), 167-195.
--   DOI: 10.1146/annurev.soc.28.110601.141107
--
-- The cultural worked examples below formalize a claim-scope boundary from the
-- supplied Kendrick/Bad Bunny/Trump-ICE analysis:
--
--   same coarse inside/outside sign does NOT imply the same provenance,
--   boundary purpose, or licensed action.
--
-- The module does not prove any empirical political or cultural proposition;
-- names here identify model roles whose empirical provenance lives outside the
-- theorem kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans; sym)

------------------------------------------------------------------------
-- Keep provenance, membership move, and action projection independent.
------------------------------------------------------------------------

data ProvenanceKind : Set where
  westCoastBlackAmerican
  puertoRicanCaribbean
  stateNational : ProvenanceKind

data MembershipMove : Set where
  protectProvenanceBoundary
  expandMembershipDomain
  enforcePolityBoundary : MembershipMove

data ActionProjection : Set where
  rhetoricalClassification
  culturalDomainExpansion
  stateCoercion : ActionProjection

data CoarseBoundarySign : Set where
  inside outside : CoarseBoundarySign

record BoundaryOperator : Set where
  constructor boundaryOperator
  field
    sign : CoarseBoundarySign
    provenance : ProvenanceKind
    move : MembershipMove
    action : ActionProjection

open BoundaryOperator public

kendrickCulturalBoundary : BoundaryOperator
kendrickCulturalBoundary =
  boundaryOperator
    outside
    westCoastBlackAmerican
    protectProvenanceBoundary
    rhetoricalClassification

badBunnyDomainRepair : BoundaryOperator
badBunnyDomainRepair =
  boundaryOperator
    inside
    puertoRicanCaribbean
    expandMembershipDomain
    culturalDomainExpansion

stateEnforcementBoundary : BoundaryOperator
stateEnforcementBoundary =
  boundaryOperator
    outside
    stateNational
    enforcePolityBoundary
    stateCoercion

------------------------------------------------------------------------
-- Kendrick-like cultural exclusion and state enforcement can share the same
-- coarse sign while remaining action-inequivalent.
------------------------------------------------------------------------

sameCoarseSign :
  sign kendrickCulturalBoundary ≡ sign stateEnforcementBoundary
sameCoarseSign = refl

coarseSignDoesNotDetermineAction :
  action kendrickCulturalBoundary ≡ action stateEnforcementBoundary → ⊥
coarseSignDoesNotDetermineAction ()

coarseSignDoesNotDetermineProvenance :
  provenance kendrickCulturalBoundary ≡ provenance stateEnforcementBoundary → ⊥
coarseSignDoesNotDetermineProvenance ()

------------------------------------------------------------------------
-- Stronger factorisation theorem: there is no single action projection that
-- factors through the coarse inside/outside sign for all three model roles.
-- This is the exact dynamic-sufficiency obstruction behind the statement that
-- two "us/them" classifiers need not license equivalent downstream actions.
------------------------------------------------------------------------

record SignActionFactorisation : Set where
  constructor signActionFactorisation
  field
    coarseAction : CoarseBoundarySign → ActionProjection
    factors :
      (operator : BoundaryOperator) →
      coarseAction (sign operator) ≡ action operator

open SignActionFactorisation public

coarseBoundaryCannotDetermineAllActions :
  SignActionFactorisation → ⊥
coarseBoundaryCannotDetermineAllActions factorisation =
  coarseSignDoesNotDetermineAction
    (trans
      (sym (factors factorisation kendrickCulturalBoundary))
      (factors factorisation stateEnforcementBoundary))

------------------------------------------------------------------------
-- Threatened, planned, and actual enforcement are separate states.
------------------------------------------------------------------------

data EnforcementState : Set where
  threatened planned actual : EnforcementState

threatenedIsNotPlanned : threatened ≡ planned → ⊥
threatenedIsNotPlanned ()

plannedIsNotActual : planned ≡ actual → ⊥
plannedIsNotActual ()

threatenedIsNotActual : threatened ≡ actual → ⊥
threatenedIsNotActual ()

------------------------------------------------------------------------
-- Domain repair: a membership disagreement can be answered by changing the
-- domain of evaluation rather than forcing an existing member to erase local
-- provenance.
------------------------------------------------------------------------

data AmericaDomain : Set where
  nationOnly hemisphericPlural : AmericaDomain

expandAmerica : AmericaDomain → AmericaDomain
expandAmerica nationOnly = hemisphericPlural
expandAmerica hemisphericPlural = hemisphericPlural

badBunnyChangesEvaluationDomain :
  expandAmerica nationOnly ≡ hemisphericPlural
badBunnyChangesEvaluationDomain = refl

expandAmericaIsIdempotent :
  (domain : AmericaDomain) →
  expandAmerica (expandAmerica domain) ≡ expandAmerica domain
expandAmericaIsIdempotent nationOnly = refl
expandAmericaIsIdempotent hemisphericPlural = refl

------------------------------------------------------------------------
-- Healthy pluralism in this finite core means difference is retained while
-- membership can be widened without rewriting provenance.
------------------------------------------------------------------------

record ProvenanceBearingMembership : Set where
  constructor provenanceBearingMembership
  field
    localProvenance : ProvenanceKind
    publicDomain : AmericaDomain

open ProvenanceBearingMembership public

widenMembership : ProvenanceBearingMembership → ProvenanceBearingMembership
widenMembership (provenanceBearingMembership p domain) =
  provenanceBearingMembership p (expandAmerica domain)

wideningPreservesProvenance :
  (member : ProvenanceBearingMembership) →
  localProvenance (widenMembership member) ≡ localProvenance member
wideningPreservesProvenance member = refl

puertoRicanMembershipWitness : ProvenanceBearingMembership
puertoRicanMembershipWitness =
  provenanceBearingMembership puertoRicanCaribbean nationOnly

puertoRicanDifferenceRetainedUnderExpansion :
  localProvenance (widenMembership puertoRicanMembershipWitness)
  ≡ puertoRicanCaribbean
puertoRicanDifferenceRetainedUnderExpansion = refl
