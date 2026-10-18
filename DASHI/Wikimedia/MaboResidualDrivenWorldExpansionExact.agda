module DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

-- Canonical parents. This module is deliberately a thin parity owner: PNF,
-- Ibrahim coverage policy, Wikimedia review/disambiguation, and context
-- persistence remain owned by their existing modules.
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact
import DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact
import DASHI.Wikimedia.PredicateNormalFormWikipediaQidBridgeExact
import DASHI.Wikimedia.SensibLawSourceUnitReviewHandoffExact
import DASHI.Wikimedia.SensibLawBoundaryArtifactMorphismExact
import DASHI.Wikimedia.MaboReviewedContextFederationExact

------------------------------------------------------------------------
-- Runtime parity coordinates
------------------------------------------------------------------------

slrRepository : String
slrRepository = "chboishabba/slr"

slrBranch : String
slrBranch = "agent/mabo-context-federation-v1"

slrWorldExpansionSourceHead : String
slrWorldExpansionSourceHead = "b8a62b0f92f9d791414111a2c3b899e8536f241d"

targetNovelObjects : Nat
targetNovelObjects = 100

targetNovelObjectsIs100 : targetNovelObjects ≡ 100
targetNovelObjectsIs100 = refl

------------------------------------------------------------------------
-- Residual-indexed producer policy.
------------------------------------------------------------------------

data ResidualClass : Set where
  legalResidual : ResidualClass
  identityResidual : ResidualClass
  contextResidual : ResidualClass
  provenanceResidual : ResidualClass
  otherResidual : ResidualClass

data ProducerLane : Set where
  governedLegal : ProducerLane
  wikidataIdentity : ProducerLane
  wikipediaContext : ProducerLane
  sourceSpecificProvenance : ProducerLane
  otherProducer : ProducerLane

preferredLane : ResidualClass → ProducerLane
preferredLane legalResidual = governedLegal
preferredLane identityResidual = wikidataIdentity
preferredLane contextResidual = wikipediaContext
preferredLane provenanceResidual = sourceSpecificProvenance
preferredLane otherResidual = otherProducer

legalLanePreferredForLegalResidual : preferredLane legalResidual ≡ governedLegal
legalLanePreferredForLegalResidual = refl

identityLanePreferredForIdentityResidual : preferredLane identityResidual ≡ wikidataIdentity
identityLanePreferredForIdentityResidual = refl

contextLanePreferredForContextResidual : preferredLane contextResidual ≡ wikipediaContext
contextLanePreferredForContextResidual = refl

------------------------------------------------------------------------
-- World-expansion boundary.
------------------------------------------------------------------------

record WorldExpansionBoundary : Set where
  constructor worldExpansionBoundary
  field
    targetIsNovelObjectCardinality : Bool
    hopDepthIsNotTarget : Bool
    legalFirstIsResidualIndexed : Bool
    legalFirstMeansLegalOnly : Bool
    firstLinkControlsSemantics : Bool
    reachabilityCreatesAdmission : Bool
    qidCreatesAuthority : Bool
    admissionCreatesClaimTruth : Bool
    explicitDisambiguationRequired : Bool
    explicitReviewRequired : Bool
    ibrahimActsAsCoveragePolicy : Bool

open WorldExpansionBoundary public

canonicalWorldExpansionBoundary : WorldExpansionBoundary
canonicalWorldExpansionBoundary =
  worldExpansionBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    true
    true
    true

targetIsNovelObjectCardinalityTrue :
  targetIsNovelObjectCardinality canonicalWorldExpansionBoundary ≡ true
targetIsNovelObjectCardinalityTrue = refl

hopDepthIsNotTargetTrue : hopDepthIsNotTarget canonicalWorldExpansionBoundary ≡ true
hopDepthIsNotTargetTrue = refl

legalFirstIsResidualIndexedTrue :
  legalFirstIsResidualIndexed canonicalWorldExpansionBoundary ≡ true
legalFirstIsResidualIndexedTrue = refl

legalFirstMeansLegalOnlyFalse :
  legalFirstMeansLegalOnly canonicalWorldExpansionBoundary ≡ false
legalFirstMeansLegalOnlyFalse = refl

firstLinkControlsSemanticsFalse :
  firstLinkControlsSemantics canonicalWorldExpansionBoundary ≡ false
firstLinkControlsSemanticsFalse = refl

reachabilityCreatesAdmissionFalse :
  reachabilityCreatesAdmission canonicalWorldExpansionBoundary ≡ false
reachabilityCreatesAdmissionFalse = refl

qidCreatesAuthorityFalse : qidCreatesAuthority canonicalWorldExpansionBoundary ≡ false
qidCreatesAuthorityFalse = refl

admissionCreatesClaimTruthFalse :
  admissionCreatesClaimTruth canonicalWorldExpansionBoundary ≡ false
admissionCreatesClaimTruthFalse = refl

explicitDisambiguationRequiredTrue :
  explicitDisambiguationRequired canonicalWorldExpansionBoundary ≡ true
explicitDisambiguationRequiredTrue = refl

explicitReviewRequiredTrue : explicitReviewRequired canonicalWorldExpansionBoundary ≡ true
explicitReviewRequiredTrue = refl

ibrahimActsAsCoveragePolicyTrue :
  ibrahimActsAsCoveragePolicy canonicalWorldExpansionBoundary ≡ true
ibrahimActsAsCoveragePolicyTrue = refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data TraversalDepthDeterminesNovelObjectCount : Set where
data GlobalProducerOrderDeterminesResidualPriority : Set where
data LegalFirstImpliesLegalOnly : Set where
data FirstLinkDeterminesSemanticFrontier : Set where
data ReachabilityEqualsAdmission : Set where
data QidEqualsLegalAuthority : Set where
data AdmissionEqualsClaimTruth : Set where

traversalDepthDoesNotDetermineNovelObjectCount :
  TraversalDepthDeterminesNovelObjectCount → ⊥
traversalDepthDoesNotDetermineNovelObjectCount ()

globalProducerOrderDoesNotDetermineResidualPriority :
  GlobalProducerOrderDeterminesResidualPriority → ⊥
globalProducerOrderDoesNotDetermineResidualPriority ()

legalFirstDoesNotImplyLegalOnly : LegalFirstImpliesLegalOnly → ⊥
legalFirstDoesNotImplyLegalOnly ()

firstLinkDoesNotDetermineSemanticFrontier : FirstLinkDeterminesSemanticFrontier → ⊥
firstLinkDoesNotDetermineSemanticFrontier ()

reachabilityDoesNotEqualAdmission : ReachabilityEqualsAdmission → ⊥
reachabilityDoesNotEqualAdmission ()

qidDoesNotEqualLegalAuthority : QidEqualsLegalAuthority → ⊥
qidDoesNotEqualLegalAuthority ()

admissionDoesNotEqualClaimTruth : AdmissionEqualsClaimTruth → ⊥
admissionDoesNotEqualClaimTruth ()

------------------------------------------------------------------------
-- Interpretation
--
-- PNF/world residual -> Ibrahim coverage/frontier policy -> residual-indexed
-- producer selection -> acquisition -> PNF/disambiguation -> explicit review
-- -> world admission.  The current runtime target is 100 novel admitted
-- objects; traversal depth is only an observed property of the resulting world.
------------------------------------------------------------------------
