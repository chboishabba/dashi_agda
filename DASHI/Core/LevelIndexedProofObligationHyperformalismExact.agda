module DASHI.Core.LevelIndexedProofObligationHyperformalismExact where

------------------------------------------------------------------------
-- LEVEL-INDEXED PROOF-OBLIGATION HYPERFABRIC
--
-- Required-axis support is local to a declared comparison level.  A required
-- obligation can be positively/negatively/conflict/missing *and* can separately
-- be applicable, no-typed-meet, outside scope, or hidden by a collapsed
-- projection.  The support square therefore does not determine applicability.
--
-- This is the proof-obligation analogue of the repo's fibre/hyperfabric rule:
-- keep the whole carrier and its provenance, project to the current local
-- question, carry residual/obstruction, and re-open or re-chart when a richer
-- comparison surface is admitted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.IntersectionalNonFactorability as NF

record ObligationCoordinate
    (Claim Axis Level Provenance : Set) : Set where
  constructor obligationCoordinate
  field
    claim : Claim
    axis : Axis
    level : Level
    provenance : Provenance

open ObligationCoordinate public

record ObligationStalk
    (Claim Axis Level Provenance : Set) : Set where
  constructor obligationStalk
  field
    coordinate : ObligationCoordinate Claim Axis Level Provenance
    evidence : Support.SupportSquare
    applicability : Transport.Applicability

open ObligationStalk public

ResolvedPositiveHere :
  ∀ {Claim Axis Level Provenance} →
  ObligationStalk Claim Axis Level Provenance → Set
ResolvedPositiveHere stalk =
  applicability stalk ≡ Transport.applicableHere
  ×
  Support.ResolvedPositive (evidence stalk)

ResolvedNegativeHere :
  ∀ {Claim Axis Level Provenance} →
  ObligationStalk Claim Axis Level Provenance → Set
ResolvedNegativeHere stalk =
  applicability stalk ≡ Transport.applicableHere
  ×
  Support.ResolvedNegative (evidence stalk)

record RequiredObligationFamily
    (Claim Axis Level Provenance : Set) : Set₁ where
  constructor requiredObligationFamily
  field
    currentClaim : Claim
    currentLevel : Level
    stalkAt : Axis → ObligationStalk Claim Axis Level Provenance
    Required : Axis → Set

open RequiredObligationFamily public

record RequiredObligationsResolved
    {Claim Axis Level Provenance : Set}
    (family : RequiredObligationFamily Claim Axis Level Provenance) : Set₁ where
  constructor requiredObligationsResolved
  field
    resolveRequired :
      (axis : Axis) →
      Required family axis →
      ResolvedPositiveHere (stalkAt family axis)

open RequiredObligationsResolved public

------------------------------------------------------------------------
-- Applicability is not recoverable from the support square alone.
------------------------------------------------------------------------

data DemoClaim : Set where
  demoClaim : DemoClaim

data DemoAxis : Set where
  demoAxis : DemoAxis

data DemoLevel : Set where
  level0 level1 : DemoLevel

data DemoProvenance : Set where
  retainedSource : DemoProvenance

positiveApplicable : ObligationStalk DemoClaim DemoAxis DemoLevel DemoProvenance
positiveApplicable =
  obligationStalk
    (obligationCoordinate demoClaim demoAxis level0 retainedSource)
    (Support.supportSquare true false)
    Transport.applicableHere

positiveOutOfScope : ObligationStalk DemoClaim DemoAxis DemoLevel DemoProvenance
positiveOutOfScope =
  obligationStalk
    (obligationCoordinate demoClaim demoAxis level0 retainedSource)
    (Support.supportSquare true false)
    Transport.outsideCurrentComparisonScope

sameEvidenceDifferentApplicability :
  evidence positiveApplicable ≡ evidence positiveOutOfScope
sameEvidenceDifferentApplicability = refl

applicableIsNotOutsideScope :
  applicability positiveApplicable ≡ applicability positiveOutOfScope → ⊥
applicableIsNotOutsideScope ()

supportSquareCannotDetermineApplicability :
  ∀ (decode : Support.SupportSquare → Transport.Applicability) →
  (decode (evidence positiveApplicable) ≡ applicability positiveApplicable)
  ×
  (decode (evidence positiveOutOfScope) ≡ applicability positiveOutOfScope) →
  ⊥
supportSquareCannotDetermineApplicability decode both =
  applicableIsNotOutsideScope
    (trans
      (sym (proj₁ both))
      (trans
        (cong decode sameEvidenceDifferentApplicability)
        (proj₂ both)))

------------------------------------------------------------------------
-- Level transport preserves claim/axis/provenance while changing level.
------------------------------------------------------------------------

record ObligationLevelTransport
    {Claim Axis Level Provenance : Set}
    (before after : ObligationStalk Claim Axis Level Provenance) : Set where
  constructor obligationLevelTransport
  field
    claimPreserved :
      claim (coordinate before) ≡ claim (coordinate after)
    axisPreserved :
      axis (coordinate before) ≡ axis (coordinate after)
    provenancePreserved :
      provenance (coordinate before) ≡ provenance (coordinate after)

open ObligationLevelTransport public

positiveReopenedAtNextLevel :
  ObligationStalk DemoClaim DemoAxis DemoLevel DemoProvenance
positiveReopenedAtNextLevel =
  obligationStalk
    (obligationCoordinate demoClaim demoAxis level1 retainedSource)
    (Support.supportSquare true false)
    Transport.applicableHere

scopeToNextLevelTransport :
  ObligationLevelTransport positiveOutOfScope positiveReopenedAtNextLevel
scopeToNextLevelTransport =
  obligationLevelTransport refl refl refl

scopeTransportKeepsClaim :
  claim (coordinate positiveOutOfScope)
  ≡ claim (coordinate positiveReopenedAtNextLevel)
scopeTransportKeepsClaim =
  claimPreserved scopeToNextLevelTransport

scopeTransportKeepsProvenance :
  provenance (coordinate positiveOutOfScope)
  ≡ provenance (coordinate positiveReopenedAtNextLevel)
scopeTransportKeepsProvenance =
  provenancePreserved scopeToNextLevelTransport

------------------------------------------------------------------------
-- Flattening applicability away is a concrete non-factorability defect.
------------------------------------------------------------------------

data FineDecisionState : Set where
  currentlyApplicable currentlyOutOfScope : FineDecisionState

data FlatEvidenceSurface : Set where
  positiveSurface : FlatEvidenceSurface

data LocalDecision : Set where
  decideHere rechartBeforeDecision : LocalDecision

flattenEvidence : FineDecisionState → FlatEvidenceSurface
flattenEvidence currentlyApplicable = positiveSurface
flattenEvidence currentlyOutOfScope = positiveSurface

fineDecision : FineDecisionState → LocalDecision
fineDecision currentlyApplicable = decideHere
fineDecision currentlyOutOfScope = rechartBeforeDecision

flattenCollision :
  flattenEvidence currentlyApplicable ≡ flattenEvidence currentlyOutOfScope
flattenCollision = refl

decisionDiffersAcrossCollision :
  fineDecision currentlyApplicable ≡ fineDecision currentlyOutOfScope → ⊥
decisionDiffersAcrossCollision ()

flatEvidenceCannotDetermineLevelAwareDecision :
  NF.NonFactorabilityWitness flattenEvidence fineDecision
flatEvidenceCannotDetermineLevelAwareDecision =
  NF.nonFactorabilityWitness
    currentlyApplicable
    currentlyOutOfScope
    flattenCollision
    decisionDiffersAcrossCollision

noFlatEvidenceFactorisationRecoversLevelAwareDecision :
  NF.FactorsThrough flattenEvidence fineDecision →
  ⊥
noFlatEvidenceFactorisationRecoversLevelAwareDecision =
  NF.witnessRulesOutEveryFlatFactorisation
    flatEvidenceCannotDetermineLevelAwareDecision

record LevelIndexedProofObligationBoundary : Set where
  constructor levelIndexedProofObligationBoundary
  field
    evidenceDeterminesApplicability : Bool
    noTypedMeetMeansFalseAtEveryLevel : Bool
    scopeExceededErasesClaim : Bool
    transportMayRetainClaimAndProvenance : Bool
    aggregateEvidenceCanRecoverErasedApplicability : Bool

canonicalLevelIndexedProofObligationBoundary :
  LevelIndexedProofObligationBoundary
canonicalLevelIndexedProofObligationBoundary =
  levelIndexedProofObligationBoundary false false false true false
