module DASHI.Cognition.CharlieKirkAssassinationEvidenceSpeculationBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CHARLIE KIRK ASSASSINATION: EVIDENCE / SPECULATION BOUNDARY
--
-- The owner records the strongly sourced physical-event layer separately from
-- post-event conspiracy/speculation surfaces.  It does not adjudicate the
-- criminal case beyond currently public official/court status.
------------------------------------------------------------------------

data KirkEvidenceKind : Set where
  fatalShootingAtUVU : KirkEvidenceKind
  rooftopShooterVideo : KirkEvidenceKind
  boltActionRifleRecovered : KirkEvidenceKind
  rooftopTraceEvidence : KirkEvidenceKind
  suspectInCustody : KirkEvidenceKind
  prosecutionCasePending : KirkEvidenceKind
  explodingMicrophoneTheory : KirkEvidenceKind
  foreignIntelligenceHitTheory : KirkEvidenceKind
  falseFlagDiversionTheory : KirkEvidenceKind
  patsyTheory : KirkEvidenceKind
  tpusaInsideJobTheory : KirkEvidenceKind

record KirkEvidenceReceipt : Set where
  constructor kirk-evidence-receipt
  field
    kind : KirkEvidenceKind
    sourceIdentity : String
    boundedFinding : String
    eventFactPaid : Bool
    theoryExistencePaid : Bool
    theoryTruthPaid : Bool
open KirkEvidenceReceipt public

shootingReceipt : KirkEvidenceReceipt
shootingReceipt = kirk-evidence-receipt
  fatalShootingAtUVU
  "Utah DPS / FBI, 2025-09-10"
  "Charlie Kirk was fatally shot while speaking at a Turning Point USA event at Utah Valley University."
  true false false

rooftopReceipt : KirkEvidenceReceipt
rooftopReceipt = kirk-evidence-receipt
  rooftopShooterVideo
  "FBI Utah Valley Shooting Updates"
  "FBI-released video shows a shooter leaving the roof area after the shooting."
  true false false

rifleReceipt : KirkEvidenceReceipt
rifleReceipt = kirk-evidence-receipt
  boltActionRifleRecovered
  "FBI Salt Lake City, 2025-09-11"
  "The FBI reported recovering a high-powered bolt-action rifle in the wooded flight path from the shooting scene."
  true false false

traceReceipt : KirkEvidenceReceipt
traceReceipt = kirk-evidence-receipt
  rooftopTraceEvidence
  "FBI Utah Valley Shooting Updates"
  "FBI reported shoe, forearm and palm impressions from the rooftop scene."
  true false false

custodyReceipt : KirkEvidenceReceipt
custodyReceipt = kirk-evidence-receipt
  suspectInCustody
  "FBI / Utah court reporting"
  "A suspect is in custody and has been identified by investigators in the pending Utah criminal case."
  true false false

pendingReceipt : KirkEvidenceReceipt
pendingReceipt = kirk-evidence-receipt
  prosecutionCasePending
  "Utah court / Reuters 2026"
  "The criminal case remains subject to adversarial court process; prosecution allegations and defense challenges are not converted into final adjudicated facts here."
  true false false

explodingMicReceipt : KirkEvidenceReceipt
explodingMicReceipt = kirk-evidence-receipt
  explodingMicrophoneTheory
  "post-event online speculation"
  "An exploding-microphone theory circulated after the assassination. Its existence is paid; no primary evidence used here establishes it."
  false true false

foreignIntelReceipt : KirkEvidenceReceipt
foreignIntelReceipt = kirk-evidence-receipt
  foreignIntelligenceHitTheory
  "post-event online/political speculation"
  "Claims of a foreign-intelligence assassination circulated after Kirk's death; current sourced event evidence used here does not establish such a plot."
  false true false

falseFlagReceipt : KirkEvidenceReceipt
falseFlagReceipt = kirk-evidence-receipt
  falseFlagDiversionTheory
  "post-event online speculation"
  "Claims that the assassination was staged or timed to divert attention from Epstein disclosures circulated online; existence does not establish truth."
  false true false

patsyReceipt : KirkEvidenceReceipt
patsyReceipt = kirk-evidence-receipt
  patsyTheory
  "post-event alternative-media speculation"
  "Claims that the charged suspect is a patsy or smokescreen circulate independently of the official case; this owner records the claim surface only."
  false true false

insideJobReceipt : KirkEvidenceReceipt
insideJobReceipt = kirk-evidence-receipt
  tpusaInsideJobTheory
  "post-event online speculation"
  "Claims implicating TPUSA leadership or Kirk's family are not promoted absent primary evidence."
  false true false

record KirkEvidenceBoundary : Set where
  constructor kirk-evidence-boundary
  field
    rifleAttackPhysicalLayerPaid : Bool
    conspiracyTheoryExistencePaid : Bool
    explodingMicTruthPaid : Bool
    foreignIntelligenceHitPaid : Bool
    falseFlagPaid : Bool
    patsyTheoryPaid : Bool
    tpusaInsideJobPaid : Bool
open KirkEvidenceBoundary public

canonicalKirkEvidenceBoundary : KirkEvidenceBoundary
canonicalKirkEvidenceBoundary = kirk-evidence-boundary
  true true false false false false false

data CapabilityPrecedentImpliesCaseAttribution : Set where
data TimingImpliesCausation : Set where
data PoliticalConflictImpliesAssassinationMotive : Set where
data OnlineAnomalyImpliesForensicContradiction : Set where

capabilityDoesNotCreateAttribution : CapabilityPrecedentImpliesCaseAttribution → ⊥
capabilityDoesNotCreateAttribution ()

timingDoesNotCreateCausation : TimingImpliesCausation → ⊥
timingDoesNotCreateCausation ()

politicalConflictDoesNotCreateMotive : PoliticalConflictImpliesAssassinationMotive → ⊥
politicalConflictDoesNotCreateMotive ()

onlineAnomalyDoesNotCreateForensicContradiction : OnlineAnomalyImpliesForensicContradiction → ⊥
onlineAnomalyDoesNotCreateForensicContradiction ()
