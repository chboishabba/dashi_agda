module DASHI.Physics.Motors.SmithFilsingerSourceEdgeAdmissionBidiExact where

-- Source-first audit of the four FM edges in the existing canonical
-- Artifacts/smith-filsinger/source_indexed_transcript_diagram_values_20261122.json.
-- Original previous-user speech says: accessible midpoint, capacitor across
-- chosen coil, common positive diode branches, return to "midpoint/Earth".
-- ALL FOUR original FM graph edges have proven_continuity=false.
-- This source distinction must not be converted into physical wire equality.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.SmithFilsingerWindingOwnerReturnCutBidiExact as Return
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Original

data NarratedEdge : Set where
  accessibleNSTMidpoint : NarratedEdge
  capacitorAcrossSelectedCoil : NarratedEdge
  diodePositiveOutputsGanged : NarratedEdge
  rectifiedReturnToMidpointOrEarth : NarratedEdge

data EvidenceState : Set where
  sourceNarratedNoPinProof : EvidenceState
  conditionalElectricalCompletion : EvidenceState
  verifiedSameOriginalPinContinuity : EvidenceState

-- Audit exactly the four original FM source-index edges, not arbitrary
-- secondary speculation. A later authenticated video may update status.
originalFMEvidence : NarratedEdge → EvidenceState
originalFMEvidence accessibleNSTMidpoint = sourceNarratedNoPinProof
originalFMEvidence capacitorAcrossSelectedCoil = sourceNarratedNoPinProof
originalFMEvidence diodePositiveOutputsGanged = sourceNarratedNoPinProof
originalFMEvidence rectifiedReturnToMidpointOrEarth = sourceNarratedNoPinProof

originalFMNotVerified :
  (e : NarratedEdge) →
  originalFMEvidence e ≡ verifiedSameOriginalPinContinuity → ⊥
originalFMNotVerified accessibleNSTMidpoint ()
originalFMNotVerified capacitorAcrossSelectedCoil ()
originalFMNotVerified diodePositiveOutputsGanged ()
originalFMNotVerified rectifiedReturnToMidpointOrEarth ()

-- A conditional circuit completion is not an observational upgrade.
-- Source-typed owners carry their own obligation for same-original pins.
data ProposedWinding : Set where
  entireNSTSecondary halfNSTSecondary separateResonator : ProposedWinding

data ProposedReturn : Set where
  wiredMidpoint capacitiveDisplacementReturn noExteriorReturn : ProposedReturn

-- All models satisfy the same four narrated-only edges by construction.
-- This models the *absence of a uniquely inferred original wiring*.
data SpeechSignature : Set where
  accessibleMidpointFourDiodesCapReturnWords : SpeechSignature

speechSignature : ProposedWinding → SpeechSignature
speechSignature entireNSTSecondary = accessibleMidpointFourDiodesCapReturnWords
speechSignature halfNSTSecondary = accessibleMidpointFourDiodesCapReturnWords
speechSignature separateResonator = accessibleMidpointFourDiodesCapReturnWords

fullNotHalf : entireNSTSecondary ≡ halfNSTSecondary → ⊥
fullNotHalf ()

fullNotSeparate : entireNSTSecondary ≡ separateResonator → ⊥
fullNotSeparate ()

noUniqueWindingFromFourSpeechEdges :
  (decode : SpeechSignature → ProposedWinding) →
  ((w : ProposedWinding) → decode (speechSignature w) ≡ w) → ⊥
noUniqueWindingFromFourSpeechEdges decode agreement =
  fullNotHalf
    (trans (sym (agreement entireNSTSecondary))
           (agreement halfNSTSecondary))

-- Physically validating a particular pin equality is a separate
-- source witness. Nothing here constructs that evidence or picks a
-- physical winding from historical source words.
record AdmissionWitness : Set₁ where
  field
    sameOriginalReel : Set
    reelWitness : sameOriginalReel
    originalCircuit : Circuit.SourceBoundCircuit
    originalCoilFirstPin : Circuit.Pin
    originalCoilSecondPin : Circuit.Pin
    originalCapFirstPin : Circuit.Pin
    originalCapSecondPin : Circuit.Pin
    originalNSTCentrePin : Circuit.Pin
    originalDiodeAnodeOne : Circuit.Pin
    originalDiodeAnodeTwo : Circuit.Pin
    originalDiodeAnodeThree : Circuit.Pin
    originalDiodeAnodeFour : Circuit.Pin
    originalLoadReturn : Circuit.Pin
    sourceVerifiedCoilIdentity : Set
    coilWitness : sourceVerifiedCoilIdentity
    sourceVerifiedReturnIdentity : Set
    returnWitness : sourceVerifiedReturnIdentity

-- No definition in this module inhabits AdmissionWitness. Reuse original
-- physical-source / signed-work owner before any experimental promotion.
