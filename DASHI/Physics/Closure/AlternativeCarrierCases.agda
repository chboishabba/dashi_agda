module DASHI.Physics.Closure.AlternativeCarrierCases where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.AlternativeCarrierSignatureStress as ACS
import DASHI.Physics.Closure.Validation.RootSystemB4PromotionBridge as B4PB
import DASHI.Physics.Closure.Validation.SyntheticOneMinusPromotionBridge as SMPB
import DASHI.Physics.Closure.Validation.SyntheticOneMinusOrientationSignatureBridge as SMOSB
import DASHI.Physics.RootSystemB4Carrier as B4
import DASHI.Physics.OrbitProfileComputedRootSystemB4 as B4OP
import DASHI.Physics.OrbitProfileComputedTailPerm as TP
import DASHI.Physics.ShellNeighborhoodClass as SNC
import DASHI.Physics.SyntheticOneMinusShellRealization as SOM

------------------------------------------------------------------------
-- Alternative-carrier controls lane.
--
-- This file is intentionally thin.  It only classifies a small set of
-- carrier controls and records the reason surfaces needed to keep the
-- noncanonical cases honest.  No router/ITIR/Mirror surfaces appear here.

data CarrierControlLane : Set where
  forced : CarrierControlLane
  conditional : CarrierControlLane
  blocked : CarrierControlLane
  held : CarrierControlLane

laneToStressStatus :
  CarrierControlLane →
  ACS.SignatureStressStatus
laneToStressStatus forced = ACS.forced
laneToStressStatus conditional = ACS.conditional
laneToStressStatus blocked = ACS.failed
laneToStressStatus held = ACS.held

record CarrierReasonSurface : Set₁ where
  field
    distortion : Set
    transport : Set
    signature : Set

open CarrierReasonSurface public

record AlternativeCarrierCase : Set₁ where
  field
    caseLabel : String
    lane : CarrierControlLane
    caseShell1Profile : List Nat
    caseShell2Profile : List Nat
    reasonSurface : CarrierReasonSurface

open AlternativeCarrierCase public

record AlternativeCarrierCaseReport : Set₂ where
  field
    controlCase : AlternativeCarrierCase
    classifiedAs : ACS.SignatureStressStatus
    classificationAgrees : laneToStressStatus (lane controlCase) ≡ classifiedAs
    controlEvidence : Set₁
    controlEvidenceWitness : controlEvidence

open AlternativeCarrierCaseReport public

------------------------------------------------------------------------
-- Gap surfaces for the blocked carrier.

data TailPermutationMissingDistortion : Set where
  tailPermutationDistortionUnavailable : TailPermutationMissingDistortion

data TailPermutationMissingTransport : Set where
  tailPermutationTransportUnavailable : TailPermutationMissingTransport

data TailPermutationMissingSignature : Set where
  tailPermutationSignatureUnavailable : TailPermutationMissingSignature

tailPermutationMissingSurface : CarrierReasonSurface
tailPermutationMissingSurface =
  record
    { distortion = TailPermutationMissingDistortion
    ; transport = TailPermutationMissingTransport
    ; signature = TailPermutationMissingSignature
    }

------------------------------------------------------------------------
-- Held reason for the synthetic one-minus control.

syntheticOneMinusHeldReason : Set
syntheticOneMinusHeldReason =
  SOM.shellNeighborhood ≡ SNC.oneMinusShellNeighborhood

syntheticOneMinusHeldCarrier :
  ACS.HeldCarrierSignatureStress (List Nat)
syntheticOneMinusHeldCarrier =
  ACS.heldCarrierSignatureStress
    SOM.shell1Profile
    syntheticOneMinusHeldReason

syntheticOneMinusTransportSurface : Set
syntheticOneMinusTransportSurface =
  SOM.shellNeighborhood ≡ SNC.oneMinusShellNeighborhood

------------------------------------------------------------------------
-- Carrier cases.

rootSystemB4ReasonSurface : CarrierReasonSurface
rootSystemB4ReasonSurface =
  record
    { distortion = ⊤
    ; transport = ⊤
    ; signature = ⊤
    }

rootSystemB4Case : AlternativeCarrierCase
rootSystemB4Case =
  record
    { caseLabel = "root-system-b4"
    ; lane = forced
    ; caseShell1Profile = B4OP.b4-shell1-computed
    ; caseShell2Profile = B4OP.b4-shell2-computed
    ; reasonSurface = rootSystemB4ReasonSurface
    }

rootSystemB4CaseReport : AlternativeCarrierCaseReport
rootSystemB4CaseReport =
  record
    { controlCase = rootSystemB4Case
    ; classifiedAs = ACS.forced
    ; classificationAgrees = refl
    ; controlEvidence = CarrierReasonSurface
    ; controlEvidenceWitness = rootSystemB4ReasonSurface
    }

syntheticOneMinusReasonSurface : CarrierReasonSurface
syntheticOneMinusReasonSurface =
  record
    { distortion = ⊤
    ; transport = syntheticOneMinusTransportSurface
    ; signature = ⊤
    }

syntheticOneMinusCase : AlternativeCarrierCase
syntheticOneMinusCase =
  record
    { caseLabel = "synthetic-one-minus"
    ; lane = held
    ; caseShell1Profile = SOM.shell1Profile
    ; caseShell2Profile = SOM.shell2Profile
    ; reasonSurface = syntheticOneMinusReasonSurface
    }

syntheticOneMinusCaseReport : AlternativeCarrierCaseReport
syntheticOneMinusCaseReport =
  record
    { controlCase = syntheticOneMinusCase
    ; classifiedAs = ACS.held
    ; classificationAgrees = refl
    ; controlEvidence = ACS.HeldCarrierSignatureStress (List Nat)
    ; controlEvidenceWitness = syntheticOneMinusHeldCarrier
    }

tailPermutationReasonSurface : CarrierReasonSurface
tailPermutationReasonSurface = tailPermutationMissingSurface

tailPermutationCase : AlternativeCarrierCase
tailPermutationCase =
  record
    { caseLabel = "tail-permutation-control"
    ; lane = blocked
    ; caseShell1Profile = TP.shell1_p3_q1_tailperm_computed
    ; caseShell2Profile = TP.shell2_p3_q1_tailperm_computed
    ; reasonSurface = tailPermutationReasonSurface
    }

tailPermutationCaseReport : AlternativeCarrierCaseReport
tailPermutationCaseReport =
  record
    { controlCase = tailPermutationCase
    ; classifiedAs = ACS.failed
    ; classificationAgrees = refl
    ; controlEvidence = CarrierReasonSurface
    ; controlEvidenceWitness = tailPermutationReasonSurface
    }

carrierCases : List AlternativeCarrierCase
carrierCases =
  rootSystemB4Case ∷
  syntheticOneMinusCase ∷
  tailPermutationCase ∷
  []

carrierCaseReports : List AlternativeCarrierCaseReport
carrierCaseReports =
  rootSystemB4CaseReport ∷
  syntheticOneMinusCaseReport ∷
  tailPermutationCaseReport ∷
  []

carrierCaseCount : Nat
carrierCaseCount = 3

rootSystemB4PromotionBridge : B4PB.B4PromotionBridge
rootSystemB4PromotionBridge = B4PB.bridge

syntheticOneMinusPromotionBridge : SMPB.SyntheticPromotionBridge
syntheticOneMinusPromotionBridge = SMPB.bridge

rootSystemB4Carrier : B4.B4Point
rootSystemB4Carrier = B4.pt B4.p1 B4.z B4.z B4.z
