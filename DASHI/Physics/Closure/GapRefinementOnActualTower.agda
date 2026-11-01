module DASHI.Physics.Closure.GapRefinementOnActualTower where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.LCP.InductiveLimit using (NatColimitWitness)
import DASHI.Geometry.LCP.FiniteSpectralGap as FSG
import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as Pressure
import DASHI.Physics.Closure.SpectralGapRefinementStability as Spectral

------------------------------------------------------------------------
-- Gate 2 refinement receipt on the actual Nat-indexed tower.
--
-- This module does not instantiate the Gate 2 physics on the Bool toy
-- carrier.  Instead, it packages the existing Nat-indexed pressure slice,
-- the upstream spectral-gap stability receipt, and the Nat-directed
-- colimit witness already exported by the repo into a single fail-closed
-- receipt surface.

data GapRefinementOnActualTowerStatus : Set where
  boundaryOnlyNoPromotion :
    GapRefinementOnActualTowerStatus

data GapRefinementOnActualTowerOpenObligation : Set where
  missingGapMonotonicityWitness :
    GapRefinementOnActualTowerOpenObligation

  missingLowerBoundPersistenceWitness :
    GapRefinementOnActualTowerOpenObligation

  missingNatColimitCompatibilityWitness :
    GapRefinementOnActualTowerOpenObligation

  missingInductiveLimitTransferWitness :
    GapRefinementOnActualTowerOpenObligation

  missingGate2Promotion :
    GapRefinementOnActualTowerOpenObligation

canonicalGapRefinementOnActualTowerOpenObligations :
  List GapRefinementOnActualTowerOpenObligation
canonicalGapRefinementOnActualTowerOpenObligations =
  missingGapMonotonicityWitness
  ∷ missingLowerBoundPersistenceWitness
  ∷ missingNatColimitCompatibilityWitness
  ∷ missingInductiveLimitTransferWitness
  ∷ missingGate2Promotion
  ∷ []

data GapRefinementOnActualTowerProofShape : Set where
  gapMonotonicityShape :
    GapRefinementOnActualTowerProofShape

  lowerBoundPersistenceShape :
    GapRefinementOnActualTowerProofShape

  natColimitCompatibilityShape :
    GapRefinementOnActualTowerProofShape

  inductiveLimitTransferShape :
    GapRefinementOnActualTowerProofShape

canonicalGapRefinementOnActualTowerProofShape :
  List GapRefinementOnActualTowerProofShape
canonicalGapRefinementOnActualTowerProofShape =
  gapMonotonicityShape
  ∷ lowerBoundPersistenceShape
  ∷ natColimitCompatibilityShape
  ∷ inductiveLimitTransferShape
  ∷ []

record GapRefinementOnActualTowerReceipt : Setω where
  field
    upstreamSpectralGapRefinementReceipt :
      Spectral.SpectralGapRefinementStabilityReceipt

    actualNatWitnessSlice :
      Pressure.S8NatSpectralWitnessTestSlice

    actualNatToRealCarrierTransitionReceipt :
      Pressure.S8NatToRealPhysicalCarrierTransitionReceipt

    actualTowerRefinementLabel :
      String

    actualTowerRefinementLabelIsCanonical :
      actualTowerRefinementLabel
      ≡
      "gap-monotone-under-actual-Nat-tower-refinement"

    gapMonotonicityLabel :
      String

    gapMonotonicityLabelIsCanonical :
      gapMonotonicityLabel
      ≡
      "gap-lower-bound-persistence-across-refinement"

    lowerBoundPersistenceLabel :
      String

    lowerBoundPersistenceLabelIsCanonical :
      lowerBoundPersistenceLabel
      ≡
      "positive-gap-bound-persists-across-depth"

    natColimitCompatibilityLabel :
      String

    natColimitCompatibilityLabelIsCanonical :
      natColimitCompatibilityLabel
      ≡
      "Nat-directed-colimit-compatibility"

    inductiveLimitTransferLabel :
      String

    inductiveLimitTransferLabelIsCanonical :
      inductiveLimitTransferLabel
      ≡
      "finite-to-inductive-limit-transfer"

    natColimitWitness :
      NatColimitWitness
        (FSG.diagram
          (Spectral.finiteSpectralGapToolkit
            upstreamSpectralGapRefinementReceipt))

    gapMonotonicityRecorded :
      Bool

    gapMonotonicityRecordedIsTrue :
      gapMonotonicityRecorded ≡ true

    lowerBoundPersistenceRecorded :
      Bool

    lowerBoundPersistenceRecordedIsTrue :
      lowerBoundPersistenceRecorded ≡ true

    natColimitCompatibilityRecorded :
      Bool

    natColimitCompatibilityRecordedIsTrue :
      natColimitCompatibilityRecorded ≡ true

    inductiveLimitTransferRecorded :
      Bool

    inductiveLimitTransferRecordedIsTrue :
      inductiveLimitTransferRecorded ≡ true

    actualTowerPromoted :
      Bool

    actualTowerPromotedIsFalse :
      actualTowerPromoted ≡ false

    openObligations :
      List GapRefinementOnActualTowerOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalGapRefinementOnActualTowerOpenObligations

    proofShape :
      List GapRefinementOnActualTowerProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalGapRefinementOnActualTowerProofShape

    boundaryNotes :
      List String

open GapRefinementOnActualTowerReceipt public

canonicalGapRefinementOnActualTowerReceipt :
  GapRefinementOnActualTowerReceipt
canonicalGapRefinementOnActualTowerReceipt =
  record
    { upstreamSpectralGapRefinementReceipt =
        Spectral.canonicalSpectralGapRefinementStabilityReceipt
    ; actualNatWitnessSlice =
        Pressure.canonicalS8NatSpectralWitnessTestSlice
    ; actualNatToRealCarrierTransitionReceipt =
        Pressure.canonicalS8NatToRealPhysicalCarrierTransitionReceipt
    ; actualTowerRefinementLabel =
        "gap-monotone-under-actual-Nat-tower-refinement"
    ; actualTowerRefinementLabelIsCanonical =
        refl
    ; gapMonotonicityLabel =
        "gap-lower-bound-persistence-across-refinement"
    ; gapMonotonicityLabelIsCanonical =
        refl
    ; lowerBoundPersistenceLabel =
        "positive-gap-bound-persists-across-depth"
    ; lowerBoundPersistenceLabelIsCanonical =
        refl
    ; natColimitCompatibilityLabel =
        "Nat-directed-colimit-compatibility"
    ; natColimitCompatibilityLabelIsCanonical =
        refl
    ; inductiveLimitTransferLabel =
        "finite-to-inductive-limit-transfer"
    ; inductiveLimitTransferLabelIsCanonical =
        refl
    ; natColimitWitness =
        FSG.limitWitness Spectral.canonicalSpectralGapFiniteToolkit
    ; gapMonotonicityRecorded =
        true
    ; gapMonotonicityRecordedIsTrue =
        refl
    ; lowerBoundPersistenceRecorded =
        true
    ; lowerBoundPersistenceRecordedIsTrue =
        refl
    ; natColimitCompatibilityRecorded =
        true
    ; natColimitCompatibilityRecordedIsTrue =
        refl
    ; inductiveLimitTransferRecorded =
        true
    ; inductiveLimitTransferRecordedIsTrue =
        refl
    ; actualTowerPromoted =
        false
    ; actualTowerPromotedIsFalse =
        refl
    ; openObligations =
        canonicalGapRefinementOnActualTowerOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalGapRefinementOnActualTowerProofShape
    ; proofShapeIsCanonical =
        refl
    ; boundaryNotes =
        "The upstream spectral-gap stability receipt is consumed as the refinement anchor"
        ∷ "The actual Nat-indexed pressure slice and real-carrier transition receipt are threaded explicitly"
        ∷ "The Nat-directed colimit witness is reused as the compatibility anchor"
        ∷ "Gap monotonicity, lower-bound persistence, and inductive-limit transfer are recorded fail-closed"
        ∷ "No Bool toy-model promotion is introduced by this receipt"
        ∷ []
    }
