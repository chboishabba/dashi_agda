module DASHI.Physics.Closure.SpectralGapRefinementStability where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.LCP.InductiveLimit using (NatColimitWitness)
import DASHI.Geometry.LCP.FiniteSpectralGap as FSG
import DASHI.Physics.Closure.YangMillsMassGapBoundary as YMGap

------------------------------------------------------------------------
-- Spectral-gap stability across refinements.
--
-- The finite repo already knows how to package a concrete finite spectral-gap
-- witness, its refinement monotonicity, and its transfer to a Nat colimit.
-- This module turns that shape into a reusable receipt: the finite toolkit is
-- the upstream anchor, and the refinement / lower-bound / colimit transfer
-- obligations are recorded explicitly as typed boundary data.

data SpectralGapRefinementStatus : Set where
  boundaryOnlyNoPromotion :
    SpectralGapRefinementStatus

data SpectralGapRefinementOpenObligation : Set where
  missingTowerRefinementWitness :
    SpectralGapRefinementOpenObligation

  missingGapMonotonicitySchema :
    SpectralGapRefinementOpenObligation

  missingLowerBoundPersistence :
    SpectralGapRefinementOpenObligation

  missingNatColimitCompatibility :
    SpectralGapRefinementOpenObligation

  missingInductiveLimitTransfer :
    SpectralGapRefinementOpenObligation

  missingGate2Promotion :
    SpectralGapRefinementOpenObligation

canonicalSpectralGapRefinementOpenObligations :
  List SpectralGapRefinementOpenObligation
canonicalSpectralGapRefinementOpenObligations =
  missingTowerRefinementWitness
  ∷ missingGapMonotonicitySchema
  ∷ missingLowerBoundPersistence
  ∷ missingNatColimitCompatibility
  ∷ missingInductiveLimitTransfer
  ∷ missingGate2Promotion
  ∷ []

data SpectralGapRefinementProofShape : Set where
  towerRefinementShape :
    SpectralGapRefinementProofShape

  gapMonotonicityShape :
    SpectralGapRefinementProofShape

  lowerBoundPersistenceShape :
    SpectralGapRefinementProofShape

  natColimitCompatibilityShape :
    SpectralGapRefinementProofShape

  inductiveLimitTransferShape :
    SpectralGapRefinementProofShape

canonicalSpectralGapRefinementProofShape :
  List SpectralGapRefinementProofShape
canonicalSpectralGapRefinementProofShape =
  towerRefinementShape
  ∷ gapMonotonicityShape
  ∷ lowerBoundPersistenceShape
  ∷ natColimitCompatibilityShape
  ∷ inductiveLimitTransferShape
  ∷ []

record SpectralGapRefinementStabilityReceipt : Setω where
  field
    upstreamYangMillsMassGapBoundary :
      YMGap.YangMillsMassGapBoundaryReceipt

    finiteSpectralGapToolkit :
      FSG.FiniteSpectralGapToolkit

    towerRefinementLabel :
      String

    towerRefinementLabelIsCanonical :
      towerRefinementLabel
      ≡
      "gap-monotone-under-tower-refinement"

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

    gapLowerBoundRecorded :
      Bool

    gapLowerBoundRecordedIsTrue :
      gapLowerBoundRecorded ≡ true

    monotoneUnderRefinementRecorded :
      Bool

    monotoneUnderRefinementRecordedIsTrue :
      monotoneUnderRefinementRecorded ≡ true

    lowerBoundPersistsAcrossDepthRecorded :
      Bool

    lowerBoundPersistsAcrossDepthRecordedIsTrue :
      lowerBoundPersistsAcrossDepthRecorded ≡ true

    natColimitCompatibilityRecorded :
      Bool

    natColimitCompatibilityRecordedIsTrue :
      natColimitCompatibilityRecorded ≡ true

    inductiveLimitTransferRecorded :
      Bool

    inductiveLimitTransferRecordedIsTrue :
      inductiveLimitTransferRecorded ≡ true

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    openObligations :
      List SpectralGapRefinementOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalSpectralGapRefinementOpenObligations

    proofShape :
      List SpectralGapRefinementProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalSpectralGapRefinementProofShape

    boundaryNotes :
      List String

open SpectralGapRefinementStabilityReceipt public

canonicalSpectralGapRefinementStabilityReceipt :
  SpectralGapRefinementStabilityReceipt
canonicalSpectralGapRefinementStabilityReceipt =
  record
    { upstreamYangMillsMassGapBoundary =
        YMGap.canonicalYangMillsMassGapBoundaryReceipt
    ; finiteSpectralGapToolkit =
        FSG.constantBoolFiniteSpectralGapToolkit
    ; towerRefinementLabel =
        "gap-monotone-under-tower-refinement"
    ; towerRefinementLabelIsCanonical =
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
    ; gapLowerBoundRecorded =
        true
    ; gapLowerBoundRecordedIsTrue =
        refl
    ; monotoneUnderRefinementRecorded =
        true
    ; monotoneUnderRefinementRecordedIsTrue =
        refl
    ; lowerBoundPersistsAcrossDepthRecorded =
        true
    ; lowerBoundPersistsAcrossDepthRecordedIsTrue =
        refl
    ; natColimitCompatibilityRecorded =
        true
    ; natColimitCompatibilityRecordedIsTrue =
        refl
    ; inductiveLimitTransferRecorded =
        true
    ; inductiveLimitTransferRecordedIsTrue =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; openObligations =
        canonicalSpectralGapRefinementOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalSpectralGapRefinementProofShape
    ; proofShapeIsCanonical =
        refl
    ; boundaryNotes =
        "The finite spectral-gap toolkit is the upstream witness anchor"
        ∷ "Refinement monotonicity is recorded as the reusable stability shape"
        ∷ "Lower-bound persistence is recorded across the finite depth ladder"
        ∷ "Nat colimit compatibility and inductive-limit transfer are boundary interfaces, not a promoted theorem"
        ∷ "The continuum Yang-Mills mass-gap claim remains external to this module"
        ∷ []
    }

canonicalSpectralGapFiniteToolkit :
  FSG.FiniteSpectralGapToolkit
canonicalSpectralGapFiniteToolkit =
  finiteSpectralGapToolkit
    canonicalSpectralGapRefinementStabilityReceipt

canonicalSpectralGapLimitWitness :
  NatColimitWitness (FSG.diagram canonicalSpectralGapFiniteToolkit)
canonicalSpectralGapLimitWitness =
  FSG.limitWitness canonicalSpectralGapFiniteToolkit
