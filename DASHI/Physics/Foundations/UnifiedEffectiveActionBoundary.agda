module DASHI.Physics.Foundations.UnifiedEffectiveActionBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Geometry
import DASHI.Physics.Foundations.KernelQFTEmergenceObligations as Quantum
import DASHI.Physics.Foundations.CausalCodingCosmologyBoundaryExact as Cosmology
import DASHI.Papers.Unification.TheoremInterface as ExistingUnification

------------------------------------------------------------------------
-- UV and IR are scale regimes.  They are not definitionally identical to QFT
-- and GR, because both quantum matter and gravity can have descriptions across
-- multiple scales.

data ScaleRegime : Set where
  ultravioletRegime : ScaleRegime
  intermediateRegime : ScaleRegime
  infraredRegime : ScaleRegime

data EffectiveSector : Set where
  geometrySector : EffectiveSector
  quantumMatterSector : EffectiveSector
  mixedBackreactionSector : EffectiveSector

sectorAtScale : ScaleRegime → List EffectiveSector
sectorAtScale ultravioletRegime =
  quantumMatterSector ∷ geometrySector ∷ mixedBackreactionSector ∷ []
sectorAtScale intermediateRegime =
  geometrySector ∷ quantumMatterSector ∷ mixedBackreactionSector ∷ []
sectorAtScale infraredRegime =
  geometrySector ∷ quantumMatterSector ∷ mixedBackreactionSector ∷ []

------------------------------------------------------------------------
-- One microscopic action may have several effective terms after coarse
-- graining.  Recovery requires separate theorems for every term and their
-- coupling.

data EffectiveActionTerm : Set where
  microscopicKernelTerm : EffectiveActionTerm
  einsteinHilbertTargetTerm : EffectiveActionTerm
  standardModelTargetTerm : EffectiveActionTerm
  higherCorrectionTerm : EffectiveActionTerm
  backreactionTerm : EffectiveActionTerm

canonicalEffectiveActionTerms : List EffectiveActionTerm
canonicalEffectiveActionTerms =
  microscopicKernelTerm
  ∷ einsteinHilbertTargetTerm
  ∷ standardModelTargetTerm
  ∷ higherCorrectionTerm
  ∷ backreactionTerm
  ∷ []

record EffectiveRecoveryReceipt : Set where
  constructor effectiveRecoveryReceipt
  field
    geometryAdapter : Geometry.KernelGeometryAdapter
    quantumAdapter : Quantum.KernelQFTAdapter
    geometryLimitProved : Bool
    quantumLimitProved : Bool
    commonCoarseGrainingProved : Bool
    backreactionConsistencyProved : Bool
    correctionsControlled : Bool

open EffectiveRecoveryReceipt public

currentEffectiveRecoveryReceipt : EffectiveRecoveryReceipt
currentEffectiveRecoveryReceipt =
  effectiveRecoveryReceipt
    Geometry.currentKernelGeometryAdapter
    Quantum.currentKernelQFTAdapter
    false false false false false

------------------------------------------------------------------------
-- Finite joint evolution keeps geometry and matter state explicit.

data GeometryState : Set where
  flatGeometryState : GeometryState
  curvedGeometryCandidateState : GeometryState

data MatterState : Set where
  vacuumMatterState : MatterState
  excitedMatterState : MatterState

record JointMicroscopicState : Set where
  constructor jointMicroscopicState
  field
    geometryState : GeometryState
    matterState : MatterState

open JointMicroscopicState public

jointStep : JointMicroscopicState → JointMicroscopicState
jointStep (jointMicroscopicState flatGeometryState vacuumMatterState) =
  jointMicroscopicState flatGeometryState vacuumMatterState
jointStep (jointMicroscopicState flatGeometryState excitedMatterState) =
  jointMicroscopicState curvedGeometryCandidateState excitedMatterState
jointStep (jointMicroscopicState curvedGeometryCandidateState vacuumMatterState) =
  jointMicroscopicState flatGeometryState vacuumMatterState
jointStep (jointMicroscopicState curvedGeometryCandidateState excitedMatterState) =
  jointMicroscopicState curvedGeometryCandidateState excitedMatterState

matterCanAlterGeometryCandidate :
  jointStep (jointMicroscopicState flatGeometryState excitedMatterState)
  ≡
  jointMicroscopicState curvedGeometryCandidateState excitedMatterState
matterCanAlterGeometryCandidate = refl

vacuumCandidateCanRelaxGeometry :
  jointStep (jointMicroscopicState curvedGeometryCandidateState vacuumMatterState)
  ≡
  jointMicroscopicState flatGeometryState vacuumMatterState
vacuumCandidateCanRelaxGeometry = refl

------------------------------------------------------------------------
-- The CMB is one observation channel constraining a cosmological solution; it
-- is not a header grounding the effective laws.

cmbBoundaryCarrier : Set
cmbBoundaryCarrier = Cosmology.CMBObservation

existingUnificationTerminalStillFalse :
  ExistingUnification.terminalUnificationPromoted
    ExistingUnification.canonicalUnificationPaperTheoremInterface
  ≡
  false
existingUnificationTerminalStillFalse =
  ExistingUnification.unificationPaperInterfaceTerminalFalse

record UnifiedEffectiveActionBoundary : Set where
  constructor unifiedEffectiveActionBoundary
  field
    ultravioletDefinitionallyMeansQFTOnly : Bool
    ultravioletDefinitionallyMeansQFTOnlyIsFalse :
      ultravioletDefinitionallyMeansQFTOnly ≡ false

    infraredDefinitionallyMeansGROnly : Bool
    infraredDefinitionallyMeansGROnlyIsFalse :
      infraredDefinitionallyMeansGROnly ≡ false

    oneWrittenActionAutomaticallyProvesBothEffectiveLimits : Bool
    oneWrittenActionAutomaticallyProvesBothEffectiveLimitsIsFalse :
      oneWrittenActionAutomaticallyProvesBothEffectiveLimits ≡ false

    cmbIsSharedFoundationalReferenceFrame : Bool
    cmbIsSharedFoundationalReferenceFrameIsFalse :
      cmbIsSharedFoundationalReferenceFrame ≡ false

    mdlSelectionIsAutomaticallyACosmicLaw : Bool
    mdlSelectionIsAutomaticallyACosmicLawIsFalse :
      mdlSelectionIsAutomaticallyACosmicLaw ≡ false

    planckScaleFollowsFromKernelDepthWithoutCalibration : Bool
    planckScaleFollowsFromKernelDepthWithoutCalibrationIsFalse :
      planckScaleFollowsFromKernelDepthWithoutCalibration ≡ false

    currentReceiptPromotesTerminalUnification : Bool
    currentReceiptPromotesTerminalUnificationIsFalse :
      currentReceiptPromotesTerminalUnification ≡ false

open UnifiedEffectiveActionBoundary public

canonicalUnifiedEffectiveActionBoundary : UnifiedEffectiveActionBoundary
canonicalUnifiedEffectiveActionBoundary =
  unifiedEffectiveActionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
