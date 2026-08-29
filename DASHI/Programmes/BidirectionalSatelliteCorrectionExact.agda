module DASHI.Programmes.BidirectionalSatelliteCorrectionExact where

open import DASHI.Core.Prelude

import DASHI.Core.FormalClaimTransportGeometryExact as Transport
open import DASHI.Programmes.ResearchProgrammeExact

------------------------------------------------------------------------
-- Generic BIDI compiler for satellite research programmes.
--
-- Backward direction:
--   start from the actual formal consumer / claim and obtain the exact
--   representation through which that claim is already known to factor.
--
-- Forward direction:
--   start from the satellite's actual representation and provide a correction
--   map into the formal representation, together with a commuting receipt.
--
-- Only when both halves meet may the formal claim be transported back onto the
-- satellite representation.
------------------------------------------------------------------------

record CorrectedSatelliteBridge
    {State Satellite Formal Claim : Set}
    (satelliteRepresentation : State → Satellite)
    (formalRepresentation : State → Formal)
    (claim : State → Claim) : Set₁ where
  constructor correctedSatelliteBridge
  field
    correction : Satellite → Formal
    correctionCommutes :
      (state : State) →
      formalRepresentation state ≡ correction (satelliteRepresentation state)

    backwardFormalClaimTransport :
      Transport.ClaimTransport formalRepresentation claim

open CorrectedSatelliteBridge public

satelliteToFormalTransport :
  ∀ {State Satellite Formal Claim : Set}
    {satelliteRepresentation : State → Satellite}
    {formalRepresentation : State → Formal}
    {claim : State → Claim} →
  CorrectedSatelliteBridge satelliteRepresentation formalRepresentation claim →
  Transport.ClaimTransport satelliteRepresentation formalRepresentation
satelliteToFormalTransport bridge =
  Transport.claimTransport
    (correction bridge)
    (correctionCommutes bridge)

correctedSatelliteYieldsClaimTransport :
  ∀ {State Satellite Formal Claim : Set}
    {satelliteRepresentation : State → Satellite}
    {formalRepresentation : State → Formal}
    {claim : State → Claim} →
  CorrectedSatelliteBridge satelliteRepresentation formalRepresentation claim →
  Transport.ClaimTransport satelliteRepresentation claim
correctedSatelliteYieldsClaimTransport bridge =
  Transport.composeClaimTransport
    (backwardFormalClaimTransport bridge)
    (satelliteToFormalTransport bridge)

------------------------------------------------------------------------
-- A genuine information-loss witness defeats any proposed correction bridge.
-- This is the critical distinction between a naming/semantics bug and a state
-- representation that has actually thrown away information needed by the
-- downstream claim.
------------------------------------------------------------------------

informationLossBlocksCorrectedBridge :
  ∀ {State Satellite Formal Claim : Set}
    {satelliteRepresentation : State → Satellite}
    {formalRepresentation : State → Formal}
    {claim : State → Claim} →
  Transport.ClaimNonTransportWitness satelliteRepresentation claim →
  CorrectedSatelliteBridge satelliteRepresentation formalRepresentation claim →
  ⊥
informationLossBlocksCorrectedBridge witness bridge =
  Transport.claimNonTransportWitnessBlocksTransport
    witness
    (correctedSatelliteYieldsClaimTransport bridge)

------------------------------------------------------------------------
-- Audit vocabulary.  These labels do not prove the correction; they state what
-- kind of repair the forward satellite lane must produce before it can meet the
-- backward formal consumer.
------------------------------------------------------------------------

data CorrectionKind : Set where
  semanticRelabelling : CorrectionKind
  missingPreservationReceipt : CorrectionKind
  empiricalToExactGap : CorrectionKind
  representationEnlargement : CorrectionKind
  unsupportedPromotion : CorrectionKind
  runtimeEvidenceSeparation : CorrectionKind

data SatelliteCorrectionTarget : Set where
  cfdObservationPreservingChart : SatelliteCorrectionTarget
  brainKernelFixedPointSemantics : SatelliteCorrectionTarget
  quantumFalsifiableDiscriminator : SatelliteCorrectionTarget
  dashifineHeldOutInvariantClaim : SatelliteCorrectionTarget
  grokkingHeldOutFamilyLaw : SatelliteCorrectionTarget
  coreReferenceSemanticParity : SatelliteCorrectionTarget
  fracdashCompilerCommutingSquare : SatelliteCorrectionTarget
  testHarnessTypedEvidenceReceipt : SatelliteCorrectionTarget
  rtxObservationPreservingRefinement : SatelliteCorrectionTarget

record SatelliteBIDIAudit : Set where
  constructor satelliteBIDIAudit
  field
    programme : SatelliteRepository
    correctionTarget : SatelliteCorrectionTarget
    primaryCorrection : CorrectionKind
    secondaryCorrection : CorrectionKind
    correctedModelStillNeedsReceipt : Bool
    correctedModelStillNeedsReceiptIsTrue :
      correctedModelStillNeedsReceipt ≡ true

open SatelliteBIDIAudit public

cfdBIDIAudit : SatelliteBIDIAudit
cfdBIDIAudit = satelliteBIDIAudit dashiCFD cfdObservationPreservingChart
  representationEnlargement missingPreservationReceipt true refl

brainBIDIAudit : SatelliteBIDIAudit
brainBIDIAudit = satelliteBIDIAudit dashiBRAIN brainKernelFixedPointSemantics
  semanticRelabelling missingPreservationReceipt true refl

quantumBIDIAudit : SatelliteBIDIAudit
quantumBIDIAudit = satelliteBIDIAudit dashiQ quantumFalsifiableDiscriminator
  unsupportedPromotion missingPreservationReceipt true refl

dashifineBIDIAudit : SatelliteBIDIAudit
dashifineBIDIAudit = satelliteBIDIAudit dashifine dashifineHeldOutInvariantClaim
  empiricalToExactGap missingPreservationReceipt true refl

grokkingBIDIAudit : SatelliteBIDIAudit
grokkingBIDIAudit = satelliteBIDIAudit DASHIg grokkingHeldOutFamilyLaw
  empiricalToExactGap runtimeEvidenceSeparation true refl

coreBIDIAudit : SatelliteBIDIAudit
coreBIDIAudit = satelliteBIDIAudit dashiCORE coreReferenceSemanticParity
  semanticRelabelling missingPreservationReceipt true refl

fracdashBIDIAudit : SatelliteBIDIAudit
fracdashBIDIAudit = satelliteBIDIAudit FRACDASH fracdashCompilerCommutingSquare
  missingPreservationReceipt unsupportedPromotion true refl

testHarnessBIDIAudit : SatelliteBIDIAudit
testHarnessBIDIAudit = satelliteBIDIAudit dashitest testHarnessTypedEvidenceReceipt
  empiricalToExactGap unsupportedPromotion true refl

rtxBIDIAudit : SatelliteBIDIAudit
rtxBIDIAudit = satelliteBIDIAudit dashiRTX rtxObservationPreservingRefinement
  missingPreservationReceipt unsupportedPromotion true refl

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record BidirectionalSatelliteCorrectionBoundary : Set where
  constructor bidirectionalSatelliteCorrectionBoundary
  field
    correctedNamingAloneRepairsInformationLoss : Bool
    correctedNamingAloneRepairsInformationLossIsFalse :
      correctedNamingAloneRepairsInformationLoss ≡ false

    correctedModelMayReuseExistingFormalTheorem : Bool
    correctedModelMayReuseExistingFormalTheoremIsTrue :
      correctedModelMayReuseExistingFormalTheorem ≡ true

    empiricalAgreementIsCommutingReceipt : Bool
    empiricalAgreementIsCommutingReceiptIsFalse :
      empiricalAgreementIsCommutingReceipt ≡ false

canonicalBidirectionalSatelliteCorrectionBoundary :
  BidirectionalSatelliteCorrectionBoundary
canonicalBidirectionalSatelliteCorrectionBoundary =
  bidirectionalSatelliteCorrectionBoundary
    false refl
    true refl
    false refl
