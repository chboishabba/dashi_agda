module DASHI.Core.LayeredKnowledgeReleaseBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LAYERED KNOWLEDGE-RELEASE BIDI
--
-- A programme can cross one public/private boundary without all of its
-- underlying objects crossing. Report publication, data availability,
-- hardware custody, and governance restrictions are therefore separate fibres.
------------------------------------------------------------------------

data ReleaseLayer : Set where
  governanceRestriction
  publicTechnicalReport
  underlyingData
  physicalHardware
  implementationKnowHow
  derivedPrivateResults
  : ReleaseLayer

data LayerState : Set where
  bounded
  reviewOrApprovalRequired
  public
  privateCustody
  publicCustody
  endedRestriction
  unknown
  : LayerState

record LayerReceipt : Set where
  constructor layer-receipt
  field
    programmeOrObject : String
    layer : ReleaseLayer
    state : LayerState
    sourceReference : String
    boundedReading : String

open LayerReceipt public

record LayeredReleaseProfile : Set where
  constructor layered-release-profile
  field
    programmeName : String
    governance : LayerReceipt
    report : LayerReceipt
    data : LayerReceipt
    hardware : LayerReceipt
    knowHow : LayerReceipt
    derivatives : LayerReceipt
    profileReference : String

open LayeredReleaseProfile public

------------------------------------------------------------------------
-- Weak partial release: public report plus an underlying layer that is either
-- known non-public OR still unresolved. Useful as a proof-search state, but not
-- enough to show an actual information boundary.
------------------------------------------------------------------------

record PartialReleaseWitness (profile : LayeredReleaseProfile) : Set where
  constructor partial-release-witness
  field
    reportPublic : state (report profile) ≡ public
    underlyingNotAllPublic :
      (state (data profile) ≡ privateCustody) ⊎
      (state (data profile) ≡ bounded) ⊎
      (state (data profile) ≡ unknown) ⊎
      (state (hardware profile) ≡ privateCustody) ⊎
      (state (hardware profile) ≡ bounded) ⊎
      (state (hardware profile) ≡ unknown) ⊎
      (state (knowHow profile) ≡ privateCustody) ⊎
      (state (knowHow profile) ≡ bounded) ⊎
      (state (knowHow profile) ≡ unknown)
    witnessReference : String

open PartialReleaseWitness public

------------------------------------------------------------------------
-- Stronger documented partial release. Unknown does NOT count. At least one
-- underlying layer must have a source-backed bounded/private state while the
-- report itself is public.
------------------------------------------------------------------------

record DocumentedPartialReleaseWitness (profile : LayeredReleaseProfile) : Set where
  constructor documented-partial-release-witness
  field
    reportPublic : state (report profile) ≡ public
    documentedUnderlyingBoundary :
      (state (data profile) ≡ privateCustody) ⊎
      (state (data profile) ≡ bounded) ⊎
      (state (hardware profile) ≡ privateCustody) ⊎
      (state (hardware profile) ≡ bounded) ⊎
      (state (knowHow profile) ≡ privateCustody) ⊎
      (state (knowHow profile) ≡ bounded)
    witnessReference : String

open DocumentedPartialReleaseWitness public

record GovernanceRelaxationWitness (profile : LayeredReleaseProfile) : Set where
  constructor governance-relaxation-witness
  field
    governanceEnded : state (governance profile) ≡ endedRestriction
    witnessReference : String

open GovernanceRelaxationWitness public

------------------------------------------------------------------------
-- Reverse acquisition: a claim of complete restricted->public transfer must
-- identify which layer crossed and must not inherit public status from another
-- layer.
------------------------------------------------------------------------

data LayeredReleaseAcquisitionTarget : Set where
  governanceStateReceipt
  reportReleaseReceipt
  dataReleaseReceipt
  hardwareAccessReceipt
  knowHowReleaseReceipt
  derivativeReleaseReceipt
  sameLayerSameObjectWeld
  : LayeredReleaseAcquisitionTarget

record LayeredReleaseReverseObligation : Set where
  constructor layered-release-reverse-obligation
  field
    programmeOrObject : String
    target : LayeredReleaseAcquisitionTarget
    requestedEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open LayeredReleaseReverseObligation public

record LayeredReleaseBoundary : Set where
  constructor layered-release-boundary
  field
    publicReportMeansUnderlyingDataPublic : Bool
    publicReportMeansUnderlyingDataPublicIsFalse :
      publicReportMeansUnderlyingDataPublic ≡ false
    publicReportMeansHardwarePubliclyAccessible : Bool
    publicReportMeansHardwarePubliclyAccessibleIsFalse :
      publicReportMeansHardwarePubliclyAccessible ≡ false
    proprietaryPeriodEndedMeansAllLayersPublic : Bool
    proprietaryPeriodEndedMeansAllLayersPublicIsFalse :
      proprietaryPeriodEndedMeansAllLayersPublic ≡ false
    publicSummaryMeansImplementationKnowHowPublic : Bool
    publicSummaryMeansImplementationKnowHowPublicIsFalse :
      publicSummaryMeansImplementationKnowHowPublic ≡ false
    derivedPrivateResultsInheritPublicStatusFromFoundation : Bool
    derivedPrivateResultsInheritPublicStatusFromFoundationIsFalse :
      derivedPrivateResultsInheritPublicStatusFromFoundation ≡ false
    unknownUnderlyingLayerCountsAsDocumentedBoundary : Bool
    unknownUnderlyingLayerCountsAsDocumentedBoundaryIsFalse :
      unknownUnderlyingLayerCountsAsDocumentedBoundary ≡ false

canonicalLayeredReleaseBoundary : LayeredReleaseBoundary
canonicalLayeredReleaseBoundary = layered-release-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
