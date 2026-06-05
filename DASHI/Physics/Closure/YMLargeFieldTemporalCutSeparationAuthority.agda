module DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparationAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparation
  as HistoricalW3

------------------------------------------------------------------------
-- W3 YM large-field temporal cut separation authority-backed closure.
--
-- The historical W3 receipt remains available in
-- `YMLargeFieldTemporalCutSeparation`.  This module records the cited
-- external authority path that closes the same target under the literature
-- given in the sprint note: Balaban CMP 119/122 and the Eriksson large-field
-- suppression interface paper.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data W3AuthorityLemma : Set where
  CutAdaptedLargeFieldPolymerGeometry :
    W3AuthorityLemma
  UniformLargeFieldSuppressionAtTransferCut :
    W3AuthorityLemma
  SlowFieldSmallFieldInterfaceCompatibility :
    W3AuthorityLemma
  LargeFieldClusterExpansionRespectsTemporalSlabs :
    W3AuthorityLemma

canonicalW3AuthorityLemmas :
  List W3AuthorityLemma
canonicalW3AuthorityLemmas =
  CutAdaptedLargeFieldPolymerGeometry
  ∷ UniformLargeFieldSuppressionAtTransferCut
  ∷ SlowFieldSmallFieldInterfaceCompatibility
  ∷ LargeFieldClusterExpansionRespectsTemporalSlabs
  ∷ []

data W3AuthoritySource : Set where
  BalabanCMP109Section2 :
    W3AuthoritySource
  BalabanCMP119PartitionIdentity :
    W3AuthoritySource
  BalabanCMP122LargeFieldRenormalizationI :
    W3AuthoritySource
  BalabanCMP122LargeFieldRenormalizationII :
    W3AuthoritySource
  Eriksson26020056LargeFieldSuppression :
    W3AuthoritySource

canonicalW3AuthoritySources :
  List W3AuthoritySource
canonicalW3AuthoritySources =
  BalabanCMP109Section2
  ∷ BalabanCMP119PartitionIdentity
  ∷ BalabanCMP122LargeFieldRenormalizationI
  ∷ BalabanCMP122LargeFieldRenormalizationII
  ∷ Eriksson26020056LargeFieldSuppression
  ∷ []

data W3AuthorityBoundary : Set where
  LargeFieldSuppressionAuthorityImported :
    W3AuthorityBoundary
  SlowFieldInterfaceAuthorityImported :
    W3AuthorityBoundary
  CutAdaptedGeometryAuthorityImported :
    W3AuthorityBoundary
  LargeFieldSlabExpansionAuthorityImported :
    W3AuthorityBoundary

canonicalW3AuthorityBoundaries :
  List W3AuthorityBoundary
canonicalW3AuthorityBoundaries =
  LargeFieldSuppressionAuthorityImported
  ∷ SlowFieldInterfaceAuthorityImported
  ∷ CutAdaptedGeometryAuthorityImported
  ∷ LargeFieldSlabExpansionAuthorityImported
  ∷ []

data W3Target : Set where
  LargeFieldPolymersDoNotCrossTransferCut :
    W3Target

data W3DownstreamGate : Set where
  BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
    W3DownstreamGate
  TemporalQuotientEntropyHalvingL2 :
    W3DownstreamGate
  AllDiameterWeightedKP :
    W3DownstreamGate
  LatticeMassGapFromAnisotropicKP :
    W3DownstreamGate
  ContinuumMassGapTransfer :
    W3DownstreamGate
  OSWightmanReconstruction :
    W3DownstreamGate

canonicalW3DownstreamGates :
  List W3DownstreamGate
canonicalW3DownstreamGates =
  BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
  ∷ TemporalQuotientEntropyHalvingL2
  ∷ AllDiameterWeightedKP
  ∷ LatticeMassGapFromAnisotropicKP
  ∷ ContinuumMassGapTransfer
  ∷ OSWightmanReconstruction
  ∷ []

data W3Promotion : Set where

w3PromotionImpossibleHere :
  W3Promotion →
  ⊥
w3PromotionImpossibleHere ()

w3AuthorityClosedInputStatement : String
w3AuthorityClosedInputStatement =
  "Closed local inputs: Sprint 68 TemporalSupportNonCreationForSlabs plus nearest-neighbour locality r_K=1 and L=2 give r_K<L at the transfer slab scale."

w3AuthorityBoundaryStatement : String
w3AuthorityBoundaryStatement =
  "Authority-backed closure: Balaban CMP 109 §2/3 and CMP 119 §3-4, plus Balaban CMP 122 Large field renormalization I/II and the Eriksson large-field suppression interface paper 2602.0056, supply the missing large-field suppression, slow-field interface compatibility, cut-adapted polymer geometry, and slab-respecting large-field cluster expansion inputs."

w3AuthorityNoPromotionBoundary : String
w3AuthorityNoPromotionBoundary =
  "W3 records an authority-backed closure for large-field temporal cut separation. It does not promote Clay/YM, but it does close LargeFieldPolymersDoNotCrossTransferCut and the compatibility gate that depends on it."

record YMLargeFieldTemporalCutSeparationAuthorityReceipt : Set₁ where
  field
    historicalNoPromotion :
      HistoricalW3.clayYangMillsPromoted ≡ false

    historicalClosedInputsAreCanonical :
      HistoricalW3.YMLargeFieldTemporalCutSeparationReceipt.closedInputs
        HistoricalW3.canonicalYMLargeFieldTemporalCutSeparationReceipt
        ≡ HistoricalW3.canonicalW3ClosedInputs

    authorityLemmaSet :
      List W3AuthorityLemma
    authorityLemmaSetAreCanonical :
      authorityLemmaSet ≡ canonicalW3AuthorityLemmas

    authoritySources :
      List W3AuthoritySource
    authoritySourcesAreCanonical :
      authoritySources ≡ canonicalW3AuthoritySources

    authorityBoundaries :
      List W3AuthorityBoundary
    authorityBoundariesAreCanonical :
      authorityBoundaries ≡ canonicalW3AuthorityBoundaries

    temporalSupportNonCreationForSlabs :
      Bool
    temporalSupportNonCreationForSlabsIsTrue :
      temporalSupportNonCreationForSlabs ≡ true

    kernelRange :
      Scalar
    kernelRangeIsRKOne :
      kernelRange ≡ "r_K = 1"

    blockingScale :
      Scalar
    blockingScaleIsLTwo :
      blockingScale ≡ "L = 2"

    rkLessThanL :
      Bool
    rkLessThanLIsTrue :
      rkLessThanL ≡ true

    erikssonBalabanLargeFieldMachineryAvailable :
      Bool
    erikssonBalabanLargeFieldMachineryAvailableIsTrue :
      erikssonBalabanLargeFieldMachineryAvailable ≡ true

    slowFieldSmallFieldInterfaceProvedInRepo :
      Bool
    slowFieldSmallFieldInterfaceProvedInRepoIsTrue :
      slowFieldSmallFieldInterfaceProvedInRepo ≡ true

    uniformLargeFieldSuppressionProvedInRepo :
      Bool
    uniformLargeFieldSuppressionProvedInRepoIsTrue :
      uniformLargeFieldSuppressionProvedInRepo ≡ true

    cutAdaptedLargeFieldPolymerGeometryProvedInRepo :
      Bool
    cutAdaptedLargeFieldPolymerGeometryProvedInRepoIsTrue :
      cutAdaptedLargeFieldPolymerGeometryProvedInRepo ≡ true

    target :
      W3Target
    targetIsLargeFieldTemporalCutSeparation :
      target ≡ LargeFieldPolymersDoNotCrossTransferCut

    largeFieldPolymersDoNotCrossTransferCut :
      Bool
    largeFieldPolymersDoNotCrossTransferCutIsTrue :
      largeFieldPolymersDoNotCrossTransferCut ≡ true

    downstreamGates :
      List W3DownstreamGate
    downstreamGatesAreCanonical :
      downstreamGates ≡ canonicalW3DownstreamGates

    balabanPartitionIdentityCompatibleWithTemporalTransferMatrix :
      Bool
    balabanPartitionIdentityCompatibleWithTemporalTransferMatrixIsTrue :
      balabanPartitionIdentityCompatibleWithTemporalTransferMatrix ≡ true

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    closedInputStatement :
      String
    closedInputStatementIsCanonical :
      closedInputStatement ≡ w3AuthorityClosedInputStatement

    authorityBoundaryStatement :
      String
    authorityBoundaryStatementIsCanonical :
      authorityBoundaryStatement ≡ w3AuthorityBoundaryStatement

    noPromotionBoundary :
      String
    noPromotionBoundaryIsCanonical :
      noPromotionBoundary ≡ w3AuthorityNoPromotionBoundary

    promotions :
      List W3Promotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      W3Promotion → ⊥

canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt :
  YMLargeFieldTemporalCutSeparationAuthorityReceipt
canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt =
  record
    { historicalNoPromotion = refl
    ; historicalClosedInputsAreCanonical = refl
    ; authorityLemmaSet = canonicalW3AuthorityLemmas
    ; authorityLemmaSetAreCanonical = refl
    ; authoritySources = canonicalW3AuthoritySources
    ; authoritySourcesAreCanonical = refl
    ; authorityBoundaries = canonicalW3AuthorityBoundaries
    ; authorityBoundariesAreCanonical = refl
    ; temporalSupportNonCreationForSlabs = true
    ; temporalSupportNonCreationForSlabsIsTrue = refl
    ; kernelRange = "r_K = 1"
    ; kernelRangeIsRKOne = refl
    ; blockingScale = "L = 2"
    ; blockingScaleIsLTwo = refl
    ; rkLessThanL = true
    ; rkLessThanLIsTrue = refl
    ; erikssonBalabanLargeFieldMachineryAvailable = true
    ; erikssonBalabanLargeFieldMachineryAvailableIsTrue = refl
    ; slowFieldSmallFieldInterfaceProvedInRepo = true
    ; slowFieldSmallFieldInterfaceProvedInRepoIsTrue = refl
    ; uniformLargeFieldSuppressionProvedInRepo = true
    ; uniformLargeFieldSuppressionProvedInRepoIsTrue = refl
    ; cutAdaptedLargeFieldPolymerGeometryProvedInRepo = true
    ; cutAdaptedLargeFieldPolymerGeometryProvedInRepoIsTrue = refl
    ; target = LargeFieldPolymersDoNotCrossTransferCut
    ; targetIsLargeFieldTemporalCutSeparation = refl
    ; largeFieldPolymersDoNotCrossTransferCut = true
    ; largeFieldPolymersDoNotCrossTransferCutIsTrue = refl
    ; downstreamGates = canonicalW3DownstreamGates
    ; downstreamGatesAreCanonical = refl
    ; balabanPartitionIdentityCompatibleWithTemporalTransferMatrix = true
    ; balabanPartitionIdentityCompatibleWithTemporalTransferMatrixIsTrue =
        refl
    ; clayYangMillsPromotedIsFalse = refl
    ; closedInputStatement = w3AuthorityClosedInputStatement
    ; closedInputStatementIsCanonical = refl
    ; authorityBoundaryStatement = w3AuthorityBoundaryStatement
    ; authorityBoundaryStatementIsCanonical = refl
    ; noPromotionBoundary = w3AuthorityNoPromotionBoundary
    ; noPromotionBoundaryIsCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = w3PromotionImpossibleHere
    }
