module DASHI.Interop.StratifiedTypedComparisonLaw where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.RoleGrammarCore as Core
import DASHI.Core.BridgeRequirementCore as BridgeReq
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.EmptyPromotionCore as EmptyPromotion

------------------------------------------------------------------------
-- Stratified typed comparison law v2.
--
-- This is a receipt surface, not a semantic resolver.  It records which
-- comparisons are permitted at which layer, which residual is retained, and
-- where a bridge receipt is required before content identity may be promoted.

NO_TYPED_MEET : Residual.ResidualLevel
NO_TYPED_MEET =
  Residual.noTypedMeet

PARTIAL : Residual.ResidualLevel
PARTIAL =
  Residual.partial

data InspectionLevel : Set where
  nativeResidualInspection :
    InspectionLevel

  roleStructuralInspection :
    InspectionLevel

  typedMeetInspection :
    InspectionLevel

  bridgeReceiptInspection :
    InspectionLevel

  implicitBackgroundInspection :
    InspectionLevel

data BridgeStrength : Set where
  noBridge :
    BridgeStrength

  bridgeReceiptRequired :
    BridgeStrength

  partialBridge :
    BridgeStrength

  exactBridge :
    BridgeStrength

data ComparisonVerdict : Set where
  comparisonPermitted :
    ComparisonVerdict

  comparisonBlockedPendingBridge :
    ComparisonVerdict

bridgeStrengthCore :
  BridgeStrength →
  Core.BridgeStrength
bridgeStrengthCore noBridge =
  Core.noBridge
bridgeStrengthCore bridgeReceiptRequired =
  Core.weakBridge
bridgeStrengthCore partialBridge =
  Core.partialBridge
bridgeStrengthCore exactBridge =
  Core.exactBridge

comparisonVerdictAdmissionStatus :
  ComparisonVerdict →
  Core.AdmissionStatus
comparisonVerdictAdmissionStatus comparisonPermitted =
  Core.committedAdmission
comparisonVerdictAdmissionStatus comparisonBlockedPendingBridge =
  Core.blockedPendingBridgeAdmission

comparisonVerdictExternalAuthority :
  ComparisonVerdict →
  Bool
comparisonVerdictExternalAuthority verdict =
  Core.admissionExternalAuthority
    (comparisonVerdictAdmissionStatus verdict)

data ComparisonStatus : Set where
  nativeResidualStatus :
    Residual.ResidualLevel →
    ComparisonStatus

  roleStructuralAlwaysDefinedStatus :
    ComparisonStatus

  noTypedMeetAtInspectionStatus :
    ComparisonStatus

  bridgeReceiptRequiredStatus :
    ComparisonStatus

  partialBridgeWithNamedResidualStatus :
    String →
    ComparisonStatus

  exactBridgeWithNamedResidualStatus :
    String →
    ComparisonStatus

data FibreRelation : Set where
  sameFibre :
    FibreRelation

  differentFibre :
    FibreRelation

data DomainRelation : Set where
  sameDomain :
    DomainRelation

  differentDomain :
    DomainRelation

data RoleRelation : Set where
  sameRole :
    RoleRelation

  differentRole :
    RoleRelation

data SurfaceRelation : Set where
  sameSurface :
    SurfaceRelation

  differentSurface :
    SurfaceRelation

data DivergentSurfacePart : Set where
  predicateDiverges :
    DivergentSurfacePart

  argumentDiverges :
    DivergentSurfacePart

data BridgeReceipt : Set where
  explicitBridgeReceipt :
    String →
    BridgeStrength →
    Residual.ResidualLevel →
    BridgeReceipt

data BridgeEvidence : Set where
  bridgeAbsent :
    BridgeEvidence

  bridgePresent :
    BridgeReceipt →
    BridgeEvidence

bridgeReceiptStrength :
  BridgeReceipt →
  BridgeStrength
bridgeReceiptStrength (explicitBridgeReceipt _ strength _) =
  strength

bridgeReceiptResidual :
  BridgeReceipt →
  Residual.ResidualLevel
bridgeReceiptResidual (explicitBridgeReceipt _ _ residual) =
  residual

bridgeReceiptStatus :
  BridgeReceipt →
  ComparisonStatus
bridgeReceiptStatus (explicitBridgeReceipt name partialBridge _) =
  partialBridgeWithNamedResidualStatus name
bridgeReceiptStatus (explicitBridgeReceipt _ bridgeReceiptRequired _) =
  bridgeReceiptRequiredStatus
bridgeReceiptStatus (explicitBridgeReceipt _ noBridge _) =
  bridgeReceiptRequiredStatus
bridgeReceiptStatus (explicitBridgeReceipt residualName exactBridge _) =
  exactBridgeWithNamedResidualStatus residualName

bridgeEvidenceStrength :
  BridgeEvidence →
  BridgeStrength
bridgeEvidenceStrength bridgeAbsent =
  bridgeReceiptRequired
bridgeEvidenceStrength (bridgePresent receipt) =
  bridgeReceiptStrength receipt

bridgeEvidenceResidual :
  BridgeEvidence →
  Residual.ResidualLevel
bridgeEvidenceResidual bridgeAbsent =
  NO_TYPED_MEET
bridgeEvidenceResidual (bridgePresent receipt) =
  bridgeReceiptResidual receipt

bridgeEvidenceStatus :
  BridgeEvidence →
  ComparisonStatus
bridgeEvidenceStatus bridgeAbsent =
  bridgeReceiptRequiredStatus
bridgeEvidenceStatus (bridgePresent receipt) =
  bridgeReceiptStatus receipt

bridgeEvidenceVerdict :
  BridgeEvidence →
  ComparisonVerdict
bridgeEvidenceVerdict bridgeAbsent =
  comparisonBlockedPendingBridge
bridgeEvidenceVerdict (bridgePresent _) =
  comparisonPermitted

bridgeEvidenceCoreStrength :
  BridgeEvidence →
  Core.BridgeStrength
bridgeEvidenceCoreStrength evidence =
  bridgeStrengthCore (bridgeEvidenceStrength evidence)

exactReceiptContentIdentityAdmitted :
  BridgeReceipt →
  Bool
exactReceiptContentIdentityAdmitted
  (explicitBridgeReceipt _ exactBridge Residual.exact) =
  true
exactReceiptContentIdentityAdmitted _ =
  false

bridgeEvidencePresent :
  BridgeEvidence →
  Bool
bridgeEvidencePresent bridgeAbsent =
  false
bridgeEvidencePresent (bridgePresent _) =
  true

differentDomainBridgeAdmitsContentIdentity :
  BridgeEvidence →
  Bool
differentDomainBridgeAdmitsContentIdentity bridgeAbsent =
  false
differentDomainBridgeAdmitsContentIdentity (bridgePresent receipt) =
  exactReceiptContentIdentityAdmitted receipt

data StratifiedComparisonCase : Set where
  SameDomainSameRole :
    Residual.ResidualLevel →
    StratifiedComparisonCase

  DifferentDomainSameRole :
    StratifiedComparisonCase

  SameSurfaceDivergent :
    DivergentSurfacePart →
    StratifiedComparisonCase

  DifferentDomainContentIdentification :
    BridgeEvidence →
    StratifiedComparisonCase

  CrossDomainImplicitBackgroundChain :
    String →
    StratifiedComparisonCase

comparisonInspectionLevel :
  StratifiedComparisonCase →
  InspectionLevel
comparisonInspectionLevel (SameDomainSameRole _) =
  nativeResidualInspection
comparisonInspectionLevel DifferentDomainSameRole =
  roleStructuralInspection
comparisonInspectionLevel (SameSurfaceDivergent _) =
  typedMeetInspection
comparisonInspectionLevel (DifferentDomainContentIdentification _) =
  bridgeReceiptInspection
comparisonInspectionLevel (CrossDomainImplicitBackgroundChain _) =
  implicitBackgroundInspection

comparisonBridgeStrength :
  StratifiedComparisonCase →
  BridgeStrength
comparisonBridgeStrength (SameDomainSameRole _) =
  noBridge
comparisonBridgeStrength DifferentDomainSameRole =
  noBridge
comparisonBridgeStrength (SameSurfaceDivergent _) =
  noBridge
comparisonBridgeStrength (DifferentDomainContentIdentification evidence) =
  bridgeEvidenceStrength evidence
comparisonBridgeStrength (CrossDomainImplicitBackgroundChain _) =
  partialBridge

comparisonCoreBridgeStrength :
  StratifiedComparisonCase →
  Core.BridgeStrength
comparisonCoreBridgeStrength comparisonCase =
  bridgeStrengthCore (comparisonBridgeStrength comparisonCase)

comparisonResidual :
  StratifiedComparisonCase →
  Residual.ResidualLevel
comparisonResidual (SameDomainSameRole residual) =
  residual
comparisonResidual DifferentDomainSameRole =
  PARTIAL
comparisonResidual (SameSurfaceDivergent _) =
  NO_TYPED_MEET
comparisonResidual (DifferentDomainContentIdentification evidence) =
  bridgeEvidenceResidual evidence
comparisonResidual (CrossDomainImplicitBackgroundChain _) =
  PARTIAL

comparisonStatus :
  StratifiedComparisonCase →
  ComparisonStatus
comparisonStatus (SameDomainSameRole residual) =
  nativeResidualStatus residual
comparisonStatus DifferentDomainSameRole =
  roleStructuralAlwaysDefinedStatus
comparisonStatus (SameSurfaceDivergent _) =
  noTypedMeetAtInspectionStatus
comparisonStatus (DifferentDomainContentIdentification evidence) =
  bridgeEvidenceStatus evidence
comparisonStatus (CrossDomainImplicitBackgroundChain residualName) =
  partialBridgeWithNamedResidualStatus residualName

comparisonVerdict :
  StratifiedComparisonCase →
  ComparisonVerdict
comparisonVerdict (SameDomainSameRole _) =
  comparisonPermitted
comparisonVerdict DifferentDomainSameRole =
  comparisonPermitted
comparisonVerdict (SameSurfaceDivergent _) =
  comparisonPermitted
comparisonVerdict (DifferentDomainContentIdentification evidence) =
  bridgeEvidenceVerdict evidence
comparisonVerdict (CrossDomainImplicitBackgroundChain _) =
  comparisonPermitted

comparisonAdmissionStatus :
  StratifiedComparisonCase →
  Core.AdmissionStatus
comparisonAdmissionStatus comparisonCase =
  comparisonVerdictAdmissionStatus (comparisonVerdict comparisonCase)

comparisonExternalAuthority :
  StratifiedComparisonCase →
  Bool
comparisonExternalAuthority comparisonCase =
  Core.admissionExternalAuthority
    (comparisonAdmissionStatus comparisonCase)

contentIdentityAdmitted :
  StratifiedComparisonCase →
  Bool
contentIdentityAdmitted (SameDomainSameRole _) =
  false
contentIdentityAdmitted DifferentDomainSameRole =
  false
contentIdentityAdmitted (SameSurfaceDivergent _) =
  false
contentIdentityAdmitted (DifferentDomainContentIdentification evidence) =
  differentDomainBridgeAdmitsContentIdentity evidence
contentIdentityAdmitted (CrossDomainImplicitBackgroundChain _) =
  false

contentIdentityPromoted :
  StratifiedComparisonCase →
  Bool
contentIdentityPromoted _ =
  false

roleComparisonPermitted :
  FibreRelation →
  RoleRelation →
  Bool
roleComparisonPermitted _ sameRole =
  true
roleComparisonPermitted _ differentRole =
  false

contentIdentityAdmittedWithBridgeEvidence :
  DomainRelation →
  BridgeEvidence →
  Bool
contentIdentityAdmittedWithBridgeEvidence sameDomain evidence =
  bridgeEvidencePresent evidence
contentIdentityAdmittedWithBridgeEvidence differentDomain evidence =
  differentDomainBridgeAdmitsContentIdentity evidence

data CrossDomainContentIdentityWithoutBridgePromotion : Set where

crossDomainContentIdentityWithoutBridgeImpossible :
  CrossDomainContentIdentityWithoutBridgePromotion →
  ⊥
crossDomainContentIdentityWithoutBridgeImpossible ()

record ComparisonLawRow : Set where
  constructor comparisonLawRow
  field
    rowName :
      String

    rowCase :
      StratifiedComparisonCase

    rowInspectionLevel :
      InspectionLevel

    rowBridgeStrength :
      BridgeStrength

    rowVerdict :
      ComparisonVerdict

    rowStatus :
      ComparisonStatus

    rowResidual :
      Residual.ResidualLevel

    rowContentIdentityPromoted :
      Bool

    rowNamedResidual :
      String

comparisonLawRowFromCase :
  String →
  StratifiedComparisonCase →
  String →
  ComparisonLawRow
comparisonLawRowFromCase rowName comparisonCase residualName =
  comparisonLawRow
    rowName
    comparisonCase
    (comparisonInspectionLevel comparisonCase)
    (comparisonBridgeStrength comparisonCase)
    (comparisonVerdict comparisonCase)
    (comparisonStatus comparisonCase)
    (comparisonResidual comparisonCase)
    (contentIdentityPromoted comparisonCase)
    residualName

canonicalSameDomainSameRoleRow :
  ComparisonLawRow
canonicalSameDomainSameRoleRow =
  comparisonLawRowFromCase
    "SameDomainSameRole -> native residual"
    (SameDomainSameRole Residual.exact)
    "native-residual"

canonicalDifferentDomainSameRoleRow :
  ComparisonLawRow
canonicalDifferentDomainSameRoleRow =
  comparisonLawRowFromCase
    "DifferentDomainSameRole -> role-structural comparison"
    DifferentDomainSameRole
    "role-structural-residual"

canonicalSameSurfaceDivergentPredicateRow :
  ComparisonLawRow
canonicalSameSurfaceDivergentPredicateRow =
  comparisonLawRowFromCase
    "SameSurface divergent predicate -> NO_TYPED_MEET"
    (SameSurfaceDivergent predicateDiverges)
    "predicate-divergence-no-typed-meet"

canonicalSameSurfaceDivergentArgumentRow :
  ComparisonLawRow
canonicalSameSurfaceDivergentArgumentRow =
  comparisonLawRowFromCase
    "SameSurface divergent argument -> NO_TYPED_MEET"
    (SameSurfaceDivergent argumentDiverges)
    "argument-divergence-no-typed-meet"

canonicalDifferentDomainContentIdentificationRow :
  ComparisonLawRow
canonicalDifferentDomainContentIdentificationRow =
  comparisonLawRowFromCase
    "DifferentDomain content-identification -> bridge receipt required"
    (DifferentDomainContentIdentification bridgeAbsent)
    "missing-content-identity-bridge"

canonicalCrossDomainImplicitBackgroundChainRow :
  ComparisonLawRow
canonicalCrossDomainImplicitBackgroundChainRow =
  comparisonLawRowFromCase
    "Cross-domain implicit background chain -> PARTIAL bridge"
    (CrossDomainImplicitBackgroundChain "implicit-background-chain-residual")
    "implicit-background-chain-residual"

canonicalComparisonLawV2Rows :
  List ComparisonLawRow
canonicalComparisonLawV2Rows =
  canonicalSameDomainSameRoleRow
  ∷ canonicalDifferentDomainSameRoleRow
  ∷ canonicalSameSurfaceDivergentPredicateRow
  ∷ canonicalSameSurfaceDivergentArgumentRow
  ∷ canonicalDifferentDomainContentIdentificationRow
  ∷ canonicalCrossDomainImplicitBackgroundChainRow
  ∷ []

record StratifiedTypedComparisonLawV2Receipt : Set where
  constructor stratifiedTypedComparisonLawV2Receipt
  field
    canonicalRows :
      List ComparisonLawRow

    sameDomainSameRoleUsesNativeResidual :
      comparisonResidual (SameDomainSameRole Residual.exact) ≡ Residual.exact

    differentDomainSameRoleDefined :
      comparisonVerdict DifferentDomainSameRole ≡ comparisonPermitted

    crossFibreSameRoleComparisonPermitted :
      roleComparisonPermitted differentFibre sameRole ≡ true

    sameSurfacePredicateDivergenceNoTypedMeet :
      comparisonResidual (SameSurfaceDivergent predicateDiverges)
      ≡
      NO_TYPED_MEET

    sameSurfaceArgumentDivergenceNoTypedMeet :
      comparisonResidual (SameSurfaceDivergent argumentDiverges)
      ≡
      NO_TYPED_MEET

    differentDomainContentIdentityRequiresBridge :
      comparisonStatus (DifferentDomainContentIdentification bridgeAbsent)
      ≡
      bridgeReceiptRequiredStatus

    crossDomainContentIdentityNotPromotedWithoutBridge :
      contentIdentityPromoted
        (DifferentDomainContentIdentification bridgeAbsent)
      ≡
      false

    crossDomainImplicitBackgroundChainPartial :
      comparisonResidual
        (CrossDomainImplicitBackgroundChain "implicit-background-chain-residual")
      ≡
      PARTIAL

    crossDomainImplicitBackgroundChainNamed :
      comparisonStatus
        (CrossDomainImplicitBackgroundChain "implicit-background-chain-residual")
      ≡
      partialBridgeWithNamedResidualStatus "implicit-background-chain-residual"

canonicalStratifiedTypedComparisonLawV2Receipt :
  StratifiedTypedComparisonLawV2Receipt
canonicalStratifiedTypedComparisonLawV2Receipt =
  stratifiedTypedComparisonLawV2Receipt
    canonicalComparisonLawV2Rows
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalCrossFibreRoleComparisonPermitted :
  roleComparisonPermitted differentFibre sameRole ≡ true
canonicalCrossFibreRoleComparisonPermitted =
  refl

canonicalCrossDomainContentIdentityNotPromotedWithoutBridge :
  contentIdentityPromoted
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  false
canonicalCrossDomainContentIdentityNotPromotedWithoutBridge =
  refl

canonicalDifferentDomainContentIdentityBridgeRequired :
  comparisonBridgeStrength
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  bridgeReceiptRequired
canonicalDifferentDomainContentIdentityBridgeRequired =
  refl

canonicalDifferentDomainContentIdentityCoreBridgeRequired :
  comparisonCoreBridgeStrength
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  Core.weakBridge
canonicalDifferentDomainContentIdentityCoreBridgeRequired =
  refl

canonicalDifferentDomainContentIdentityBlockedAdmission :
  comparisonAdmissionStatus
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  Core.blockedPendingBridgeAdmission
canonicalDifferentDomainContentIdentityBlockedAdmission =
  refl

canonicalCrossDomainImplicitBackgroundCorePartial :
  comparisonCoreBridgeStrength
    (CrossDomainImplicitBackgroundChain "implicit-background-chain-residual")
  ≡
  Core.partialBridge
canonicalCrossDomainImplicitBackgroundCorePartial =
  refl

canonicalComparisonLawV2NoExternalAuthority :
  comparisonExternalAuthority
    (CrossDomainImplicitBackgroundChain "implicit-background-chain-residual")
  ≡
  false
canonicalComparisonLawV2NoExternalAuthority =
  refl

------------------------------------------------------------------------
-- Reusable core adapters.
--
-- These adapters are additive evidence only: they consume the reusable
-- fail-closed cores without changing the comparison law verdicts, row
-- constructors, bridge strengths, or content-identity booleans above.

bridgeRequirementCoreAdapter :
  BridgeReq.BridgeRequirementCoreReceipt
bridgeRequirementCoreAdapter =
  BridgeReq.canonicalBridgeRequirementCoreReceipt

bridgeRequirementCoreAdapterIsCanonical :
  bridgeRequirementCoreAdapter
  ≡
  BridgeReq.canonicalBridgeRequirementCoreReceipt
bridgeRequirementCoreAdapterIsCanonical =
  refl

candidateOnlyCoreAdapter :
  CandidateOnly.CandidateOnlyReceipt
    CandidateOnly.canonicalBridgeCandidateOnlyRow
candidateOnlyCoreAdapter =
  CandidateOnly.canonicalBridgeCandidateOnlyReceipt

candidateOnlyCoreAdapterIsCanonical :
  candidateOnlyCoreAdapter
  ≡
  CandidateOnly.canonicalBridgeCandidateOnlyReceipt
candidateOnlyCoreAdapterIsCanonical =
  refl

emptyPromotionCoreAdapter :
  EmptyPromotion.EmptyPromotionReceipt
emptyPromotionCoreAdapter =
  EmptyPromotion.canonicalEmptyPromotionReceipt

emptyPromotionCoreAdapterIsCanonical :
  emptyPromotionCoreAdapter
  ≡
  EmptyPromotion.canonicalEmptyPromotionReceipt
emptyPromotionCoreAdapterIsCanonical =
  refl

comparisonBridgeAuthorityPromoted :
  StratifiedComparisonCase →
  Bool
comparisonBridgeAuthorityPromoted _ =
  BridgeReq.receiptAuthorityPromotion bridgeRequirementCoreAdapter

comparisonBridgeAuthorityPromotedFalse :
  (comparisonCase : StratifiedComparisonCase) →
  comparisonBridgeAuthorityPromoted comparisonCase ≡ false
comparisonBridgeAuthorityPromotedFalse _ =
  BridgeReq.receiptAuthorityPromotionFalse bridgeRequirementCoreAdapter

comparisonBridgeTransportMapAuthorityFalse :
  (comparisonCase : StratifiedComparisonCase) →
  BridgeReq.receiptTransportMapAuthority bridgeRequirementCoreAdapter
  ≡
  false
comparisonBridgeTransportMapAuthorityFalse _ =
  BridgeReq.receiptTransportMapAuthorityFalse bridgeRequirementCoreAdapter

comparisonBridgeBackgroundAuthorityFalse :
  (comparisonCase : StratifiedComparisonCase) →
  BridgeReq.receiptBackgroundBridgeAuthority bridgeRequirementCoreAdapter
  ≡
  false
comparisonBridgeBackgroundAuthorityFalse _ =
  BridgeReq.receiptBackgroundBridgeAuthorityFalse bridgeRequirementCoreAdapter

candidateOnlyCoreAdapterCandidateTrue :
  CandidateOnly.candidateOnly CandidateOnly.canonicalBridgeCandidateOnlyRow
  ≡
  true
candidateOnlyCoreAdapterCandidateTrue =
  CandidateOnly.candidateOnlyIsTrue candidateOnlyCoreAdapter

candidateOnlyCoreAdapterPromotedFalse :
  CandidateOnly.promoted CandidateOnly.canonicalBridgeCandidateOnlyRow
  ≡
  false
candidateOnlyCoreAdapterPromotedFalse =
  CandidateOnly.candidatePromotedIsFalse candidateOnlyCoreAdapter

emptyPromotionCoreAdapterPromotionsEmpty :
  EmptyPromotion.promotions emptyPromotionCoreAdapter
  ≡
  []
emptyPromotionCoreAdapterPromotionsEmpty =
  EmptyPromotion.emptyPromotionReceiptPromotionsAreEmpty
    emptyPromotionCoreAdapter

comparisonContentIdentityPromotedFalse :
  (comparisonCase : StratifiedComparisonCase) →
  contentIdentityPromoted comparisonCase ≡ false
comparisonContentIdentityPromotedFalse _ =
  refl

canonicalDifferentDomainContentIdentityCoreBridgeAuthorityFalse :
  comparisonBridgeAuthorityPromoted
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  false
canonicalDifferentDomainContentIdentityCoreBridgeAuthorityFalse =
  comparisonBridgeAuthorityPromotedFalse
    (DifferentDomainContentIdentification bridgeAbsent)

canonicalDifferentDomainContentIdentityCoreNotPromoted :
  contentIdentityPromoted
    (DifferentDomainContentIdentification bridgeAbsent)
  ≡
  false
canonicalDifferentDomainContentIdentityCoreNotPromoted =
  comparisonContentIdentityPromotedFalse
    (DifferentDomainContentIdentification bridgeAbsent)

canonicalSameSurfacePredicateNoTypedMeetStatus :
  comparisonStatus (SameSurfaceDivergent predicateDiverges)
  ≡
  noTypedMeetAtInspectionStatus
canonicalSameSurfacePredicateNoTypedMeetStatus =
  refl

canonicalSameSurfaceArgumentNoTypedMeetStatus :
  comparisonStatus (SameSurfaceDivergent argumentDiverges)
  ≡
  noTypedMeetAtInspectionStatus
canonicalSameSurfaceArgumentNoTypedMeetStatus =
  refl

comparisonLawV2BoundaryStatement :
  String
comparisonLawV2BoundaryStatement =
  "Comparison law v2 permits cross-fibre same-role structural comparison, records same-surface predicate or argument divergence as NO_TYPED_MEET at inspection level, blocks cross-domain content identity until a bridge receipt is present, and keeps implicit background chains as PARTIAL named bridge residuals."
