module DASHI.Promotion.NumericAndAuthorityObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- Numeric, authority, provider, comparison, covariance, holdout, and
-- runtime promotion obligations.
--
-- This module is intentionally not a new claim owner.  It turns the
-- promotion checklist into concrete rows that a future authority-token
-- implementation must discharge before any corresponding guard can flip.

data ObligationTarget : Set where
  numericMeasuredValuesTarget : ObligationTarget
  authorityPolicyTarget : ObligationTarget
  providerAuthorityTarget : ObligationTarget
  comparisonLawTarget : ObligationTarget
  covarianceCalibrationTarget : ObligationTarget
  holdoutValidationTarget : ObligationTarget
  runtimeReplayTarget : ObligationTarget
  semanticAdequacyTarget : ObligationTarget
  empiricalAdequacyTarget : ObligationTarget

data EvidenceStage : Set where
  sourceSlotNamed : EvidenceStage
  metadataFieldsBound : EvidenceStage
  authorityTokenRequired : EvidenceStage
  consumerReceiptRequired : EvidenceStage
  validationTargetRequired : EvidenceStage
  claimGuardStillFalse : EvidenceStage

data RequiredAuthorityKind : Set where
  codataNumericAuthority : RequiredAuthorityKind
  pdgNumericAuthority : RequiredAuthorityKind
  providerDatasetAuthority : RequiredAuthorityKind
  comparisonMethodAuthority : RequiredAuthorityKind
  covarianceCalibrationAuthority : RequiredAuthorityKind
  holdoutProtocolAuthority : RequiredAuthorityKind
  runtimeReplayAuthority : RequiredAuthorityKind
  semanticReviewAuthority : RequiredAuthorityKind

data GuardName : Set where
  numericValuePromotedGuard : GuardName
  acceptedAuthorityTokenPresentGuard : GuardName
  acceptedProviderAuthorityPromotedGuard : GuardName
  comparisonLawPromotedGuard : GuardName
  covarianceCalibrationPromotedGuard : GuardName
  holdoutValidationAcceptedGuard : GuardName
  runtimeReplayAuthorityAcceptedGuard : GuardName
  semanticAdequacyAcceptedGuard : GuardName
  empiricalAdequacyAcceptedGuard : GuardName

record MetadataObligation : Set where
  field
    metadataLabel : String
    metadataPurpose : String
    requiredBeforeNumericUse : Bool
    requiredBeforeNumericUseIsTrue : requiredBeforeNumericUse ≡ true

open MetadataObligation public

record AuthorityObligationRow : Set₁ where
  field
    rowLabel : String
    target : ObligationTarget
    authorityKind : RequiredAuthorityKind
    evidenceStage : EvidenceStage
    guardName : GuardName
    sourceRegistry : Registry.ConstantsRegistry
    sourcePolicyReceipt : Registry.AuthorityConsumptionPolicyReceipt
    sourceEmpiricalRuntimeReceipt :
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt
    requiredMetadata : List MetadataObligation
    requiredSourceReceipts : List String
    requiredConsumerReceipts : List String
    validationTargets : List String
    currentPromotion : Bool
    currentPromotionIsFalse : currentPromotion ≡ false
    sourcePopulationUsable : Bool
    sourcePopulationUsableIsTrue : sourcePopulationUsable ≡ true
    promotionRequiresAuthorityToken : Bool
    promotionRequiresAuthorityTokenIsTrue :
      promotionRequiresAuthorityToken ≡ true

open AuthorityObligationRow public

canonicalNumericAndAuthorityBoundaryReceipt :
  AuthorityBoundary.AuthorityBoundaryReceipt
canonicalNumericAndAuthorityBoundaryReceipt =
  AuthorityBoundary.mkFailClosedAuthorityBoundaryReceipt
    "numeric and authority obligations boundary receipt"
    AuthorityBoundary.physicsBoundaryDomain
    AuthorityBoundary.physicsAuthorityClaim
    (CandidateOnly.namedCandidateKind
      "numeric and authority obligations boundary candidate")
    (CandidateOnly.namedCandidateOnlyStatus
      "numeric and authority obligations boundary status")
    "numeric and authority obligations remain candidate-only"
    "numeric and authority promotion requires a separate bridge receipt"
    "DASHI.Promotion.NumericAndAuthorityObligations"

canonicalNumericAndAuthorityBoundaryReceiptClaimDomainMatches :
  AuthorityBoundary.receiptDomain
    canonicalNumericAndAuthorityBoundaryReceipt
  ≡
  AuthorityBoundary.authorityBoundaryClaimDomain
    (AuthorityBoundary.receiptClaimKind
      canonicalNumericAndAuthorityBoundaryReceipt)
canonicalNumericAndAuthorityBoundaryReceiptClaimDomainMatches =
  AuthorityBoundary.authorityBoundaryClaimKindMatchesDomain
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptClaimAuthorityKindMatches :
  AuthorityBoundary.receiptClaimAuthorityKind
    canonicalNumericAndAuthorityBoundaryReceipt
  ≡
  AuthorityBoundary.authorityBoundaryClaimAuthorityKind
    (AuthorityBoundary.receiptClaimKind
      canonicalNumericAndAuthorityBoundaryReceipt)
canonicalNumericAndAuthorityBoundaryReceiptClaimAuthorityKindMatches =
  AuthorityBoundary.authorityBoundaryClaimKindMatchesAuthorityKind
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly
    (AuthorityBoundary.receiptCandidateRow
      canonicalNumericAndAuthorityBoundaryReceipt)
  ≡ true
canonicalNumericAndAuthorityBoundaryReceiptCandidateOnlyIsTrue =
  AuthorityBoundary.authorityBoundaryCandidateOnlyIsTrue
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptCandidatePromotedIsFalse :
  CandidateOnly.promoted
    (AuthorityBoundary.receiptCandidateRow
      canonicalNumericAndAuthorityBoundaryReceipt)
  ≡ false
canonicalNumericAndAuthorityBoundaryReceiptCandidatePromotedIsFalse =
  AuthorityBoundary.authorityBoundaryCandidatePromotedIsFalse
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundary.receiptAuthorityBundle
      canonicalNumericAndAuthorityBoundaryReceipt)
    (AuthorityBoundary.receiptBlockedAuthorityKinds
      canonicalNumericAndAuthorityBoundaryReceipt)
canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsFalse =
  AuthorityBoundary.authorityBoundaryBlockedAuthorityKindsFalse
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsCountIsCanonical :
  AuthorityBoundary.receiptBlockedAuthorityKindsCount
    canonicalNumericAndAuthorityBoundaryReceipt
  ≡ AuthorityBoundary.canonicalBlockedAuthorityKindCount
canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsCountIsCanonical =
  AuthorityBoundary.receiptBlockedAuthorityKindsCountIsCanonical
    canonicalNumericAndAuthorityBoundaryReceipt

canonicalNumericAndAuthorityBoundaryReceiptPromotedIsFalse :
  AuthorityBoundary.receiptBoundaryPromoted
    canonicalNumericAndAuthorityBoundaryReceipt
  ≡ false
canonicalNumericAndAuthorityBoundaryReceiptPromotedIsFalse =
  AuthorityBoundary.receiptBoundaryPromotedIsFalse
    canonicalNumericAndAuthorityBoundaryReceipt

record NumericAndAuthorityObligationIndex : Set₁ where
  field
    indexLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourcePolicyReceipt : Registry.AuthorityConsumptionPolicyReceipt
    sourceEmpiricalRuntimeReceipt :
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt
    metadataObligations : List MetadataObligation
    authorityRows : List AuthorityObligationRow
    numericAuthorityRows : List AuthorityObligationRow
    providerRuntimeRows : List AuthorityObligationRow
    rowCount : Nat
    numericAuthorityRowCount : Nat
    providerRuntimeRowCount : Nat
    allRowsHaveFalsePromotionGuards : Bool
    allRowsHaveFalsePromotionGuardsIsTrue :
      allRowsHaveFalsePromotionGuards ≡ true
    allRowsRequireAuthorityTokens : Bool
    allRowsRequireAuthorityTokensIsTrue :
      allRowsRequireAuthorityTokens ≡ true
    registryExternalInputOnly : Bool
    registryExternalInputOnlyIsTrue : registryExternalInputOnly ≡ true
    numericValuePromoted : Bool
    numericValuePromotedIsFalse : numericValuePromoted ≡ false
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    acceptedProviderAuthorityPromoted : Bool
    acceptedProviderAuthorityPromotedIsFalse :
      acceptedProviderAuthorityPromoted ≡ false
    comparisonLawPromoted : Bool
    comparisonLawPromotedIsFalse : comparisonLawPromoted ≡ false
    covarianceCalibrationPromoted : Bool
    covarianceCalibrationPromotedIsFalse :
      covarianceCalibrationPromoted ≡ false
    holdoutValidationAccepted : Bool
    holdoutValidationAcceptedIsFalse :
      holdoutValidationAccepted ≡ false
    runtimeReplayAuthorityAccepted : Bool
    runtimeReplayAuthorityAcceptedIsFalse :
      runtimeReplayAuthorityAccepted ≡ false
    semanticAdequacyAccepted : Bool
    semanticAdequacyAcceptedIsFalse :
      semanticAdequacyAccepted ≡ false
    empiricalAdequacyAccepted : Bool
    empiricalAdequacyAcceptedIsFalse :
      empiricalAdequacyAccepted ≡ false
    authorityBoundaryReceipt :
      AuthorityBoundary.AuthorityBoundaryReceipt
    authorityBoundaryReceiptIsCanonical :
      authorityBoundaryReceipt ≡
      canonicalNumericAndAuthorityBoundaryReceipt
    authorityBoundaryClaimDomainMatches :
      AuthorityBoundary.receiptDomain authorityBoundaryReceipt
      ≡
      AuthorityBoundary.authorityBoundaryClaimDomain
        (AuthorityBoundary.receiptClaimKind authorityBoundaryReceipt)
    authorityBoundaryClaimAuthorityKindMatches :
      AuthorityBoundary.receiptClaimAuthorityKind
        authorityBoundaryReceipt
      ≡
      AuthorityBoundary.authorityBoundaryClaimAuthorityKind
        (AuthorityBoundary.receiptClaimKind authorityBoundaryReceipt)
    authorityBoundaryCandidateOnlyIsTrue :
      CandidateOnly.candidateOnly
        (AuthorityBoundary.receiptCandidateRow authorityBoundaryReceipt) ≡ true
    authorityBoundaryCandidatePromotedIsFalse :
      CandidateOnly.promoted
        (AuthorityBoundary.receiptCandidateRow authorityBoundaryReceipt) ≡ false
    authorityBoundaryBlockedAuthorityKindsFalse :
      AuthorityNA.AllAuthorityKindsFalse
        (AuthorityBoundary.receiptAuthorityBundle authorityBoundaryReceipt)
        (AuthorityBoundary.receiptBlockedAuthorityKinds
          authorityBoundaryReceipt)
    authorityBoundaryBlockedAuthorityKindsCountIsCanonical :
      AuthorityBoundary.receiptBlockedAuthorityKindsCount
        authorityBoundaryReceipt ≡
        AuthorityBoundary.canonicalBlockedAuthorityKindCount
    authorityBoundaryPromoted : Bool
    authorityBoundaryPromotedIsFalse :
      authorityBoundaryPromoted ≡ false

open NumericAndAuthorityObligationIndex public

mkMetadata :
  String →
  String →
  MetadataObligation
mkMetadata label purpose =
  record
    { metadataLabel = label
    ; metadataPurpose = purpose
    ; requiredBeforeNumericUse = true
    ; requiredBeforeNumericUseIsTrue = refl
    }

mkAuthorityRow :
  String →
  ObligationTarget →
  RequiredAuthorityKind →
  EvidenceStage →
  GuardName →
  List MetadataObligation →
  List String →
  List String →
  List String →
  AuthorityObligationRow
mkAuthorityRow
  label target authority stage guard metadata sources consumers validation =
  record
    { rowLabel = label
    ; target = target
    ; authorityKind = authority
    ; evidenceStage = stage
    ; guardName = guard
    ; sourceRegistry = Registry.repoWideConstantsRegistry
    ; sourcePolicyReceipt =
        Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; sourceEmpiricalRuntimeReceipt =
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
    ; requiredMetadata = metadata
    ; requiredSourceReceipts = sources
    ; requiredConsumerReceipts = consumers
    ; validationTargets = validation
    ; currentPromotion = false
    ; currentPromotionIsFalse = refl
    ; sourcePopulationUsable = true
    ; sourcePopulationUsableIsTrue = refl
    ; promotionRequiresAuthorityToken = true
    ; promotionRequiresAuthorityTokenIsTrue = refl
    }

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalMetadataObligations : List MetadataObligation
canonicalMetadataObligations =
  mkMetadata
    "authorityVersion"
    "binds CODATA, PDG, provider, protocol, or runtime authority to a versioned source"
  ∷ mkMetadata
    "sourceUri"
    "locates the authority artifact or provider record consumed by the row"
  ∷ mkMetadata
    "sourceChecksum"
    "prevents silent source drift between authority ingestion and validation"
  ∷ mkMetadata
    "sourceAccessDate"
    "records when the authority artifact was observed by the repo"
  ∷ mkMetadata
    "valueUncertainty"
    "records uncertainty for measured numeric values, covariance inputs, and calibrated observations"
  ∷ mkMetadata
    "roundingPolicy"
    "defines how authority numerics are converted into repo-side finite tokens"
  ∷ mkMetadata
    "unitConvention"
    "binds SI, natural-unit, particle-data, chemistry, or provider unit conventions"
  ∷ mkMetadata
    "validityRegime"
    "bounds the physical, empirical, runtime, or semantic regime where the token may be consumed"
  ∷ mkMetadata
    "providerReceiptId"
    "names the concrete provider, replay, holdout, or semantic-review receipt"
  ∷ []

numericValueObligation : AuthorityObligationRow
numericValueObligation =
  mkAuthorityRow
    "measured numeric constant promotion"
    numericMeasuredValuesTarget
    codataNumericAuthority
    authorityTokenRequired
    numericValuePromotedGuard
    canonicalMetadataObligations
    ( "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots"
    ∷ "NIST CODATA measured and adjusted constants"
    ∷ "PDG particle-data values where the numeric slot is particle-sector owned"
    ∷ []
    )
    ( "per-slot numeric authority token"
    ∷ "per-slot uncertainty and unit-convention consumer receipt"
    ∷ "rounding-policy consumer receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

acceptedAuthorityTokenObligation : AuthorityObligationRow
acceptedAuthorityTokenObligation =
  mkAuthorityRow
    "accepted external authority token"
    authorityPolicyTarget
    pdgNumericAuthority
    authorityTokenRequired
    acceptedAuthorityTokenPresentGuard
    canonicalMetadataObligations
    ( "DASHI.Constants.Registry.canonicalAuthorityConsumptionPolicyReceipt"
    ∷ "BIPM/NIST/CODATA/PDG/provider source slot selected by consumer lane"
    ∷ []
    )
    ( "authority-token acceptance receipt"
    ∷ "consumer-lane source-kind compatibility receipt"
    ∷ "claim-surface audit receipt before guard flip"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "git diff --check"
    ∷ []
    )

providerAuthorityObligation : AuthorityObligationRow
providerAuthorityObligation =
  mkAuthorityRow
    "accepted provider authority"
    providerAuthorityTarget
    providerDatasetAuthority
    authorityTokenRequired
    acceptedProviderAuthorityPromotedGuard
    canonicalMetadataObligations
    ( "HEPData/provider source URI"
    ∷ "provider record id and version"
    ∷ "source checksum and observable definition"
    ∷ []
    )
    ( "provider authority decision token"
    ∷ "observable-class authority receipt"
    ∷ "source checksum consumer receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

comparisonLawObligation : AuthorityObligationRow
comparisonLawObligation =
  mkAuthorityRow
    "comparison-law promotion"
    comparisonLawTarget
    comparisonMethodAuthority
    consumerReceiptRequired
    comparisonLawPromotedGuard
    canonicalMetadataObligations
    ( "provider observable definition"
    ∷ "transform/projection law"
    ∷ "comparison-law receipt request"
    ∷ []
    )
    ( "comparison law theorem/adapter receipt"
    ∷ "unit and observable compatibility receipt"
    ∷ "residual-table comparison consumer receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

covarianceCalibrationObligation : AuthorityObligationRow
covarianceCalibrationObligation =
  mkAuthorityRow
    "covariance and calibration promotion"
    covarianceCalibrationTarget
    covarianceCalibrationAuthority
    consumerReceiptRequired
    covarianceCalibrationPromotedGuard
    canonicalMetadataObligations
    ( "covariance metadata"
    ∷ "unit metadata"
    ∷ "calibration metadata"
    ∷ "uncertainty metadata"
    ∷ []
    )
    ( "covariance matrix authority receipt"
    ∷ "calibration convention receipt"
    ∷ "uncertainty propagation receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

holdoutValidationObligation : AuthorityObligationRow
holdoutValidationObligation =
  mkAuthorityRow
    "holdout validation acceptance"
    holdoutValidationTarget
    holdoutProtocolAuthority
    validationTargetRequired
    holdoutValidationAcceptedGuard
    canonicalMetadataObligations
    ( "holdout dataset id"
    ∷ "holdout dataset checksum"
    ∷ "validation protocol and pass/fail criterion"
    ∷ []
    )
    ( "holdout dataset authority receipt"
    ∷ "validation protocol receipt"
    ∷ "blind or frozen evaluation log receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

runtimeReplayObligation : AuthorityObligationRow
runtimeReplayObligation =
  mkAuthorityRow
    "runtime replay authority"
    runtimeReplayTarget
    runtimeReplayAuthority
    consumerReceiptRequired
    runtimeReplayAuthorityAcceptedGuard
    canonicalMetadataObligations
    ( "runtime receipt id"
    ∷ "parser/reducer version"
    ∷ "source artifact checksum"
    ∷ "projection digest"
    ∷ "replay command and environment"
    ∷ []
    )
    ( "runtime replay receipt"
    ∷ "PNF emission receipt"
    ∷ "residual computation receipt"
    ∷ "environment lock receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

semanticAdequacyObligation : AuthorityObligationRow
semanticAdequacyObligation =
  mkAuthorityRow
    "semantic adequacy acceptance"
    semanticAdequacyTarget
    semanticReviewAuthority
    validationTargetRequired
    semanticAdequacyAcceptedGuard
    canonicalMetadataObligations
    ( "semantic adequacy review receipt"
    ∷ "non-inspection boundary review"
    ∷ "source/projection digest pair"
    ∷ []
    )
    ( "semantic review authority receipt"
    ∷ "domain reviewer or formal semantic-equivalence receipt"
    ∷ "claim-boundary update receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

empiricalAdequacyObligation : AuthorityObligationRow
empiricalAdequacyObligation =
  mkAuthorityRow
    "empirical adequacy acceptance"
    empiricalAdequacyTarget
    holdoutProtocolAuthority
    validationTargetRequired
    empiricalAdequacyAcceptedGuard
    canonicalMetadataObligations
    ( "provider authority token"
    ∷ "comparison law"
    ∷ "covariance/calibration receipt"
    ∷ "holdout validation receipt"
    ∷ "runtime replay receipt where generated projections are consumed"
    ∷ []
    )
    ( "aggregate empirical adequacy theorem/authority receipt"
    ∷ "all upstream empirical/runtime guards consumed"
    ∷ "claim-surface audit receipt"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/NumericAndAuthorityObligations.agda"
    ∷ []
    )

canonicalAuthorityRows : List AuthorityObligationRow
canonicalAuthorityRows =
  numericValueObligation
  ∷ acceptedAuthorityTokenObligation
  ∷ providerAuthorityObligation
  ∷ comparisonLawObligation
  ∷ covarianceCalibrationObligation
  ∷ holdoutValidationObligation
  ∷ runtimeReplayObligation
  ∷ semanticAdequacyObligation
  ∷ empiricalAdequacyObligation
  ∷ []

canonicalNumericAuthorityRows : List AuthorityObligationRow
canonicalNumericAuthorityRows =
  numericValueObligation
  ∷ acceptedAuthorityTokenObligation
  ∷ []

canonicalProviderRuntimeRows : List AuthorityObligationRow
canonicalProviderRuntimeRows =
  providerAuthorityObligation
  ∷ comparisonLawObligation
  ∷ covarianceCalibrationObligation
  ∷ holdoutValidationObligation
  ∷ runtimeReplayObligation
  ∷ semanticAdequacyObligation
  ∷ empiricalAdequacyObligation
  ∷ []

canonicalNumericAndAuthorityObligationIndex :
  NumericAndAuthorityObligationIndex
canonicalNumericAndAuthorityObligationIndex = record
  { indexLabel =
      "numeric measured values and authority/provider/runtime promotion obligations"
  ; sourceRegistry = Registry.repoWideConstantsRegistry
  ; sourcePolicyReceipt =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; sourceEmpiricalRuntimeReceipt =
      Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; metadataObligations = canonicalMetadataObligations
  ; authorityRows = canonicalAuthorityRows
  ; numericAuthorityRows = canonicalNumericAuthorityRows
  ; providerRuntimeRows = canonicalProviderRuntimeRows
  ; rowCount = listCount canonicalAuthorityRows
  ; numericAuthorityRowCount = listCount canonicalNumericAuthorityRows
  ; providerRuntimeRowCount = listCount canonicalProviderRuntimeRows
  ; allRowsHaveFalsePromotionGuards = true
  ; allRowsHaveFalsePromotionGuardsIsTrue = refl
  ; allRowsRequireAuthorityTokens = true
  ; allRowsRequireAuthorityTokensIsTrue = refl
  ; registryExternalInputOnly =
      Registry.ConstantsRegistry.externalInputOnly
        Registry.repoWideConstantsRegistry
  ; registryExternalInputOnlyIsTrue =
      Registry.ConstantsRegistry.externalInputOnlyIsTrue
        Registry.repoWideConstantsRegistry
  ; numericValuePromoted =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; numericValuePromotedIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; acceptedAuthorityTokenPresent =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresent
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; acceptedAuthorityTokenPresentIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresentIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; acceptedProviderAuthorityPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; acceptedProviderAuthorityPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.acceptedProviderAuthorityPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; comparisonLawPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; comparisonLawPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.comparisonLawPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; covarianceCalibrationPromoted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromoted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; covarianceCalibrationPromotedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.covarianceCalibrationPromotedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; holdoutValidationAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; holdoutValidationAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.holdoutValidationAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; runtimeReplayAuthorityAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.runtimeReplayAuthorityAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; semanticAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; semanticAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.semanticAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAccepted =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAccepted
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; empiricalAdequacyAcceptedIsFalse =
      Registry.EmpiricalRuntimeKnownInputsReferenceReceipt.empiricalAdequacyAcceptedIsFalse
        Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; authorityBoundaryReceipt =
      canonicalNumericAndAuthorityBoundaryReceipt
  ; authorityBoundaryReceiptIsCanonical = refl
  ; authorityBoundaryClaimDomainMatches =
      canonicalNumericAndAuthorityBoundaryReceiptClaimDomainMatches
  ; authorityBoundaryClaimAuthorityKindMatches =
      canonicalNumericAndAuthorityBoundaryReceiptClaimAuthorityKindMatches
  ; authorityBoundaryCandidateOnlyIsTrue =
      canonicalNumericAndAuthorityBoundaryReceiptCandidateOnlyIsTrue
  ; authorityBoundaryCandidatePromotedIsFalse =
      canonicalNumericAndAuthorityBoundaryReceiptCandidatePromotedIsFalse
  ; authorityBoundaryBlockedAuthorityKindsFalse =
      canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsFalse
  ; authorityBoundaryBlockedAuthorityKindsCountIsCanonical =
      canonicalNumericAndAuthorityBoundaryReceiptBlockedAuthorityKindsCountIsCanonical
  ; authorityBoundaryPromoted =
      AuthorityBoundary.receiptBoundaryPromoted
        canonicalNumericAndAuthorityBoundaryReceipt
  ; authorityBoundaryPromotedIsFalse =
      canonicalNumericAndAuthorityBoundaryReceiptPromotedIsFalse
  }

canonicalAuthorityRowCountIs9 :
  NumericAndAuthorityObligationIndex.rowCount
    canonicalNumericAndAuthorityObligationIndex
  ≡ 9
canonicalAuthorityRowCountIs9 = refl

canonicalNumericAuthorityRowCountIs2 :
  NumericAndAuthorityObligationIndex.numericAuthorityRowCount
    canonicalNumericAndAuthorityObligationIndex
  ≡ 2
canonicalNumericAuthorityRowCountIs2 = refl

canonicalProviderRuntimeRowCountIs7 :
  NumericAndAuthorityObligationIndex.providerRuntimeRowCount
    canonicalNumericAndAuthorityObligationIndex
  ≡ 7
canonicalProviderRuntimeRowCountIs7 = refl

canonicalMetadataObligationCountIs9 :
  listCount
    (NumericAndAuthorityObligationIndex.metadataObligations
      canonicalNumericAndAuthorityObligationIndex)
  ≡ 9
canonicalMetadataObligationCountIs9 = refl

canonicalAuthorityBoundaryReceiptIsCanonical :
  NumericAndAuthorityObligationIndex.authorityBoundaryReceipt
    canonicalNumericAndAuthorityObligationIndex
  ≡ canonicalNumericAndAuthorityBoundaryReceipt
canonicalAuthorityBoundaryReceiptIsCanonical = refl

canonicalAuthorityBoundaryReceiptCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly
    (AuthorityBoundary.receiptCandidateRow
      (NumericAndAuthorityObligationIndex.authorityBoundaryReceipt
        canonicalNumericAndAuthorityObligationIndex))
  ≡ true
canonicalAuthorityBoundaryReceiptCandidateOnlyIsTrue =
  NumericAndAuthorityObligationIndex.authorityBoundaryCandidateOnlyIsTrue
    canonicalNumericAndAuthorityObligationIndex

canonicalAuthorityBoundaryReceiptBlockedAuthorityKindsFalse :
  AuthorityNA.AllAuthorityKindsFalse
    (AuthorityBoundary.receiptAuthorityBundle
      (NumericAndAuthorityObligationIndex.authorityBoundaryReceipt
        canonicalNumericAndAuthorityObligationIndex))
    (AuthorityBoundary.receiptBlockedAuthorityKinds
      (NumericAndAuthorityObligationIndex.authorityBoundaryReceipt
        canonicalNumericAndAuthorityObligationIndex))
canonicalAuthorityBoundaryReceiptBlockedAuthorityKindsFalse =
  NumericAndAuthorityObligationIndex.authorityBoundaryBlockedAuthorityKindsFalse
    canonicalNumericAndAuthorityObligationIndex

canonicalAuthorityBoundaryReceiptBlockedAuthorityKindsCountIsCanonical :
  AuthorityBoundary.receiptBlockedAuthorityKindsCount
    (NumericAndAuthorityObligationIndex.authorityBoundaryReceipt
      canonicalNumericAndAuthorityObligationIndex)
  ≡ AuthorityBoundary.canonicalBlockedAuthorityKindCount
canonicalAuthorityBoundaryReceiptBlockedAuthorityKindsCountIsCanonical =
  NumericAndAuthorityObligationIndex.authorityBoundaryBlockedAuthorityKindsCountIsCanonical
    canonicalNumericAndAuthorityObligationIndex

canonicalAuthorityBoundaryReceiptPromotedIsFalse :
  NumericAndAuthorityObligationIndex.authorityBoundaryPromoted
    canonicalNumericAndAuthorityObligationIndex
  ≡ false
canonicalAuthorityBoundaryReceiptPromotedIsFalse =
  NumericAndAuthorityObligationIndex.authorityBoundaryPromotedIsFalse
    canonicalNumericAndAuthorityObligationIndex
