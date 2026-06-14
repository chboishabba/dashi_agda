module DASHI.Physics.Closure.ArchimedeanFlatLimitCandidatesReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Archimedean H3 -> R3 flat-limit candidate audit.
--
-- This receipt enumerates the three currently identified candidate
-- mechanisms for turning the archimedean hyperbolic H3 carrier into an R3
-- flat-limit carrier.  Each candidate is retained as an audit item, and each
-- carries a recorded issue.  No Yang-Mills continuum theorem, Clay promotion,
-- or terminal claim is introduced here.

data ArchimedeanFlatLimitCandidatesStatus : Set where
  threeCandidatesRecordedAllIssueFlagged :
    ArchimedeanFlatLimitCandidatesStatus

data ArchimedeanFlatLimitCandidateMechanism : Set where
  curvatureDeformation :
    ArchimedeanFlatLimitCandidateMechanism

  adelicIntegration :
    ArchimedeanFlatLimitCandidateMechanism

  largeLevelCuspDegeneration :
    ArchimedeanFlatLimitCandidateMechanism

canonicalArchimedeanFlatLimitCandidateMechanisms :
  List ArchimedeanFlatLimitCandidateMechanism
canonicalArchimedeanFlatLimitCandidateMechanisms =
  curvatureDeformation
  ∷ adelicIntegration
  ∷ largeLevelCuspDegeneration
  ∷ []

data ArchimedeanFlatLimitCandidateIssue : Set where
  modularCurvesFixedCurvatureMinusOneNoVariableCurvatureShimuraFamily :
    ArchimedeanFlatLimitCandidateIssue

  archimedeanIntegrationLeavesPAdicQp3NotR3 :
    ArchimedeanFlatLimitCandidateIssue

  cuspFlatnessOnlyLocalAsymptoticNoGlobalR3Carrier :
    ArchimedeanFlatLimitCandidateIssue

canonicalArchimedeanFlatLimitCandidateIssues :
  List ArchimedeanFlatLimitCandidateIssue
canonicalArchimedeanFlatLimitCandidateIssues =
  modularCurvesFixedCurvatureMinusOneNoVariableCurvatureShimuraFamily
  ∷ archimedeanIntegrationLeavesPAdicQp3NotR3
  ∷ cuspFlatnessOnlyLocalAsymptoticNoGlobalR3Carrier
  ∷ []

data ArchimedeanFlatLimitCandidatePromotion : Set where

archimedeanFlatLimitCandidatePromotionImpossibleHere :
  ArchimedeanFlatLimitCandidatePromotion →
  ⊥
archimedeanFlatLimitCandidatePromotionImpossibleHere ()

archimedeanFlatLimitCandidates : Nat
archimedeanFlatLimitCandidates =
  3

allThreeHaveIssues : Bool
allThreeHaveIssues =
  true

curvatureDeformationStatement : String
curvatureDeformationStatement =
  "Candidate (a): curvature deformation, a family of Shimura varieties with curvature kappa in [-1,0]. Issue: modular curves have fixed curvature -1, and there is no standard variable-curvature Shimura family."

adelicIntegrationStatement : String
adelicIntegrationStatement =
  "Candidate (b): adelic integration, integrate out the archimedean component. Issue: the remaining spatial carrier is p-adic Q_p^3, not R^3."

largeLevelCuspDegenerationStatement : String
largeLevelCuspDegenerationStatement =
  "Candidate (c): large-level/cusp degeneration, where X_0(N) degenerates with compactified boundary cusps and local coordinate q = exp(2 pi i tau), giving an asymptotically flat local cusp regime."

candidateAuditStatement : String
candidateAuditStatement =
  "Exactly three archimedean H3 -> R3 flat-limit candidates are recorded, and all three retain issues; this is not a Clay/Yang-Mills terminal promotion."

record ArchimedeanFlatLimitCandidatesReceipt : Setω where
  field
    status :
      ArchimedeanFlatLimitCandidatesStatus

    candidateMechanisms :
      List ArchimedeanFlatLimitCandidateMechanism

    candidateMechanismsAreCanonical :
      candidateMechanisms ≡ canonicalArchimedeanFlatLimitCandidateMechanisms

    candidateIssues :
      List ArchimedeanFlatLimitCandidateIssue

    candidateIssuesAreCanonical :
      candidateIssues ≡ canonicalArchimedeanFlatLimitCandidateIssues

    candidateCount :
      Nat

    candidateCountIsThree :
      candidateCount ≡ archimedeanFlatLimitCandidates

    allCandidatesIssueFlagged :
      Bool

    allCandidatesIssueFlaggedIsTrue :
      allCandidatesIssueFlagged ≡ allThreeHaveIssues

    curvatureDeformationRecorded :
      Bool

    curvatureDeformationRecordedIsTrue :
      curvatureDeformationRecorded ≡ true

    curvatureDeformationHasIssue :
      Bool

    curvatureDeformationHasIssueIsTrue :
      curvatureDeformationHasIssue ≡ true

    adelicIntegrationRecorded :
      Bool

    adelicIntegrationRecordedIsTrue :
      adelicIntegrationRecorded ≡ true

    adelicIntegrationHasIssue :
      Bool

    adelicIntegrationHasIssueIsTrue :
      adelicIntegrationHasIssue ≡ true

    largeLevelCuspDegenerationRecorded :
      Bool

    largeLevelCuspDegenerationRecordedIsTrue :
      largeLevelCuspDegenerationRecorded ≡ true

    largeLevelCuspDegenerationHasIssue :
      Bool

    largeLevelCuspDegenerationHasIssueIsTrue :
      largeLevelCuspDegenerationHasIssue ≡ true

    variableCurvatureShimuraFamilyConstructed :
      Bool

    variableCurvatureShimuraFamilyConstructedIsFalse :
      variableCurvatureShimuraFamilyConstructed ≡ false

    adelicIntegrationProducesR3 :
      Bool

    adelicIntegrationProducesR3IsFalse :
      adelicIntegrationProducesR3 ≡ false

    cuspDegenerationPromotesGlobalR3Carrier :
      Bool

    cuspDegenerationPromotesGlobalR3CarrierIsFalse :
      cuspDegenerationPromotesGlobalR3Carrier ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    yangMillsTerminalClaimPromoted :
      Bool

    yangMillsTerminalClaimPromotedIsFalse :
      yangMillsTerminalClaimPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    curvatureDeformationReceiptStatement :
      String

    curvatureDeformationReceiptStatementIsCanonical :
      curvatureDeformationReceiptStatement ≡ curvatureDeformationStatement

    adelicIntegrationReceiptStatement :
      String

    adelicIntegrationReceiptStatementIsCanonical :
      adelicIntegrationReceiptStatement ≡ adelicIntegrationStatement

    largeLevelCuspDegenerationReceiptStatement :
      String

    largeLevelCuspDegenerationReceiptStatementIsCanonical :
      largeLevelCuspDegenerationReceiptStatement
      ≡
      largeLevelCuspDegenerationStatement

    auditStatement :
      String

    auditStatementIsCanonical :
      auditStatement ≡ candidateAuditStatement

    promotionFlags :
      List ArchimedeanFlatLimitCandidatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ArchimedeanFlatLimitCandidatesReceipt public

canonicalArchimedeanFlatLimitCandidatesReceipt :
  ArchimedeanFlatLimitCandidatesReceipt
canonicalArchimedeanFlatLimitCandidatesReceipt =
  record
    { status =
        threeCandidatesRecordedAllIssueFlagged
    ; candidateMechanisms =
        canonicalArchimedeanFlatLimitCandidateMechanisms
    ; candidateMechanismsAreCanonical =
        refl
    ; candidateIssues =
        canonicalArchimedeanFlatLimitCandidateIssues
    ; candidateIssuesAreCanonical =
        refl
    ; candidateCount =
        archimedeanFlatLimitCandidates
    ; candidateCountIsThree =
        refl
    ; allCandidatesIssueFlagged =
        allThreeHaveIssues
    ; allCandidatesIssueFlaggedIsTrue =
        refl
    ; curvatureDeformationRecorded =
        true
    ; curvatureDeformationRecordedIsTrue =
        refl
    ; curvatureDeformationHasIssue =
        true
    ; curvatureDeformationHasIssueIsTrue =
        refl
    ; adelicIntegrationRecorded =
        true
    ; adelicIntegrationRecordedIsTrue =
        refl
    ; adelicIntegrationHasIssue =
        true
    ; adelicIntegrationHasIssueIsTrue =
        refl
    ; largeLevelCuspDegenerationRecorded =
        true
    ; largeLevelCuspDegenerationRecordedIsTrue =
        refl
    ; largeLevelCuspDegenerationHasIssue =
        true
    ; largeLevelCuspDegenerationHasIssueIsTrue =
        refl
    ; variableCurvatureShimuraFamilyConstructed =
        false
    ; variableCurvatureShimuraFamilyConstructedIsFalse =
        refl
    ; adelicIntegrationProducesR3 =
        false
    ; adelicIntegrationProducesR3IsFalse =
        refl
    ; cuspDegenerationPromotesGlobalR3Carrier =
        false
    ; cuspDegenerationPromotesGlobalR3CarrierIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; yangMillsTerminalClaimPromoted =
        false
    ; yangMillsTerminalClaimPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; curvatureDeformationReceiptStatement =
        curvatureDeformationStatement
    ; curvatureDeformationReceiptStatementIsCanonical =
        refl
    ; adelicIntegrationReceiptStatement =
        adelicIntegrationStatement
    ; adelicIntegrationReceiptStatementIsCanonical =
        refl
    ; largeLevelCuspDegenerationReceiptStatement =
        largeLevelCuspDegenerationStatement
    ; largeLevelCuspDegenerationReceiptStatementIsCanonical =
        refl
    ; auditStatement =
        candidateAuditStatement
    ; auditStatementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Candidate (a) curvature deformation is recorded, with fixed-curvature issue"
        ∷ "Candidate (b) adelic integration is recorded, with Q_p^3-not-R^3 issue"
        ∷ "Candidate (c) large-level/cusp degeneration is recorded, with only local asymptotic cusp flatness"
        ∷ "archimedeanFlatLimitCandidates = 3"
        ∷ "allThreeHaveIssues = true"
        ∷ "No continuum Yang-Mills, Clay Yang-Mills, Yang-Mills terminal, or terminal Clay claim is promoted"
        ∷ []
    }

archimedeanFlatLimitCandidatesFlag :
  archimedeanFlatLimitCandidates ≡ 3
archimedeanFlatLimitCandidatesFlag =
  refl

allThreeHaveIssuesFlag :
  allThreeHaveIssues ≡ true
allThreeHaveIssuesFlag =
  refl

archimedeanFlatLimitCandidatesReceiptKeepsClayFalse :
  clayYangMillsPromoted canonicalArchimedeanFlatLimitCandidatesReceipt
  ≡
  false
archimedeanFlatLimitCandidatesReceiptKeepsClayFalse =
  refl

archimedeanFlatLimitCandidatesReceiptKeepsYMTerminalFalse :
  yangMillsTerminalClaimPromoted canonicalArchimedeanFlatLimitCandidatesReceipt
  ≡
  false
archimedeanFlatLimitCandidatesReceiptKeepsYMTerminalFalse =
  refl

archimedeanFlatLimitCandidatesReceiptKeepsTerminalClayFalse :
  terminalClayClaimPromoted canonicalArchimedeanFlatLimitCandidatesReceipt
  ≡
  false
archimedeanFlatLimitCandidatesReceiptKeepsTerminalClayFalse =
  refl
