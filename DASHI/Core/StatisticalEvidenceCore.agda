module DASHI.Core.StatisticalEvidenceCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as AuthorityNA
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Core.FormalLensQualificationCore as FormalLensCore
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Promotion.AuthorityBoundaryCore as AuthorityBoundary

------------------------------------------------------------------------
-- Statistical evidence core.
--
-- Probability is kept distinct from statistical evidence.  The module
-- records a candidate-only statistical surface, a named formal-lens
-- vocabulary for statistical, inference, and robust evidence, and explicit
-- fail-closed gates that refuse theorem authority, certainty, causal proof,
-- clinical authority, prediction guarantee, and promotion authority.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Statistical vocabulary.

data StatisticalEvidenceKind : Set where
  statisticalEvidenceKind :
    StatisticalEvidenceKind

  inferenceKind :
    StatisticalEvidenceKind

  robustEvidenceKind :
    StatisticalEvidenceKind

  observationCarrierKind :
    StatisticalEvidenceKind

  statisticKind :
    StatisticalEvidenceKind

  estimatorKind :
    StatisticalEvidenceKind

  confidenceIntervalKind :
    StatisticalEvidenceKind

  hypothesisTestKind :
    StatisticalEvidenceKind

  decisionRuleKind :
    StatisticalEvidenceKind

  robustFilterKind :
    StatisticalEvidenceKind

  outlierKind :
    StatisticalEvidenceKind

  contaminationKind :
    StatisticalEvidenceKind

  uncertaintyKind :
    StatisticalEvidenceKind

  residualKind :
    StatisticalEvidenceKind

  probabilityKind :
    StatisticalEvidenceKind

  namedStatisticalEvidenceKind :
    String →
    StatisticalEvidenceKind

canonicalStatisticalEvidenceVocabulary : List StatisticalEvidenceKind
canonicalStatisticalEvidenceVocabulary =
  statisticalEvidenceKind
  ∷ inferenceKind
  ∷ robustEvidenceKind
  ∷ observationCarrierKind
  ∷ statisticKind
  ∷ estimatorKind
  ∷ confidenceIntervalKind
  ∷ hypothesisTestKind
  ∷ decisionRuleKind
  ∷ robustFilterKind
  ∷ outlierKind
  ∷ contaminationKind
  ∷ uncertaintyKind
  ∷ residualKind
  ∷ probabilityKind
  ∷ []

canonicalStatisticalEvidenceVocabularyCount : Nat
canonicalStatisticalEvidenceVocabularyCount =
  listCount canonicalStatisticalEvidenceVocabulary

------------------------------------------------------------------------
-- Formal-lens coverage.

canonicalStatisticalEvidenceFormalLenses : List FormalLensCore.FormalLens
canonicalStatisticalEvidenceFormalLenses =
  FormalLensCore.NamedFormalLens "statistical evidence"
  ∷ FormalLensCore.NamedFormalLens "inference"
  ∷ FormalLensCore.NamedFormalLens "robust evidence"
  ∷ FormalLensCore.NamedFormalLens "observation carrier"
  ∷ FormalLensCore.NamedFormalLens "statistic"
  ∷ FormalLensCore.NamedFormalLens "estimator"
  ∷ FormalLensCore.NamedFormalLens "confidence interval"
  ∷ FormalLensCore.NamedFormalLens "hypothesis test"
  ∷ FormalLensCore.NamedFormalLens "decision rule"
  ∷ FormalLensCore.NamedFormalLens "robust filter"
  ∷ FormalLensCore.NamedFormalLens "outlier"
  ∷ FormalLensCore.NamedFormalLens "contamination"
  ∷ FormalLensCore.NamedFormalLens "uncertainty"
  ∷ FormalLensCore.NamedFormalLens "residual"
  ∷ FormalLensCore.NamedFormalLens "probability"
  ∷ []

canonicalStatisticalEvidenceFormalLensCount : Nat
canonicalStatisticalEvidenceFormalLensCount =
  listCount canonicalStatisticalEvidenceFormalLenses

------------------------------------------------------------------------
-- Boundary claims.

canonicalStatisticalEvidenceBoundaryClaims :
  List AuthorityBoundary.AuthorityBoundaryClaimKind
canonicalStatisticalEvidenceBoundaryClaims =
  AuthorityBoundary.clinicalAuthorityClaim
  ∷ AuthorityBoundary.runtimeAuthorityClaim
  ∷ []

canonicalStatisticalEvidenceBoundaryClaimCount : Nat
canonicalStatisticalEvidenceBoundaryClaimCount =
  listCount canonicalStatisticalEvidenceBoundaryClaims

------------------------------------------------------------------------
-- Candidate surface.

canonicalStatisticalEvidenceCandidateRow : CandidateOnly.CandidateOnlyRow
canonicalStatisticalEvidenceCandidateRow =
  CandidateOnly.mkCandidateOnlyRow
    "statistical evidence candidate"
    "DASHI.Core.StatisticalEvidenceCore"
    "canonicalStatisticalEvidenceCandidateRow"
    CandidateOnly.diagnosticCandidateKind
    CandidateOnly.diagnosticCandidateOnlyStatus
    "statistical evidence is a candidate-only observation and inference surface"
    "probability is distinct from statistical evidence; theorem, certainty, causal proof, clinical authority, prediction guarantee, and promotion authority remain closed"

canonicalStatisticalEvidenceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalStatisticalEvidenceCandidateRow
canonicalStatisticalEvidenceCandidateReceipt =
  CandidateOnly.canonicalCandidateOnlyReceipt
    canonicalStatisticalEvidenceCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Statistical evidence surface and receipt.

record StatisticalEvidenceSurface : Set where
  constructor statisticalEvidenceSurface
  field
    evidenceLabel :
      String

    evidenceOwner :
      String

    evidenceSurface :
      String

    evidenceVocabulary :
      List StatisticalEvidenceKind

    evidenceFormalLenses :
      List FormalLensCore.FormalLens

    evidenceCandidateRow :
      CandidateOnly.CandidateOnlyRow

    evidenceCandidateReceipt :
      CandidateOnly.CandidateOnlyReceipt evidenceCandidateRow

    evidenceAuthorityBundle :
      AuthorityNA.AuthorityNonPromotionBundle

    evidenceBoundaryClaims :
      List AuthorityBoundary.AuthorityBoundaryClaimKind

    probabilityDistinctFromStatistical :
      Bool

    probabilityDistinctFromStatisticalIsTrue :
      probabilityDistinctFromStatistical ≡ true

    certaintyAuthority :
      Bool

    certaintyAuthorityIsFalse :
      certaintyAuthority ≡ false

    causalProofAuthority :
      Bool

    causalProofAuthorityIsFalse :
      causalProofAuthority ≡ false

    predictionGuaranteeAuthority :
      Bool

    predictionGuaranteeAuthorityIsFalse :
      predictionGuaranteeAuthority ≡ false

    evidenceStatement :
      String

    evidenceRemainingGap :
      String

open StatisticalEvidenceSurface public

record StatisticalEvidenceReceipt
  (surface : StatisticalEvidenceSurface) :
  Set where
  constructor statisticalEvidenceReceipt
  field
    receiptCandidateReceiptPresent :
      CandidateOnly.CandidateOnlyReceipt (evidenceCandidateRow surface)

    receiptCandidateOnlyIsTrue :
      CandidateOnly.candidateOnly (evidenceCandidateRow surface) ≡ true

    receiptPromotedIsFalse :
      CandidateOnly.promoted (evidenceCandidateRow surface) ≡ false

    receiptTheoremAuthorityIsFalse :
      AuthorityNA.theoremAuthorityFlag
        (evidenceAuthorityBundle surface)
      ≡
      false

    receiptClinicalAuthorityIsFalse :
      AuthorityNA.clinicalAuthorityFlag
        (evidenceAuthorityBundle surface)
      ≡
      false

    receiptPromotesAnyAuthorityIsFalse :
      AuthorityNA.promotesAnyAuthority
        (evidenceAuthorityBundle surface)
      ≡
      false

    receiptProbabilityDistinctFromStatisticalIsTrue :
      probabilityDistinctFromStatistical surface ≡ true

    receiptCertaintyAuthorityIsFalse :
      certaintyAuthority surface ≡ false

    receiptCausalProofAuthorityIsFalse :
      causalProofAuthority surface ≡ false

    receiptPredictionGuaranteeAuthorityIsFalse :
      predictionGuaranteeAuthority surface ≡ false

    receiptBoundaryClaimsCanonical :
      evidenceBoundaryClaims surface
      ≡
      canonicalStatisticalEvidenceBoundaryClaims

    receiptFormalLensesCanonical :
      evidenceFormalLenses surface
      ≡
      canonicalStatisticalEvidenceFormalLenses

    receiptVocabularyCanonical :
      evidenceVocabulary surface
      ≡
      canonicalStatisticalEvidenceVocabulary

open StatisticalEvidenceReceipt public

mkStatisticalEvidenceSurface :
  String →
  String →
  String →
  List StatisticalEvidenceKind →
  List FormalLensCore.FormalLens →
  (candidateRow : CandidateOnly.CandidateOnlyRow) →
  CandidateOnly.CandidateOnlyReceipt candidateRow →
  AuthorityNA.AuthorityNonPromotionBundle →
  List AuthorityBoundary.AuthorityBoundaryClaimKind →
  (probabilityDistinct : Bool) →
  (probabilityDistinctIsTrue : probabilityDistinct ≡ true) →
  (certaintyAuthorityValue : Bool) →
  (certaintyAuthorityValueIsFalse : certaintyAuthorityValue ≡ false) →
  (causalProofAuthorityValue : Bool) →
  (causalProofAuthorityValueIsFalse : causalProofAuthorityValue ≡ false) →
  (predictionGuaranteeAuthorityValue : Bool) →
  (predictionGuaranteeAuthorityValueIsFalse : predictionGuaranteeAuthorityValue ≡ false) →
  String →
  String →
  StatisticalEvidenceSurface
mkStatisticalEvidenceSurface
  label
  owner
  surface
  vocabulary
  formalLenses
  candidateRow
  candidateReceipt
  authorityBundle
  boundaryClaims
  probabilityDistinct
  probabilityDistinctIsTrue
  certaintyAuthorityValue
  certaintyAuthorityValueIsFalse
  causalProofAuthorityValue
  causalProofAuthorityValueIsFalse
  predictionGuaranteeAuthorityValue
  predictionGuaranteeAuthorityValueIsFalse
  statement
  remainingGap =
  statisticalEvidenceSurface
    label
    owner
    surface
    vocabulary
    formalLenses
    candidateRow
    candidateReceipt
    authorityBundle
    boundaryClaims
    probabilityDistinct
    probabilityDistinctIsTrue
    certaintyAuthorityValue
    certaintyAuthorityValueIsFalse
    causalProofAuthorityValue
    causalProofAuthorityValueIsFalse
    predictionGuaranteeAuthorityValue
    predictionGuaranteeAuthorityValueIsFalse
    statement
    remainingGap

mkStatisticalEvidenceReceipt :
  (surface : StatisticalEvidenceSurface) →
  CandidateOnly.CandidateOnlyReceipt (evidenceCandidateRow surface) →
  CandidateOnly.candidateOnly (evidenceCandidateRow surface) ≡ true →
  CandidateOnly.promoted (evidenceCandidateRow surface) ≡ false →
  AuthorityNA.theoremAuthorityFlag
    (evidenceAuthorityBundle surface)
  ≡
  false →
  AuthorityNA.clinicalAuthorityFlag
    (evidenceAuthorityBundle surface)
  ≡
  false →
  AuthorityNA.promotesAnyAuthority
    (evidenceAuthorityBundle surface)
  ≡
  false →
  probabilityDistinctFromStatistical surface ≡ true →
  certaintyAuthority surface ≡ false →
  causalProofAuthority surface ≡ false →
  predictionGuaranteeAuthority surface ≡ false →
  evidenceBoundaryClaims surface
  ≡
  canonicalStatisticalEvidenceBoundaryClaims →
  evidenceFormalLenses surface
  ≡
  canonicalStatisticalEvidenceFormalLenses →
  evidenceVocabulary surface
  ≡
  canonicalStatisticalEvidenceVocabulary →
  StatisticalEvidenceReceipt surface
mkStatisticalEvidenceReceipt
  surface
  candidateReceiptProof
  candidateOnlyProof
  promotedProof
  theoremProof
  clinicalProof
  promotesProof
  probabilityProof
  certaintyProof
  causalProof
  predictionProof
  boundaryProof
  formalLensesProof
  vocabularyProof =
  statisticalEvidenceReceipt
    candidateReceiptProof
    candidateOnlyProof
    promotedProof
    theoremProof
    clinicalProof
    promotesProof
    probabilityProof
    certaintyProof
    causalProof
    predictionProof
    boundaryProof
    formalLensesProof
    vocabularyProof

canonicalStatisticalEvidenceSurface :
  StatisticalEvidenceSurface
canonicalStatisticalEvidenceSurface =
  mkStatisticalEvidenceSurface
    "statistical evidence"
    "DASHI.Core.StatisticalEvidenceCore"
    "canonicalStatisticalEvidenceSurface"
    canonicalStatisticalEvidenceVocabulary
    canonicalStatisticalEvidenceFormalLenses
    canonicalStatisticalEvidenceCandidateRow
    canonicalStatisticalEvidenceCandidateReceipt
    AuthorityNA.canonicalAuthorityNonPromotionBundle
    canonicalStatisticalEvidenceBoundaryClaims
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    "statistical evidence is candidate-only bookkeeping over observation carriers, statistics, estimators, intervals, tests, decision rules, robust filters, outliers, contamination, uncertainty, and residuals"
    "probability stays distinct from statistical evidence; theorem, certainty, causal proof, clinical authority, prediction guarantee, and promotion authority stay closed"

canonicalStatisticalEvidenceReceipt :
  StatisticalEvidenceReceipt canonicalStatisticalEvidenceSurface
canonicalStatisticalEvidenceReceipt =
  mkStatisticalEvidenceReceipt
    canonicalStatisticalEvidenceSurface
    canonicalStatisticalEvidenceCandidateReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Projection lemmas.

statisticalEvidenceCandidateReceiptCanonical :
  evidenceCandidateReceipt canonicalStatisticalEvidenceSurface
  ≡
  canonicalStatisticalEvidenceCandidateReceipt
statisticalEvidenceCandidateReceiptCanonical =
  refl

statisticalEvidenceCandidateOnlyIsTrue :
  CandidateOnly.candidateOnly
    (evidenceCandidateRow canonicalStatisticalEvidenceSurface)
  ≡
  true
statisticalEvidenceCandidateOnlyIsTrue =
  receiptCandidateOnlyIsTrue canonicalStatisticalEvidenceReceipt

statisticalEvidencePromotedIsFalse :
  CandidateOnly.promoted
    (evidenceCandidateRow canonicalStatisticalEvidenceSurface)
  ≡
  false
statisticalEvidencePromotedIsFalse =
  receiptPromotedIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidenceTheoremAuthorityIsFalse :
  AuthorityNA.theoremAuthorityFlag
    (evidenceAuthorityBundle canonicalStatisticalEvidenceSurface)
  ≡
  false
statisticalEvidenceTheoremAuthorityIsFalse =
  receiptTheoremAuthorityIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidenceClinicalAuthorityIsFalse :
  AuthorityNA.clinicalAuthorityFlag
    (evidenceAuthorityBundle canonicalStatisticalEvidenceSurface)
  ≡
  false
statisticalEvidenceClinicalAuthorityIsFalse =
  receiptClinicalAuthorityIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidencePromotesAnyAuthorityIsFalse :
  AuthorityNA.promotesAnyAuthority
    (evidenceAuthorityBundle canonicalStatisticalEvidenceSurface)
  ≡
  false
statisticalEvidencePromotesAnyAuthorityIsFalse =
  receiptPromotesAnyAuthorityIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidenceProbabilityDistinctFromStatisticalIsTrue :
  probabilityDistinctFromStatistical canonicalStatisticalEvidenceSurface
  ≡
  true
statisticalEvidenceProbabilityDistinctFromStatisticalIsTrue =
  receiptProbabilityDistinctFromStatisticalIsTrue
    canonicalStatisticalEvidenceReceipt

statisticalEvidenceCertaintyAuthorityIsFalse :
  certaintyAuthority canonicalStatisticalEvidenceSurface ≡ false
statisticalEvidenceCertaintyAuthorityIsFalse =
  receiptCertaintyAuthorityIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidenceCausalProofAuthorityIsFalse :
  causalProofAuthority canonicalStatisticalEvidenceSurface ≡ false
statisticalEvidenceCausalProofAuthorityIsFalse =
  receiptCausalProofAuthorityIsFalse canonicalStatisticalEvidenceReceipt

statisticalEvidencePredictionGuaranteeAuthorityIsFalse :
  predictionGuaranteeAuthority canonicalStatisticalEvidenceSurface ≡ false
statisticalEvidencePredictionGuaranteeAuthorityIsFalse =
  receiptPredictionGuaranteeAuthorityIsFalse
    canonicalStatisticalEvidenceReceipt

statisticalEvidenceBoundaryClaimsCanonical :
  evidenceBoundaryClaims canonicalStatisticalEvidenceSurface
  ≡
  canonicalStatisticalEvidenceBoundaryClaims
statisticalEvidenceBoundaryClaimsCanonical =
  receiptBoundaryClaimsCanonical canonicalStatisticalEvidenceReceipt

statisticalEvidenceFormalLensesCanonical :
  evidenceFormalLenses canonicalStatisticalEvidenceSurface
  ≡
  canonicalStatisticalEvidenceFormalLenses
statisticalEvidenceFormalLensesCanonical =
  receiptFormalLensesCanonical canonicalStatisticalEvidenceReceipt

statisticalEvidenceVocabularyCanonical :
  evidenceVocabulary canonicalStatisticalEvidenceSurface
  ≡
  canonicalStatisticalEvidenceVocabulary
statisticalEvidenceVocabularyCanonical =
  receiptVocabularyCanonical canonicalStatisticalEvidenceReceipt

------------------------------------------------------------------------
-- Generic receipt adapter.

statisticalEvidenceGenericReceipt :
  StatisticalEvidenceSurface →
  GenericReceipt.GenericReceipt
statisticalEvidenceGenericReceipt surface =
  GenericReceipt.mkNonPromotingReceipt
    (evidenceLabel surface)
    (evidenceOwner surface)
    (evidenceSurface surface)
    (evidenceStatement surface)
    (evidenceRemainingGap surface)
    "agda -i . DASHI/Core/StatisticalEvidenceCore.agda"

canonicalStatisticalEvidenceGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalStatisticalEvidenceGenericReceipt =
  statisticalEvidenceGenericReceipt
    canonicalStatisticalEvidenceSurface

canonicalStatisticalEvidenceGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalStatisticalEvidenceGenericReceipt
  ≡
  false
canonicalStatisticalEvidenceGenericReceiptNonPromoting =
  refl
