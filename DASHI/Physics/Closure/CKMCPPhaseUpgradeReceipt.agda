module DASHI.Physics.Closure.CKMCPPhaseUpgradeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM CP phase upgrade receipt.
--
-- This records the C3 diagnostic upgrade only.  The candidate
-- atan(sqrt7) * (1 - alpha1) is numerically close to the PDG central CKM
-- phase, but the receipt keeps it comparison-only: no physical CP phase,
-- physical CKM, or Vub authority is promoted here.

data CKMCPPhaseUpgradeStatus : Set where
  cpPhaseCandidateWithinOneSigmaDiagnosticOnly :
    CKMCPPhaseUpgradeStatus

data CKMCPPhaseUpgradeBlocker : Set where
  missingPhysicalCPPhaseAuthority :
    CKMCPPhaseUpgradeBlocker

  missingPhysicalVubAuthority :
    CKMCPPhaseUpgradeBlocker

  missingAcceptedWolfensteinAuthorityBinding :
    CKMCPPhaseUpgradeBlocker

canonicalCKMCPPhaseUpgradeBlockers :
  List CKMCPPhaseUpgradeBlocker
canonicalCKMCPPhaseUpgradeBlockers =
  missingPhysicalCPPhaseAuthority
  ∷ missingPhysicalVubAuthority
  ∷ missingAcceptedWolfensteinAuthorityBinding
  ∷ []

data CKMWolfensteinCandidateParameter : Set where
  lambdaCandidate :
    CKMWolfensteinCandidateParameter

  aCandidate :
    CKMWolfensteinCandidateParameter

  rhoCandidate :
    CKMWolfensteinCandidateParameter

  etaCandidate :
    CKMWolfensteinCandidateParameter

canonicalCKMWolfensteinCandidateParameters :
  List CKMWolfensteinCandidateParameter
canonicalCKMWolfensteinCandidateParameters =
  lambdaCandidate
  ∷ aCandidate
  ∷ rhoCandidate
  ∷ etaCandidate
  ∷ []

data CKMCPPhaseUpgradePromotion : Set where

ckmCPPhaseUpgradePromotionImpossibleHere :
  CKMCPPhaseUpgradePromotion →
  ⊥
ckmCPPhaseUpgradePromotionImpossibleHere ()

cpPhaseUpgradeFormula : String
cpPhaseUpgradeFormula =
  "delta_CP candidate = atan(sqrt7) * (1 - alpha1)"

cpPhaseUpgradeStatement : String
cpPhaseUpgradeStatement =
  "C3 records a CKM CP phase candidate atan(sqrt7)*(1-alpha1)=1.1596 rad versus PDG central 1.144 rad, within 1sigma; this is diagnostic candidate data only, physical CP promotion is false, all four Wolfenstein parameters have candidates, and Vub remains pending."

record CKMCPPhaseUpgradeReceipt : Setω where
  field
    status :
      CKMCPPhaseUpgradeStatus

    statusIsDiagnosticOnly :
      status ≡ cpPhaseCandidateWithinOneSigmaDiagnosticOnly

    phaseFormula :
      String

    phaseFormulaIsCanonical :
      phaseFormula ≡ cpPhaseUpgradeFormula

    candidatePhaseRadians :
      Float

    candidatePhaseRadiansIsCanonical :
      candidatePhaseRadians ≡ 1.1596

    pdgCentralPhaseRadians :
      Float

    pdgCentralPhaseRadiansIsCanonical :
      pdgCentralPhaseRadians ≡ 1.144

    candidateWithinOneSigma :
      Bool

    candidateWithinOneSigmaIsTrue :
      candidateWithinOneSigma ≡ true

    diagnosticCandidateOnly :
      Bool

    diagnosticCandidateOnlyIsTrue :
      diagnosticCandidateOnly ≡ true

    physicalCPPhasePromoted :
      Bool

    physicalCPPhasePromotedIsFalse :
      physicalCPPhasePromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    wolfensteinCandidateParameters :
      List CKMWolfensteinCandidateParameter

    wolfensteinCandidateParametersAreCanonical :
      wolfensteinCandidateParameters
      ≡
      canonicalCKMWolfensteinCandidateParameters

    allFourWolfensteinParametersHaveCandidates :
      Bool

    allFourWolfensteinParametersHaveCandidatesIsTrue :
      allFourWolfensteinParametersHaveCandidates ≡ true

    vubPending :
      Bool

    vubPendingIsTrue :
      vubPending ≡ true

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    blockers :
      List CKMCPPhaseUpgradeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMCPPhaseUpgradeBlockers

    statement :
      String

    statementIsCanonical :
      statement ≡ cpPhaseUpgradeStatement

    promotionFlags :
      List CKMCPPhaseUpgradePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMCPPhaseUpgradeReceipt public

canonicalCKMCPPhaseUpgradeReceipt :
  CKMCPPhaseUpgradeReceipt
canonicalCKMCPPhaseUpgradeReceipt =
  record
    { status =
        cpPhaseCandidateWithinOneSigmaDiagnosticOnly
    ; statusIsDiagnosticOnly =
        refl
    ; phaseFormula =
        cpPhaseUpgradeFormula
    ; phaseFormulaIsCanonical =
        refl
    ; candidatePhaseRadians =
        1.1596
    ; candidatePhaseRadiansIsCanonical =
        refl
    ; pdgCentralPhaseRadians =
        1.144
    ; pdgCentralPhaseRadiansIsCanonical =
        refl
    ; candidateWithinOneSigma =
        true
    ; candidateWithinOneSigmaIsTrue =
        refl
    ; diagnosticCandidateOnly =
        true
    ; diagnosticCandidateOnlyIsTrue =
        refl
    ; physicalCPPhasePromoted =
        false
    ; physicalCPPhasePromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; wolfensteinCandidateParameters =
        canonicalCKMWolfensteinCandidateParameters
    ; wolfensteinCandidateParametersAreCanonical =
        refl
    ; allFourWolfensteinParametersHaveCandidates =
        true
    ; allFourWolfensteinParametersHaveCandidatesIsTrue =
        refl
    ; vubPending =
        true
    ; vubPendingIsTrue =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMCPPhaseUpgradeBlockers
    ; blockersAreCanonical =
        refl
    ; statement =
        cpPhaseUpgradeStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "CP phase candidate atan(sqrt7)*(1-alpha1)=1.1596 rad is recorded"
        ∷ "PDG central comparison is 1.144 rad and the candidate is marked within 1sigma"
        ∷ "The phase is diagnostic candidate data only"
        ∷ "All four Wolfenstein parameters have candidates"
        ∷ "Vub remains pending; physical CP, Vub, and CKM promotion remain false"
        ∷ []
    }

ckmCPPhaseUpgradeWithinOneSigma :
  candidateWithinOneSigma canonicalCKMCPPhaseUpgradeReceipt ≡ true
ckmCPPhaseUpgradeWithinOneSigma =
  refl

ckmCPPhaseUpgradeDoesNotPromotePhysicalCP :
  physicalCPPhasePromoted canonicalCKMCPPhaseUpgradeReceipt ≡ false
ckmCPPhaseUpgradeDoesNotPromotePhysicalCP =
  refl

ckmCPPhaseUpgradeKeepsVubPending :
  vubPending canonicalCKMCPPhaseUpgradeReceipt ≡ true
ckmCPPhaseUpgradeKeepsVubPending =
  refl

ckmCPPhaseUpgradeNoPromotion :
  CKMCPPhaseUpgradePromotion →
  ⊥
ckmCPPhaseUpgradeNoPromotion =
  ckmCPPhaseUpgradePromotionImpossibleHere
