module DASHI.Physics.Closure.NSKappaBiasVariationalHarnessResult where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS kappa-bias variational harness result receipt.
--
-- Source receipt:
--
--   outputs/ns_kappa_bias_variational_summary.json
--
-- Harness:
--
--   scripts/ns_kappa_bias_variational_harness.py
--
-- Scope:
--
--   finite S2 variational proxy, not a PDE proof.
--
-- Latest recorded values:
--
--   max_bias_unconstrained             =  0.2407495053615816
--   max_bias_LRT_constrained           =  0.2407495053615816
--   max_bias_stationary_proxy          = -0.03522081297975654
--   max_bias_LRT_and_stationary_proxy  = -0.025449723525345455
--
-- Interpretation:
--
--   Unconstrained and LRT-only top-tail selection can keep positive
--   kappa-bias.  The sampled great-circle hitting proxy therefore does not
--   kill positive bias by itself.
--
--   The one-step true-Leray direction-transport stationarity proxy is the
--   decisive finite constraint in this receipt: stationary-only and
--   LRT-plus-stationary selections are both negative in the latest run.
--
--   This is evidence for NSTypeIBlowupKappaBiasBound only.  It proves no
--   Abel triadic defect measure construction, no Type-I/self-similar PDE
--   stationarity theorem, no residual depletion estimate, no CKN/BKM
--   closure, no Navier-Stokes Clay result, and no terminal promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Receipt source and numeric payload.

sourceJsonPath : String
sourceJsonPath =
  "outputs/ns_kappa_bias_variational_summary.json"

harnessScriptPath : String
harnessScriptPath =
  "scripts/ns_kappa_bias_variational_harness.py"

harnessName : String
harnessName =
  "ns_kappa_bias_variational_harness"

seedReceipt : String
seedReceipt =
  "20260608"

requestedSamplesReceipt : String
requestedSamplesReceipt =
  "12000"

acceptedSamplesReceipt : String
acceptedSamplesReceipt =
  "12000"

selectedCountPerRegimeReceipt : String
selectedCountPerRegimeReceipt =
  "600"

biasDefinitionReceipt : String
biasDefinitionReceipt =
  "lambda_weight*(kappa^2-1/2)"

kappaDefinitionReceipt : String
kappaDefinitionReceipt =
  "dot(normalize(P_c b), omega_hat(c))"

lambdaWeightDefinitionReceipt : String
lambdaWeightDefinitionReceipt =
  "sqrt(m11^2+m12^2) from ns_s2_biot_savart_eigenbundle.angular_eigenbundle"

scopeReceipt : String
scopeReceipt =
  "finite_s2_variational_proxy_not_pde_proof"

data BiasRegime : Set where
  unconstrainedRegime :
    BiasRegime
  lrtConstrainedRegime :
    BiasRegime
  stationaryProxyRegime :
    BiasRegime
  lrtAndStationaryProxyRegime :
    BiasRegime

canonicalBiasRegimes :
  List BiasRegime
canonicalBiasRegimes =
  unconstrainedRegime
  ∷ lrtConstrainedRegime
  ∷ stationaryProxyRegime
  ∷ lrtAndStationaryProxyRegime
  ∷ []

biasRegimeCount : Nat
biasRegimeCount =
  listLength canonicalBiasRegimes

biasRegimeCountIs4 :
  biasRegimeCount ≡ 4
biasRegimeCountIs4 =
  refl

data BiasSign : Set where
  positiveBias :
    BiasSign
  negativeBias :
    BiasSign

data BiasMagnitudeReceipt : BiasRegime → BiasSign → Set where
  unconstrainedBiasPositiveRecorded :
    BiasMagnitudeReceipt unconstrainedRegime positiveBias
  lrtConstrainedBiasPositiveRecorded :
    BiasMagnitudeReceipt lrtConstrainedRegime positiveBias
  stationaryProxyBiasNegativeRecorded :
    BiasMagnitudeReceipt stationaryProxyRegime negativeBias
  lrtAndStationaryProxyBiasNegativeRecorded :
    BiasMagnitudeReceipt lrtAndStationaryProxyRegime negativeBias

maxBiasUnconstrainedReceipt : String
maxBiasUnconstrainedReceipt =
  "0.2407495053615816"

maxBiasLRTConstrainedReceipt : String
maxBiasLRTConstrainedReceipt =
  "0.2407495053615816"

maxBiasStationaryProxyReceipt : String
maxBiasStationaryProxyReceipt =
  "-0.03522081297975654"

maxBiasLRTAndStationaryProxyReceipt : String
maxBiasLRTAndStationaryProxyReceipt =
  "-0.025449723525345455"

baselineAllMeanBiasReceipt : String
baselineAllMeanBiasReceipt =
  "-0.000609557330890978"

unconstrainedCoverageScoreReceipt : String
unconstrainedCoverageScoreReceipt =
  "0.9983093682268799"

lrtProxyCoverageScoreReceipt : String
lrtProxyCoverageScoreReceipt =
  "0.9983093682268799"

stationaryProxyCoverageScoreReceipt : String
stationaryProxyCoverageScoreReceipt =
  "0.9982957847916428"

lrtAndStationaryProxyCoverageScoreReceipt : String
lrtAndStationaryProxyCoverageScoreReceipt =
  "0.9983920879692378"

data ActiveConstraint : Set where
  sampledGreatCircleHittingProxy :
    ActiveConstraint
  greedyHighBiasCoverageReplacement :
    ActiveConstraint
  oneStepTrueLerayDirectionTransportProxy :
    ActiveConstraint
  resampledInteractingMode :
    ActiveConstraint

lrtOnlyActiveConstraints :
  List ActiveConstraint
lrtOnlyActiveConstraints =
  sampledGreatCircleHittingProxy
  ∷ greedyHighBiasCoverageReplacement
  ∷ []

stationaryOnlyActiveConstraints :
  List ActiveConstraint
stationaryOnlyActiveConstraints =
  oneStepTrueLerayDirectionTransportProxy
  ∷ resampledInteractingMode
  ∷ []

lrtAndStationaryActiveConstraints :
  List ActiveConstraint
lrtAndStationaryActiveConstraints =
  sampledGreatCircleHittingProxy
  ∷ greedyHighBiasCoverageReplacement
  ∷ oneStepTrueLerayDirectionTransportProxy
  ∷ resampledInteractingMode
  ∷ []

lrtOnlyActiveConstraintCount : Nat
lrtOnlyActiveConstraintCount =
  listLength lrtOnlyActiveConstraints

stationaryOnlyActiveConstraintCount : Nat
stationaryOnlyActiveConstraintCount =
  listLength stationaryOnlyActiveConstraints

lrtAndStationaryActiveConstraintCount : Nat
lrtAndStationaryActiveConstraintCount =
  listLength lrtAndStationaryActiveConstraints

lrtOnlyActiveConstraintCountIs2 :
  lrtOnlyActiveConstraintCount ≡ 2
lrtOnlyActiveConstraintCountIs2 =
  refl

stationaryOnlyActiveConstraintCountIs2 :
  stationaryOnlyActiveConstraintCount ≡ 2
stationaryOnlyActiveConstraintCountIs2 =
  refl

lrtAndStationaryActiveConstraintCountIs4 :
  lrtAndStationaryActiveConstraintCount ≡ 4
lrtAndStationaryActiveConstraintCountIs4 =
  refl

------------------------------------------------------------------------
-- Interpretation clauses.

data HarnessFinding : Set where
  unconstrainedTopTailCanSelectPositiveBias :
    HarnessFinding
  lrtGreatCircleProxyDoesNotKillPositiveBiasAlone :
    HarnessFinding
  stationarityProxySelectsNegativeBias :
    HarnessFinding
  lrtPlusStationarityProxySelectsNegativeBias :
    HarnessFinding
  stationarityIsDecisiveFiniteConstraintInThisRun :
    HarnessFinding
  lrtRoleIsAngularCollapseGuardNotBiasKiller :
    HarnessFinding

canonicalHarnessFindings :
  List HarnessFinding
canonicalHarnessFindings =
  unconstrainedTopTailCanSelectPositiveBias
  ∷ lrtGreatCircleProxyDoesNotKillPositiveBiasAlone
  ∷ stationarityProxySelectsNegativeBias
  ∷ lrtPlusStationarityProxySelectsNegativeBias
  ∷ stationarityIsDecisiveFiniteConstraintInThisRun
  ∷ lrtRoleIsAngularCollapseGuardNotBiasKiller
  ∷ []

harnessFindingCount : Nat
harnessFindingCount =
  listLength canonicalHarnessFindings

harnessFindingCountIs6 :
  harnessFindingCount ≡ 6
harnessFindingCountIs6 =
  refl

data EvidenceTarget : Set where
  evidenceForNSTypeIBlowupKappaBiasBound :
    EvidenceTarget
  evidenceForApproximateStationarityAsPDEGate :
    EvidenceTarget
  evidenceAgainstLRTAaloneAsBiasSuppression :
    EvidenceTarget

canonicalEvidenceTargets :
  List EvidenceTarget
canonicalEvidenceTargets =
  evidenceForNSTypeIBlowupKappaBiasBound
  ∷ evidenceForApproximateStationarityAsPDEGate
  ∷ evidenceAgainstLRTAaloneAsBiasSuppression
  ∷ []

evidenceTargetCount : Nat
evidenceTargetCount =
  listLength canonicalEvidenceTargets

evidenceTargetCountIs3 :
  evidenceTargetCount ≡ 3
evidenceTargetCountIs3 =
  refl

------------------------------------------------------------------------
-- Fail-closed blockers and promotion guards.

data MissingProofObligation : Set where
  missingAbelTriadicDefectMeasureConstruction :
    MissingProofObligation
  missingTypeISelfSimilarPDEStationarityTransfer :
    MissingProofObligation
  missingGaussianDriftViscosityKappaBiasIdentity :
    MissingProofObligation
  missingNSTypeIBlowupKappaBiasBoundProof :
    MissingProofObligation
  missingTriadicCompensatedLeakageIdentity :
    MissingProofObligation
  missingCriticalResidualNonPositive :
    MissingProofObligation
  missingCKNBKMClosure :
    MissingProofObligation

canonicalMissingProofObligations :
  List MissingProofObligation
canonicalMissingProofObligations =
  missingAbelTriadicDefectMeasureConstruction
  ∷ missingTypeISelfSimilarPDEStationarityTransfer
  ∷ missingGaussianDriftViscosityKappaBiasIdentity
  ∷ missingNSTypeIBlowupKappaBiasBoundProof
  ∷ missingTriadicCompensatedLeakageIdentity
  ∷ missingCriticalResidualNonPositive
  ∷ missingCKNBKMClosure
  ∷ []

missingProofObligationCount : Nat
missingProofObligationCount =
  listLength canonicalMissingProofObligations

missingProofObligationCountIs7 :
  missingProofObligationCount ≡ 7
missingProofObligationCountIs7 =
  refl

data NSKappaBiasVariationalPromotion : Set where

nsKappaBiasVariationalPromotionImpossibleHere :
  NSKappaBiasVariationalPromotion →
  ⊥
nsKappaBiasVariationalPromotionImpossibleHere ()

finiteProxyOnly : Bool
finiteProxyOnly =
  true

stationarityDecisiveInHarness : Bool
stationarityDecisiveInHarness =
  true

lrtAloneDecisiveInHarness : Bool
lrtAloneDecisiveInHarness =
  false

pdeGateClosed : Bool
pdeGateClosed =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSKappaBiasVariationalHarnessResultStatus : Set where
  finiteProxyEvidenceRecorded_stationarityNegative_noPDEProof_noPromotion :
    NSKappaBiasVariationalHarnessResultStatus

nsKappaBiasVariationalHarnessResultSummary : String
nsKappaBiasVariationalHarnessResultSummary =
  "Finite S2 kappa-bias variational proxy: unconstrained and LRT-only regimes keep positive bias 0.2407495053615816, while stationary proxy is -0.03522081297975654 and LRT+stationary proxy is -0.025449723525345455.  Stationarity is the decisive numerical constraint; this is evidence only for NSTypeIBlowupKappaBiasBound and proves no PDE or Clay theorem."

record NSKappaBiasVariationalHarnessResult : Set where
  field
    status :
      NSKappaBiasVariationalHarnessResultStatus
    statusIsCanonical :
      status ≡
        finiteProxyEvidenceRecorded_stationarityNegative_noPDEProof_noPromotion
    sourceJson :
      String
    sourceJsonIsCanonical :
      sourceJson ≡ sourceJsonPath
    harnessScript :
      String
    harnessScriptIsCanonical :
      harnessScript ≡ harnessScriptPath
    biasRegimes :
      List BiasRegime
    biasRegimesAreCanonical :
      biasRegimes ≡ canonicalBiasRegimes
    biasRegimeCountIsFour :
      biasRegimeCount ≡ 4
    unconstrainedBiasPositive :
      BiasMagnitudeReceipt unconstrainedRegime positiveBias
    lrtConstrainedBiasPositive :
      BiasMagnitudeReceipt lrtConstrainedRegime positiveBias
    stationaryProxyBiasNegative :
      BiasMagnitudeReceipt stationaryProxyRegime negativeBias
    lrtAndStationaryProxyBiasNegative :
      BiasMagnitudeReceipt lrtAndStationaryProxyRegime negativeBias
    findings :
      List HarnessFinding
    findingsAreCanonical :
      findings ≡ canonicalHarnessFindings
    findingCountIsSix :
      harnessFindingCount ≡ 6
    evidenceTargets :
      List EvidenceTarget
    evidenceTargetsAreCanonical :
      evidenceTargets ≡ canonicalEvidenceTargets
    evidenceTargetCountIsThree :
      evidenceTargetCount ≡ 3
    missingProofObligations :
      List MissingProofObligation
    missingProofObligationsAreCanonical :
      missingProofObligations ≡ canonicalMissingProofObligations
    missingProofObligationCountIsSeven :
      missingProofObligationCount ≡ 7
    finiteProxyOnlyIsTrue :
      finiteProxyOnly ≡ true
    stationarityDecisiveInHarnessIsTrue :
      stationarityDecisiveInHarness ≡ true
    lrtAloneDecisiveInHarnessIsFalse :
      lrtAloneDecisiveInHarness ≡ false
    pdeGateClosedIsFalse :
      pdeGateClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsKappaBiasVariationalHarnessResultSummary

canonicalNSKappaBiasVariationalHarnessResult :
  NSKappaBiasVariationalHarnessResult
canonicalNSKappaBiasVariationalHarnessResult =
  record
    { status =
        finiteProxyEvidenceRecorded_stationarityNegative_noPDEProof_noPromotion
    ; statusIsCanonical =
        refl
    ; sourceJson =
        sourceJsonPath
    ; sourceJsonIsCanonical =
        refl
    ; harnessScript =
        harnessScriptPath
    ; harnessScriptIsCanonical =
        refl
    ; biasRegimes =
        canonicalBiasRegimes
    ; biasRegimesAreCanonical =
        refl
    ; biasRegimeCountIsFour =
        refl
    ; unconstrainedBiasPositive =
        unconstrainedBiasPositiveRecorded
    ; lrtConstrainedBiasPositive =
        lrtConstrainedBiasPositiveRecorded
    ; stationaryProxyBiasNegative =
        stationaryProxyBiasNegativeRecorded
    ; lrtAndStationaryProxyBiasNegative =
        lrtAndStationaryProxyBiasNegativeRecorded
    ; findings =
        canonicalHarnessFindings
    ; findingsAreCanonical =
        refl
    ; findingCountIsSix =
        refl
    ; evidenceTargets =
        canonicalEvidenceTargets
    ; evidenceTargetsAreCanonical =
        refl
    ; evidenceTargetCountIsThree =
        refl
    ; missingProofObligations =
        canonicalMissingProofObligations
    ; missingProofObligationsAreCanonical =
        refl
    ; missingProofObligationCountIsSeven =
        refl
    ; finiteProxyOnlyIsTrue =
        refl
    ; stationarityDecisiveInHarnessIsTrue =
        refl
    ; lrtAloneDecisiveInHarnessIsFalse =
        refl
    ; pdeGateClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsKappaBiasVariationalHarnessResultSummary
    ; summaryIsCanonical =
        refl
    }

nsKappaBiasVariationalHarnessResultKeepsPDEGateOpen :
  pdeGateClosed ≡ false
nsKappaBiasVariationalHarnessResultKeepsPDEGateOpen =
  refl

nsKappaBiasVariationalHarnessResultKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsKappaBiasVariationalHarnessResultKeepsClayFalse =
  refl

nsKappaBiasVariationalHarnessResultKeepsTerminalFalse :
  terminalPromotion ≡ false
nsKappaBiasVariationalHarnessResultKeepsTerminalFalse =
  refl
