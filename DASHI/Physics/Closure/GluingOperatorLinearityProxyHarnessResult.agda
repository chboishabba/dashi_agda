module DASHI.Physics.Closure.GluingOperatorLinearityProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/gluing_operator_linearity_proxy_harness.py
--
-- The harness is a finite diagnostic for the U-1a unification blocker:
--
--   GluingOperatorLinearityOnDefectQuotient
--
-- It checks that a quotient-linear finite proxy passes additivity, scalar
-- compatibility, representative compatibility, and the induced quadratic
-- four-point output identity, while a nonlinear representative-dependent
-- counterexample fails those checks visibly.
--
-- This module records that diagnostic result only.  It does not define the
-- real admissible defect quotient V, prove that the true gluing operator is
-- linear on V, prove four-point cancellation, prove the parallelogram law,
-- derive a quadratic form, or promote terminal unification.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary
  as U1a

------------------------------------------------------------------------
-- Local list and counting utilities.

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

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/gluing_operator_linearity_proxy_harness.py"

jsonSmokeReceiptPath : String
jsonSmokeReceiptPath =
  "outputs/gluing_operator_linearity_proxy_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/gluing_operator_linearity_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_quotient_linearity_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/gluing_operator_linearity_proxy_harness.py --json-output outputs/gluing_operator_linearity_proxy_smoke.json --json"

manifestEntryText : String
manifestEntryText =
  "local_clay_harness_manifest entry: gluing_operator_linearity_proxy"

defaultParameterText : String
defaultParameterText =
  "ambient_dim=6, quotient_dim=4, samples=512, seed=20260608, tolerance=1e-10"

counterexampleVisibilityText : String
counterexampleVisibilityText =
  "nonlinear counterexample combined error exceeds counterexample_min_error=1e-3"

------------------------------------------------------------------------
-- Imported U-1a support.

u1aBoundaryReference : String
u1aBoundaryReference =
  "DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary"

u1aBoundaryImported : Bool
u1aBoundaryImported =
  true

record ImportedGluingProxySupport : Setω where
  field
    gluingOperatorLinearityBoundary :
      U1a.GluingOperatorLinearityOnDefectQuotientBoundary
    u1aBoundaryImportedIsTrue :
      u1aBoundaryImported ≡ true
    importedBoundaryKeepsLinearityOpen :
      U1a.gluingLinearityProvedField
        gluingOperatorLinearityBoundary
      ≡ false
    importedBoundaryKeepsFourPointBlocked :
      U1a.fourPointCancellationProvedField
        gluingOperatorLinearityBoundary
      ≡ false
    importedBoundaryKeepsTerminalFalse :
      U1a.terminalPromotionField
        gluingOperatorLinearityBoundary
      ≡ false

canonicalImportedGluingProxySupport : ImportedGluingProxySupport
canonicalImportedGluingProxySupport =
  record
    { gluingOperatorLinearityBoundary =
        U1a.canonicalGluingOperatorLinearityOnDefectQuotientBoundary
    ; u1aBoundaryImportedIsTrue =
        refl
    ; importedBoundaryKeepsLinearityOpen =
        U1a.canonicalU1aGluingLinearityStillOpen
    ; importedBoundaryKeepsFourPointBlocked =
        U1a.canonicalU1aFourPointCancellationBlocked
    ; importedBoundaryKeepsTerminalFalse =
        U1a.canonicalU1aTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Top-level harness fields.

data GluingHarnessField : Set where
  controlCardField :
    GluingHarnessField
  promotionField :
    GluingHarnessField
  clayPromotionField :
    GluingHarnessField
  unificationPromotionField :
    GluingHarnessField
  okField :
    GluingHarnessField
  parametersField :
    GluingHarnessField
  summaryField :
    GluingHarnessField
  casesField :
    GluingHarnessField
  interpretationField :
    GluingHarnessField

canonicalGluingHarnessFields : List GluingHarnessField
canonicalGluingHarnessFields =
  controlCardField
  ∷ promotionField
  ∷ clayPromotionField
  ∷ unificationPromotionField
  ∷ okField
  ∷ parametersField
  ∷ summaryField
  ∷ casesField
  ∷ interpretationField
  ∷ []

gluingHarnessFieldCount : Nat
gluingHarnessFieldCount =
  listLength canonicalGluingHarnessFields

gluingHarnessFieldCountIs9 :
  gluingHarnessFieldCount ≡ 9
gluingHarnessFieldCountIs9 =
  refl

ok_observed : Bool
ok_observed =
  true

promotion : Bool
promotion =
  false

clay_promotion : Bool
clay_promotion =
  false

unification_promotion : Bool
unification_promotion =
  false

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

clay_promotion_is_false :
  clay_promotion ≡ false
clay_promotion_is_false =
  refl

unification_promotion_is_false :
  unification_promotion ≡ false
unification_promotion_is_false =
  refl

------------------------------------------------------------------------
-- Proxy cases and expected check outcomes.

data GluingProxyCase : Set where
  quotientLinearCase :
    GluingProxyCase
  nonlinearRepresentativeDependentCounterexample :
    GluingProxyCase

caseName : GluingProxyCase → String
caseName quotientLinearCase =
  "quotient_linear"
caseName nonlinearRepresentativeDependentCounterexample =
  "nonlinear_representative_dependent"

caseDescription : GluingProxyCase → String
caseDescription quotientLinearCase =
  "Applies a fixed matrix to observable quotient coordinates and ignores null representatives."
caseDescription nonlinearRepresentativeDependentCounterexample =
  "Adds coordinate squares and null-energy dependence; expected to fail quotient-linearity."

data GluingProxyCheck : Set where
  additivityCheck :
    GluingProxyCheck
  scalarCompatibilityCheck :
    GluingProxyCheck
  representativeCompatibilityCheck :
    GluingProxyCheck
  quadraticFourPointOutputCheck :
    GluingProxyCheck

checkName : GluingProxyCheck → String
checkName additivityCheck =
  "additivity"
checkName scalarCompatibilityCheck =
  "scalar_compatibility"
checkName representativeCompatibilityCheck =
  "representative_compatibility"
checkName quadraticFourPointOutputCheck =
  "quadratic_four_point_output"

canonicalGluingProxyChecks : List GluingProxyCheck
canonicalGluingProxyChecks =
  additivityCheck
  ∷ scalarCompatibilityCheck
  ∷ representativeCompatibilityCheck
  ∷ quadraticFourPointOutputCheck
  ∷ []

gluingProxyCheckCount : Nat
gluingProxyCheckCount =
  listLength canonicalGluingProxyChecks

gluingProxyCheckCountIs4 :
  gluingProxyCheckCount ≡ 4
gluingProxyCheckCountIs4 =
  refl

expectedCheckOutcome : GluingProxyCase → GluingProxyCheck → Bool
expectedCheckOutcome quotientLinearCase additivityCheck =
  true
expectedCheckOutcome quotientLinearCase scalarCompatibilityCheck =
  true
expectedCheckOutcome quotientLinearCase representativeCompatibilityCheck =
  true
expectedCheckOutcome quotientLinearCase quadraticFourPointOutputCheck =
  true
expectedCheckOutcome nonlinearRepresentativeDependentCounterexample additivityCheck =
  false
expectedCheckOutcome nonlinearRepresentativeDependentCounterexample scalarCompatibilityCheck =
  false
expectedCheckOutcome nonlinearRepresentativeDependentCounterexample representativeCompatibilityCheck =
  false
expectedCheckOutcome nonlinearRepresentativeDependentCounterexample quadraticFourPointOutputCheck =
  false

record GluingProxyCheckReceipt : Set where
  field
    case :
      GluingProxyCase
    check :
      GluingProxyCheck
    observedOutcome :
      Bool
    observedOutcomeIsExpected :
      observedOutcome ≡ expectedCheckOutcome case check
    checkLabel :
      String

open GluingProxyCheckReceipt public

mkGluingProxyCheckReceipt :
  (case : GluingProxyCase) →
  (check : GluingProxyCheck) →
  GluingProxyCheckReceipt
mkGluingProxyCheckReceipt case check =
  record
    { case =
        case
    ; check =
        check
    ; observedOutcome =
        expectedCheckOutcome case check
    ; observedOutcomeIsExpected =
        refl
    ; checkLabel =
        checkName check
    }

quotientLinearCheckReceipts : List GluingProxyCheckReceipt
quotientLinearCheckReceipts =
  mkGluingProxyCheckReceipt quotientLinearCase additivityCheck
  ∷ mkGluingProxyCheckReceipt quotientLinearCase scalarCompatibilityCheck
  ∷ mkGluingProxyCheckReceipt quotientLinearCase representativeCompatibilityCheck
  ∷ mkGluingProxyCheckReceipt quotientLinearCase quadraticFourPointOutputCheck
  ∷ []

nonlinearCounterexampleCheckReceipts : List GluingProxyCheckReceipt
nonlinearCounterexampleCheckReceipts =
  mkGluingProxyCheckReceipt nonlinearRepresentativeDependentCounterexample additivityCheck
  ∷ mkGluingProxyCheckReceipt nonlinearRepresentativeDependentCounterexample scalarCompatibilityCheck
  ∷ mkGluingProxyCheckReceipt nonlinearRepresentativeDependentCounterexample representativeCompatibilityCheck
  ∷ mkGluingProxyCheckReceipt nonlinearRepresentativeDependentCounterexample quadraticFourPointOutputCheck
  ∷ []

quotientLinearCheckReceiptCountIs4 :
  listLength quotientLinearCheckReceipts ≡ 4
quotientLinearCheckReceiptCountIs4 =
  refl

nonlinearCounterexampleCheckReceiptCountIs4 :
  listLength nonlinearCounterexampleCheckReceipts ≡ 4
nonlinearCounterexampleCheckReceiptCountIs4 =
  refl

------------------------------------------------------------------------
-- Case-level receipts.

record GluingProxyCaseReceipt : Set where
  field
    case :
      GluingProxyCase
    name :
      String
    description :
      String
    passedAllProxyChecks :
      Bool
    expectedPassedAllProxyChecks :
      Bool
    passedAllProxyChecksIsExpected :
      passedAllProxyChecks ≡ expectedPassedAllProxyChecks
    checkReceipts :
      List GluingProxyCheckReceipt
    checkReceiptCountIs4 :
      listLength checkReceipts ≡ 4
    promotionForCase :
      Bool
    promotionForCaseIsFalse :
      promotionForCase ≡ false
    maxErrorSummary :
      String
    interpretation :
      String

open GluingProxyCaseReceipt public

quotientLinearCaseReceipt : GluingProxyCaseReceipt
quotientLinearCaseReceipt =
  record
    { case =
        quotientLinearCase
    ; name =
        caseName quotientLinearCase
    ; description =
        caseDescription quotientLinearCase
    ; passedAllProxyChecks =
        true
    ; expectedPassedAllProxyChecks =
        true
    ; passedAllProxyChecksIsExpected =
        refl
    ; checkReceipts =
        quotientLinearCheckReceipts
    ; checkReceiptCountIs4 =
        quotientLinearCheckReceiptCountIs4
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; maxErrorSummary =
        "linear proxy max combined error ~= 1.42e-14, within floating tolerance"
    ; interpretation =
        "finite quotient-linear proxy preserves additivity, scalar compatibility, representative independence, and the output four-point identity"
    }

nonlinearRepresentativeDependentCounterexampleReceipt :
  GluingProxyCaseReceipt
nonlinearRepresentativeDependentCounterexampleReceipt =
  record
    { case =
        nonlinearRepresentativeDependentCounterexample
    ; name =
        caseName nonlinearRepresentativeDependentCounterexample
    ; description =
        caseDescription nonlinearRepresentativeDependentCounterexample
    ; passedAllProxyChecks =
        false
    ; expectedPassedAllProxyChecks =
        false
    ; passedAllProxyChecksIsExpected =
        refl
    ; checkReceipts =
        nonlinearCounterexampleCheckReceipts
    ; checkReceiptCountIs4 =
        nonlinearCounterexampleCheckReceiptCountIs4
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; maxErrorSummary =
        "nonlinear counterexample max combined error ~= 13.57, visibly above threshold"
    ; interpretation =
        "nonlinear representative-dependent proxy fails additivity, scalar compatibility, representative compatibility, and four-point output checks"
    }

canonicalGluingProxyCaseReceipts : List GluingProxyCaseReceipt
canonicalGluingProxyCaseReceipts =
  quotientLinearCaseReceipt
  ∷ nonlinearRepresentativeDependentCounterexampleReceipt
  ∷ []

gluingProxyCaseReceiptCount : Nat
gluingProxyCaseReceiptCount =
  listLength canonicalGluingProxyCaseReceipts

gluingProxyCaseReceiptCountIs2 :
  gluingProxyCaseReceiptCount ≡ 2
gluingProxyCaseReceiptCountIs2 =
  refl

quotientLinearCasePassed :
  passedAllProxyChecks quotientLinearCaseReceipt ≡ true
quotientLinearCasePassed =
  refl

nonlinearCounterexampleFailed :
  passedAllProxyChecks
    nonlinearRepresentativeDependentCounterexampleReceipt
  ≡ false
nonlinearCounterexampleFailed =
  refl

------------------------------------------------------------------------
-- Summary and non-claim boundaries.

data GluingHarnessSummaryObservation : Set where
  linearCasePassedObserved :
    GluingHarnessSummaryObservation
  nonlinearCounterexampleFailedObserved :
    GluingHarnessSummaryObservation
  nonlinearCounterexampleVisibleObserved :
    GluingHarnessSummaryObservation
  allExpectedOutcomesObserved :
    GluingHarnessSummaryObservation
  promotionFalseObserved :
    GluingHarnessSummaryObservation

canonicalGluingHarnessSummaryObservations :
  List GluingHarnessSummaryObservation
canonicalGluingHarnessSummaryObservations =
  linearCasePassedObserved
  ∷ nonlinearCounterexampleFailedObserved
  ∷ nonlinearCounterexampleVisibleObserved
  ∷ allExpectedOutcomesObserved
  ∷ promotionFalseObserved
  ∷ []

gluingHarnessSummaryObservationCount : Nat
gluingHarnessSummaryObservationCount =
  listLength canonicalGluingHarnessSummaryObservations

gluingHarnessSummaryObservationCountIs5 :
  gluingHarnessSummaryObservationCount ≡ 5
gluingHarnessSummaryObservationCountIs5 =
  refl

data GluingHarnessNonClaimBoundary : Set where
  diagnosticOnlyNotAdmissibleQuotientDefinition :
    GluingHarnessNonClaimBoundary
  noTrueGluingOperatorLinearityProof :
    GluingHarnessNonClaimBoundary
  noGluingResidualForcesFourPointCancellationProof :
    GluingHarnessNonClaimBoundary
  noParallelogramOrQuadraticEmergenceProof :
    GluingHarnessNonClaimBoundary
  noClayOrTerminalPromotion :
    GluingHarnessNonClaimBoundary

canonicalGluingHarnessNonClaimBoundaries :
  List GluingHarnessNonClaimBoundary
canonicalGluingHarnessNonClaimBoundaries =
  diagnosticOnlyNotAdmissibleQuotientDefinition
  ∷ noTrueGluingOperatorLinearityProof
  ∷ noGluingResidualForcesFourPointCancellationProof
  ∷ noParallelogramOrQuadraticEmergenceProof
  ∷ noClayOrTerminalPromotion
  ∷ []

gluingHarnessNonClaimBoundaryCount : Nat
gluingHarnessNonClaimBoundaryCount =
  listLength canonicalGluingHarnessNonClaimBoundaries

gluingHarnessNonClaimBoundaryCountIs5 :
  gluingHarnessNonClaimBoundaryCount ≡ 5
gluingHarnessNonClaimBoundaryCountIs5 =
  refl

realAdmissibleDefectQuotientDefinedHere : Bool
realAdmissibleDefectQuotientDefinedHere =
  false

trueGluingLinearityProvedHere : Bool
trueGluingLinearityProvedHere =
  false

fourPointCancellationProvedHere : Bool
fourPointCancellationProvedHere =
  false

parallelogramLawProvedHere : Bool
parallelogramLawProvedHere =
  false

quadraticEmergenceProvedHere : Bool
quadraticEmergenceProvedHere =
  false

terminalPromotion : Bool
terminalPromotion =
  false

realAdmissibleDefectQuotientDefinedHereIsFalse :
  realAdmissibleDefectQuotientDefinedHere ≡ false
realAdmissibleDefectQuotientDefinedHereIsFalse =
  refl

trueGluingLinearityProvedHereIsFalse :
  trueGluingLinearityProvedHere ≡ false
trueGluingLinearityProvedHereIsFalse =
  refl

fourPointCancellationProvedHereIsFalse :
  fourPointCancellationProvedHere ≡ false
fourPointCancellationProvedHereIsFalse =
  refl

parallelogramLawProvedHereIsFalse :
  parallelogramLawProvedHere ≡ false
parallelogramLawProvedHereIsFalse =
  refl

quadraticEmergenceProvedHereIsFalse :
  quadraticEmergenceProvedHere ≡ false
quadraticEmergenceProvedHereIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Closed harness receipt.

gluingHarnessControlCardText : String
gluingHarnessControlCardText =
  "O Lane 6 diagnostic; R test quotient-linearity proxies; C scripts/gluing_operator_linearity_proxy_harness.py; G promotion=false"

gluingHarnessSupportsText : String
gluingHarnessSupportsText =
  "Linearity plus representative independence is checkable on finite quotient proxies."

gluingHarnessRejectsText : String
gluingHarnessRejectsText =
  "Nonlinear or representative-dependent gluing operators fail quotient compatibility and four-point cancellation in this proxy."

gluingHarnessResidualGapText : String
gluingHarnessResidualGapText =
  "The actual admissible defect quotient V and true gluing-linearity theorem remain open."

record GluingOperatorLinearityProxyHarnessResult : Setω where
  field
    sourceHarness :
      String
    jsonReceipt :
      String
    manifestChildReceipt :
      String
    scope :
      String
    runCommand :
      String
    manifestEntry :
      String
    defaultParameters :
      String
    importedSupport :
      ImportedGluingProxySupport
    harnessFields :
      List GluingHarnessField
    harnessFieldCountIs9 :
      listLength harnessFields ≡ 9
    caseReceipts :
      List GluingProxyCaseReceipt
    caseReceiptCountIs2 :
      listLength caseReceipts ≡ 2
    summaryObservations :
      List GluingHarnessSummaryObservation
    summaryObservationCountIs5 :
      listLength summaryObservations ≡ 5
    nonClaimBoundaries :
      List GluingHarnessNonClaimBoundary
    nonClaimBoundaryCountIs5 :
      listLength nonClaimBoundaries ≡ 5
    okObserved :
      ok_observed ≡ true
    promotionFalse :
      promotion ≡ false
    clayPromotionFalse :
      clay_promotion ≡ false
    unificationPromotionFalse :
      unification_promotion ≡ false
    quotientLinearCasePassedProof :
      passedAllProxyChecks quotientLinearCaseReceipt ≡ true
    nonlinearCounterexampleFailedProof :
      passedAllProxyChecks
        nonlinearRepresentativeDependentCounterexampleReceipt
      ≡ false
    realAdmissibleDefectQuotientDefinedHereFalse :
      realAdmissibleDefectQuotientDefinedHere ≡ false
    trueGluingLinearityProvedHereFalse :
      trueGluingLinearityProvedHere ≡ false
    fourPointCancellationProvedHereFalse :
      fourPointCancellationProvedHere ≡ false
    parallelogramLawProvedHereFalse :
      parallelogramLawProvedHere ≡ false
    quadraticEmergenceProvedHereFalse :
      quadraticEmergenceProvedHere ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    controlCard :
      String
    supports :
      String
    rejects :
      String
    residualGap :
      String

open GluingOperatorLinearityProxyHarnessResult public

canonicalGluingOperatorLinearityProxyHarnessResult :
  GluingOperatorLinearityProxyHarnessResult
canonicalGluingOperatorLinearityProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonSmokeReceiptPath
    ; manifestChildReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; runCommand =
        runCommandText
    ; manifestEntry =
        manifestEntryText
    ; defaultParameters =
        defaultParameterText
    ; importedSupport =
        canonicalImportedGluingProxySupport
    ; harnessFields =
        canonicalGluingHarnessFields
    ; harnessFieldCountIs9 =
        gluingHarnessFieldCountIs9
    ; caseReceipts =
        canonicalGluingProxyCaseReceipts
    ; caseReceiptCountIs2 =
        gluingProxyCaseReceiptCountIs2
    ; summaryObservations =
        canonicalGluingHarnessSummaryObservations
    ; summaryObservationCountIs5 =
        gluingHarnessSummaryObservationCountIs5
    ; nonClaimBoundaries =
        canonicalGluingHarnessNonClaimBoundaries
    ; nonClaimBoundaryCountIs5 =
        gluingHarnessNonClaimBoundaryCountIs5
    ; okObserved =
        ok_observed_is_true
    ; promotionFalse =
        promotion_is_false
    ; clayPromotionFalse =
        clay_promotion_is_false
    ; unificationPromotionFalse =
        unification_promotion_is_false
    ; quotientLinearCasePassedProof =
        quotientLinearCasePassed
    ; nonlinearCounterexampleFailedProof =
        nonlinearCounterexampleFailed
    ; realAdmissibleDefectQuotientDefinedHereFalse =
        realAdmissibleDefectQuotientDefinedHereIsFalse
    ; trueGluingLinearityProvedHereFalse =
        trueGluingLinearityProvedHereIsFalse
    ; fourPointCancellationProvedHereFalse =
        fourPointCancellationProvedHereIsFalse
    ; parallelogramLawProvedHereFalse =
        parallelogramLawProvedHereIsFalse
    ; quadraticEmergenceProvedHereFalse =
        quadraticEmergenceProvedHereIsFalse
    ; terminalPromotionFalse =
        terminalPromotionIsFalse
    ; controlCard =
        gluingHarnessControlCardText
    ; supports =
        gluingHarnessSupportsText
    ; rejects =
        gluingHarnessRejectsText
    ; residualGap =
        gluingHarnessResidualGapText
    }

------------------------------------------------------------------------
-- Convenience projections and guard lemmas.

canonicalGluingHarnessFieldCountIs9 :
  listLength
    (harnessFields canonicalGluingOperatorLinearityProxyHarnessResult)
  ≡ 9
canonicalGluingHarnessFieldCountIs9 =
  refl

canonicalGluingHarnessCaseCountIs2 :
  listLength
    (caseReceipts canonicalGluingOperatorLinearityProxyHarnessResult)
  ≡ 2
canonicalGluingHarnessCaseCountIs2 =
  refl

canonicalGluingHarnessSummaryCountIs5 :
  listLength
    (summaryObservations canonicalGluingOperatorLinearityProxyHarnessResult)
  ≡ 5
canonicalGluingHarnessSummaryCountIs5 =
  refl

canonicalGluingHarnessNonClaimCountIs5 :
  listLength
    (nonClaimBoundaries canonicalGluingOperatorLinearityProxyHarnessResult)
  ≡ 5
canonicalGluingHarnessNonClaimCountIs5 =
  refl

canonicalGluingHarnessOkObserved :
  ok_observed ≡ true
canonicalGluingHarnessOkObserved =
  refl

canonicalGluingHarnessPromotionFalse :
  promotion ≡ false
canonicalGluingHarnessPromotionFalse =
  refl

canonicalGluingHarnessClayPromotionFalse :
  clay_promotion ≡ false
canonicalGluingHarnessClayPromotionFalse =
  refl

canonicalGluingHarnessUnificationPromotionFalse :
  unification_promotion ≡ false
canonicalGluingHarnessUnificationPromotionFalse =
  refl

canonicalGluingHarnessDoesNotDefineRealQuotient :
  realAdmissibleDefectQuotientDefinedHere ≡ false
canonicalGluingHarnessDoesNotDefineRealQuotient =
  refl

canonicalGluingHarnessDoesNotProveTrueLinearity :
  trueGluingLinearityProvedHere ≡ false
canonicalGluingHarnessDoesNotProveTrueLinearity =
  refl

canonicalGluingHarnessDoesNotProveFourPointCancellation :
  fourPointCancellationProvedHere ≡ false
canonicalGluingHarnessDoesNotProveFourPointCancellation =
  refl

canonicalGluingHarnessDoesNotProveParallelogram :
  parallelogramLawProvedHere ≡ false
canonicalGluingHarnessDoesNotProveParallelogram =
  refl

canonicalGluingHarnessDoesNotProveQuadraticEmergence :
  quadraticEmergenceProvedHere ≡ false
canonicalGluingHarnessDoesNotProveQuadraticEmergence =
  refl

canonicalGluingHarnessTerminalPromotionFalse :
  terminalPromotion ≡ false
canonicalGluingHarnessTerminalPromotionFalse =
  refl

noTerminalPromotionFromGluingProxyHarnessAlone :
  terminalPromotion ≡ true →
  ⊥
noTerminalPromotionFromGluingProxyHarnessAlone ()
