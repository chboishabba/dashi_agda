module DASHI.Physics.Closure.UnificationGluingQuotientAdmissibilityProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/unification_gluing_quotient_admissibility_proxy_harness.py
--
-- The harness is a finite diagnostic for quotient admissibility in the
-- unification gluing line.  It checks one representative-invariant linear
-- quotient proxy and three visible obstruction cases.  This module records
-- that diagnostic result only.  It does not construct the true admissible
-- defect quotient, prove gluing linearity, prove four-point cancellation,
-- prove the parallelogram law, derive quadratic emergence, or promote
-- terminal unification.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary
  as U1a
import DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary
  as Composite

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/unification_gluing_quotient_admissibility_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/unification_gluing_quotient_admissibility_proxy_harness.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/unification_gluing_quotient_admissibility_proxy_harness.json"

receiptScope : String
receiptScope =
  "finite_unification_gluing_quotient_admissibility_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/unification_gluing_quotient_admissibility_proxy_harness.py --json-output outputs/local_clay_harness_manifest_children/unification_gluing_quotient_admissibility_proxy_harness.json --json"

defaultParameterText : String
defaultParameterText =
  "ambient_dim=7, quotient_dim=4, output_dim=4, radius=3, tolerance=1e-10, counterexample_min_error=1e-3"

------------------------------------------------------------------------
-- Imported support.

u1aBoundaryReference : String
u1aBoundaryReference =
  "DASHI.Physics.Closure.GluingOperatorLinearityOnDefectQuotientBoundary"

compositeBoundaryReference : String
compositeBoundaryReference =
  "DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary"

u1aBoundaryImported : Bool
u1aBoundaryImported =
  true

compositeBoundaryImported : Bool
compositeBoundaryImported =
  true

record ImportedUnificationGluingQuotientSupport : Setω where
  field
    gluingLinearityBoundary :
      U1a.GluingOperatorLinearityOnDefectQuotientBoundary
    compositeBoundary :
      Composite.UnificationGluingLinearityCompositeBoundary
    u1aBoundaryImportedIsTrue :
      u1aBoundaryImported ≡ true
    compositeBoundaryImportedIsTrue :
      compositeBoundaryImported ≡ true
    importedGluingLinearityStillOpen :
      U1a.gluingLinearityProvedField gluingLinearityBoundary ≡ false
    importedFourPointCancellationStillOpen :
      U1a.fourPointCancellationProvedField gluingLinearityBoundary ≡ false
    importedCompositeTheoremPromotionFlagsAllFalse :
      Composite.theoremPromotionFlagsAllFalse compositeBoundary ≡ true
    importedCompositeUnificationPromotionFalse :
      Composite.unificationPromoted compositeBoundary ≡ false
    importedU1aTerminalPromotionFalse :
      U1a.terminalPromotionField gluingLinearityBoundary ≡ false

canonicalImportedUnificationGluingQuotientSupport :
  ImportedUnificationGluingQuotientSupport
canonicalImportedUnificationGluingQuotientSupport =
  record
    { gluingLinearityBoundary =
        U1a.canonicalGluingOperatorLinearityOnDefectQuotientBoundary
    ; compositeBoundary =
        Composite.canonicalUnificationGluingLinearityCompositeBoundary
    ; u1aBoundaryImportedIsTrue =
        refl
    ; compositeBoundaryImportedIsTrue =
        refl
    ; importedGluingLinearityStillOpen =
        U1a.canonicalU1aGluingLinearityStillOpen
    ; importedFourPointCancellationStillOpen =
        U1a.canonicalU1aFourPointCancellationBlocked
    ; importedCompositeTheoremPromotionFlagsAllFalse =
        Composite.canonicalCompositeTheoremPromotionFlagsAllFalse
    ; importedCompositeUnificationPromotionFalse =
        Composite.canonicalCompositeUnificationPromotionFalse
    ; importedU1aTerminalPromotionFalse =
        U1a.canonicalU1aTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Observed harness flags.

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

quotientAdmissibilityProved : Bool
quotientAdmissibilityProved =
  false

gluingLinearityProved : Bool
gluingLinearityProved =
  false

fourPointCancellationProved : Bool
fourPointCancellationProved =
  false

parallelogramProved : Bool
parallelogramProved =
  false

quadraticEmergenceProved : Bool
quadraticEmergenceProved =
  false

terminalPromotion : Bool
terminalPromotion =
  false

ok_observed_is_true :
  ok_observed ≡ true
ok_observed_is_true =
  refl

diagnostic_only_is_true :
  diagnostic_only ≡ true
diagnostic_only_is_true =
  refl

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

quotientAdmissibilityProved_is_false :
  quotientAdmissibilityProved ≡ false
quotientAdmissibilityProved_is_false =
  refl

gluingLinearityProved_is_false :
  gluingLinearityProved ≡ false
gluingLinearityProved_is_false =
  refl

fourPointCancellationProved_is_false :
  fourPointCancellationProved ≡ false
fourPointCancellationProved_is_false =
  refl

parallelogramProved_is_false :
  parallelogramProved ≡ false
parallelogramProved_is_false =
  refl

quadraticEmergenceProved_is_false :
  quadraticEmergenceProved ≡ false
quadraticEmergenceProved_is_false =
  refl

terminalPromotion_is_false :
  terminalPromotion ≡ false
terminalPromotion_is_false =
  refl

------------------------------------------------------------------------
-- Proxy cases.

data ProxyCaseKind : Set where
  goodCase :
    ProxyCaseKind
  badCase :
    ProxyCaseKind

data UnificationGluingQuotientProxyCase : Set where
  linear_quotient_gluing :
    UnificationGluingQuotientProxyCase
  representative_dependent_leak :
    UnificationGluingQuotientProxyCase
  nonlinear_quotient_gluing :
    UnificationGluingQuotientProxyCase
  norm_like_near_miss :
    UnificationGluingQuotientProxyCase

caseName : UnificationGluingQuotientProxyCase → String
caseName linear_quotient_gluing =
  "linear_quotient_gluing"
caseName representative_dependent_leak =
  "representative_dependent_leak"
caseName nonlinear_quotient_gluing =
  "nonlinear_quotient_gluing"
caseName norm_like_near_miss =
  "norm_like_near_miss"

sourceHarnessCaseName : UnificationGluingQuotientProxyCase → String
sourceHarnessCaseName linear_quotient_gluing =
  "linear_quotient_gluing"
sourceHarnessCaseName representative_dependent_leak =
  "representative_dependent_leak"
sourceHarnessCaseName nonlinear_quotient_gluing =
  "nonlinear_quotient_gluing"
sourceHarnessCaseName norm_like_near_miss =
  "two_homogeneous_norm_like_near_miss"

record ProxyCaseReceipt : Set where
  field
    proxyCase :
      UnificationGluingQuotientProxyCase
    sourceName :
      String
    kind :
      ProxyCaseKind
    observedPass :
      Bool
    expectedOutcomeObserved :
      Bool
    representativeInvariant :
      Bool
    additive :
      Bool
    scalarCompatible :
      Bool
    twoHomogeneousEnergy :
      Bool
    fourPointResidualCancellation :
      Bool
    expectedOutcomeObservedIsTrue :
      expectedOutcomeObserved ≡ true

open ProxyCaseReceipt public

linearQuotientGluingReceipt : ProxyCaseReceipt
linearQuotientGluingReceipt =
  record
    { proxyCase =
        linear_quotient_gluing
    ; sourceName =
        sourceHarnessCaseName linear_quotient_gluing
    ; kind =
        goodCase
    ; observedPass =
        true
    ; expectedOutcomeObserved =
        true
    ; representativeInvariant =
        true
    ; additive =
        true
    ; scalarCompatible =
        true
    ; twoHomogeneousEnergy =
        true
    ; fourPointResidualCancellation =
        true
    ; expectedOutcomeObservedIsTrue =
        refl
    }

representativeDependentLeakReceipt : ProxyCaseReceipt
representativeDependentLeakReceipt =
  record
    { proxyCase =
        representative_dependent_leak
    ; sourceName =
        sourceHarnessCaseName representative_dependent_leak
    ; kind =
        badCase
    ; observedPass =
        false
    ; expectedOutcomeObserved =
        true
    ; representativeInvariant =
        false
    ; additive =
        false
    ; scalarCompatible =
        false
    ; twoHomogeneousEnergy =
        false
    ; fourPointResidualCancellation =
        false
    ; expectedOutcomeObservedIsTrue =
        refl
    }

nonlinearQuotientGluingReceipt : ProxyCaseReceipt
nonlinearQuotientGluingReceipt =
  record
    { proxyCase =
        nonlinear_quotient_gluing
    ; sourceName =
        sourceHarnessCaseName nonlinear_quotient_gluing
    ; kind =
        badCase
    ; observedPass =
        false
    ; expectedOutcomeObserved =
        true
    ; representativeInvariant =
        true
    ; additive =
        false
    ; scalarCompatible =
        false
    ; twoHomogeneousEnergy =
        false
    ; fourPointResidualCancellation =
        false
    ; expectedOutcomeObservedIsTrue =
        refl
    }

normLikeNearMissReceipt : ProxyCaseReceipt
normLikeNearMissReceipt =
  record
    { proxyCase =
        norm_like_near_miss
    ; sourceName =
        sourceHarnessCaseName norm_like_near_miss
    ; kind =
        badCase
    ; observedPass =
        false
    ; expectedOutcomeObserved =
        true
    ; representativeInvariant =
        true
    ; additive =
        true
    ; scalarCompatible =
        true
    ; twoHomogeneousEnergy =
        true
    ; fourPointResidualCancellation =
        false
    ; expectedOutcomeObservedIsTrue =
        refl
    }

canonicalProxyCaseReceipts : List ProxyCaseReceipt
canonicalProxyCaseReceipts =
  linearQuotientGluingReceipt
  ∷ representativeDependentLeakReceipt
  ∷ nonlinearQuotientGluingReceipt
  ∷ normLikeNearMissReceipt
  ∷ []

proxyCaseReceiptCount : Nat
proxyCaseReceiptCount =
  listLength canonicalProxyCaseReceipts

proxyCaseReceiptCountIs4 :
  proxyCaseReceiptCount ≡ 4
proxyCaseReceiptCountIs4 =
  refl

linearQuotientGluingPassed :
  observedPass linearQuotientGluingReceipt ≡ true
linearQuotientGluingPassed =
  refl

representativeDependentLeakFailed :
  observedPass representativeDependentLeakReceipt ≡ false
representativeDependentLeakFailed =
  refl

nonlinearQuotientGluingFailed :
  observedPass nonlinearQuotientGluingReceipt ≡ false
nonlinearQuotientGluingFailed =
  refl

normLikeNearMissFailed :
  observedPass normLikeNearMissReceipt ≡ false
normLikeNearMissFailed =
  refl

------------------------------------------------------------------------
-- Closed harness receipt.

controlCardText : String
controlCardText =
  "O Worker Lane 5 Dewey receipt; R record finite quotient-admissibility proxy result; C scripts/unification_gluing_quotient_admissibility_proxy_harness.py; S typed fail-closed Agda receipt only; L good quotient-linear case plus three visible obstruction cases; P import U-1a and composite boundaries; G promotion=false diagnostic_only=true; F quotient/theorem/promotion flags remain false."

resultInterpretationText : String
resultInterpretationText =
  "The finite proxy separates linear quotient gluing from representative leaks, nonlinear quotient gluing, and a norm-like near miss; it does not certify the true unification quotient."

record UnificationGluingQuotientAdmissibilityProxyHarnessResult : Setω where
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
    defaultParameters :
      String
    importedSupport :
      ImportedUnificationGluingQuotientSupport
    caseReceipts :
      List ProxyCaseReceipt
    caseReceiptCountIs4 :
      listLength caseReceipts ≡ 4
    okObserved :
      ok_observed ≡ true
    diagnosticOnlyTrue :
      diagnostic_only ≡ true
    promotionFalse :
      promotion ≡ false
    quotientAdmissibilityProvedFalse :
      quotientAdmissibilityProved ≡ false
    gluingLinearityProvedFalse :
      gluingLinearityProved ≡ false
    fourPointCancellationProvedFalse :
      fourPointCancellationProved ≡ false
    parallelogramProvedFalse :
      parallelogramProved ≡ false
    quadraticEmergenceProvedFalse :
      quadraticEmergenceProved ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    goodCasePassed :
      observedPass linearQuotientGluingReceipt ≡ true
    representativeLeakFailed :
      observedPass representativeDependentLeakReceipt ≡ false
    nonlinearGluingFailed :
      observedPass nonlinearQuotientGluingReceipt ≡ false
    normNearMissFailed :
      observedPass normLikeNearMissReceipt ≡ false
    controlCard :
      String
    interpretation :
      String

open UnificationGluingQuotientAdmissibilityProxyHarnessResult public

canonicalUnificationGluingQuotientAdmissibilityProxyHarnessResult :
  UnificationGluingQuotientAdmissibilityProxyHarnessResult
canonicalUnificationGluingQuotientAdmissibilityProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        jsonReceiptPath
    ; manifestChildReceipt =
        manifestChildReceiptPath
    ; scope =
        receiptScope
    ; runCommand =
        runCommandText
    ; defaultParameters =
        defaultParameterText
    ; importedSupport =
        canonicalImportedUnificationGluingQuotientSupport
    ; caseReceipts =
        canonicalProxyCaseReceipts
    ; caseReceiptCountIs4 =
        proxyCaseReceiptCountIs4
    ; okObserved =
        ok_observed_is_true
    ; diagnosticOnlyTrue =
        diagnostic_only_is_true
    ; promotionFalse =
        promotion_is_false
    ; quotientAdmissibilityProvedFalse =
        quotientAdmissibilityProved_is_false
    ; gluingLinearityProvedFalse =
        gluingLinearityProved_is_false
    ; fourPointCancellationProvedFalse =
        fourPointCancellationProved_is_false
    ; parallelogramProvedFalse =
        parallelogramProved_is_false
    ; quadraticEmergenceProvedFalse =
        quadraticEmergenceProved_is_false
    ; terminalPromotionFalse =
        terminalPromotion_is_false
    ; goodCasePassed =
        linearQuotientGluingPassed
    ; representativeLeakFailed =
        representativeDependentLeakFailed
    ; nonlinearGluingFailed =
        nonlinearQuotientGluingFailed
    ; normNearMissFailed =
        normLikeNearMissFailed
    ; controlCard =
        controlCardText
    ; interpretation =
        resultInterpretationText
    }
