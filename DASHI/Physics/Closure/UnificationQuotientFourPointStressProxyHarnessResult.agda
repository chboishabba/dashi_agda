module DASHI.Physics.Closure.UnificationQuotientFourPointStressProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/unification_quotient_four_point_stress_harness.py
--
-- The harness stresses the quotient/four-point unification lane with one
-- quadratic representative-invariant good case and four visible obstruction
-- cases.  This module records only the executable diagnostic result.  It does
-- not construct the admissible quotient, prove gluing linearity, prove
-- four-point cancellation, prove the parallelogram law, derive quadratic
-- emergence, or promote terminal unification.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.GluingResidualForcesFourPointCancellationBoundary
  as Residual
import DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary
  as Composite
import DASHI.Physics.Closure.UnificationGluingQuotientAdmissibilityProxyHarnessResult
  as QuotientProxy

------------------------------------------------------------------------
-- Local utilities.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Harness identity and expected output.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/unification_quotient_four_point_stress_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/unification_quotient_four_point_stress_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/unification_quotient_four_point_stress_smoke.json"

receiptScope : String
receiptScope =
  "finite_unification_quotient_four_point_stress_proxy_diagnostic_only"

expectedRunCommandText : String
expectedRunCommandText =
  "python scripts/unification_quotient_four_point_stress_harness.py --json-output outputs/unification_quotient_four_point_stress_smoke.json --json"

expectedManifestCommandText : String
expectedManifestCommandText =
  "python scripts/unification_quotient_four_point_stress_harness.py --json-output outputs/local_clay_harness_manifest_children/unification_quotient_four_point_stress_smoke.json --json"

summaryText : String
summaryText =
  "quadratic quotient good case passes; representative leak, nonlinear gluing, p-norm near miss, and asymmetric cross-term fail"

------------------------------------------------------------------------
-- Imported support.

gluingLinearityCompositeReference : String
gluingLinearityCompositeReference =
  "DASHI.Physics.Closure.UnificationGluingLinearityCompositeBoundary"

quotientAdmissibilityProxyReference : String
quotientAdmissibilityProxyReference =
  "DASHI.Physics.Closure.UnificationGluingQuotientAdmissibilityProxyHarnessResult"

gluingResidualFourPointReference : String
gluingResidualFourPointReference =
  "DASHI.Physics.Closure.GluingResidualForcesFourPointCancellationBoundary"

gluingLinearityCompositeImported : Bool
gluingLinearityCompositeImported =
  true

quotientAdmissibilityProxyImported : Bool
quotientAdmissibilityProxyImported =
  true

gluingResidualFourPointImported : Bool
gluingResidualFourPointImported =
  true

record ImportedUnificationFourPointStressSupport : Setω where
  field
    gluingLinearityComposite :
      Composite.UnificationGluingLinearityCompositeBoundary

    quotientAdmissibilityProxy :
      QuotientProxy.UnificationGluingQuotientAdmissibilityProxyHarnessResult

    gluingResidualFourPointBoundary :
      Residual.GluingResidualForcesFourPointCancellationBoundary

    gluingLinearityCompositeImportedIsTrue :
      gluingLinearityCompositeImported ≡ true

    quotientAdmissibilityProxyImportedIsTrue :
      quotientAdmissibilityProxyImported ≡ true

    gluingResidualFourPointImportedIsTrue :
      gluingResidualFourPointImported ≡ true

    importedCompositePromotionFlagsAllFalse :
      Composite.theoremPromotionFlagsAllFalse gluingLinearityComposite ≡ true

    importedCompositeUnificationPromotionFalse :
      Composite.unificationPromoted gluingLinearityComposite ≡ false

    importedQuotientAdmissibilityStillOpen :
      QuotientProxy.quotientAdmissibilityProved ≡ false

    importedQuotientGluingLinearityStillOpen :
      QuotientProxy.gluingLinearityProved ≡ false

    importedQuotientFourPointStillOpen :
      QuotientProxy.fourPointCancellationProved ≡ false

    importedQuotientTerminalPromotionFalse :
      QuotientProxy.terminalPromotion ≡ false

    importedResidualFourPointStillOpen :
      Residual.fourPointDefectVanishes gluingResidualFourPointBoundary ≡ false

    importedResidualParallelogramStillOpen :
      Residual.parallelogramLawProved gluingResidualFourPointBoundary ≡ false

    importedResidualQuadraticEmergenceStillOpen :
      Residual.quadraticFormEmergenceApplied gluingResidualFourPointBoundary ≡ false

    importedResidualTerminalPromotionFalse :
      Residual.terminalUnificationPromoted gluingResidualFourPointBoundary ≡ false

canonicalImportedUnificationFourPointStressSupport :
  ImportedUnificationFourPointStressSupport
canonicalImportedUnificationFourPointStressSupport =
  record
    { gluingLinearityComposite =
        Composite.canonicalUnificationGluingLinearityCompositeBoundary
    ; quotientAdmissibilityProxy =
        QuotientProxy.canonicalUnificationGluingQuotientAdmissibilityProxyHarnessResult
    ; gluingResidualFourPointBoundary =
        Residual.canonicalGluingResidualForcesFourPointCancellationBoundary
    ; gluingLinearityCompositeImportedIsTrue =
        refl
    ; quotientAdmissibilityProxyImportedIsTrue =
        refl
    ; gluingResidualFourPointImportedIsTrue =
        refl
    ; importedCompositePromotionFlagsAllFalse =
        Composite.canonicalCompositeTheoremPromotionFlagsAllFalse
    ; importedCompositeUnificationPromotionFalse =
        Composite.canonicalCompositeUnificationPromotionFalse
    ; importedQuotientAdmissibilityStillOpen =
        QuotientProxy.quotientAdmissibilityProved_is_false
    ; importedQuotientGluingLinearityStillOpen =
        QuotientProxy.gluingLinearityProved_is_false
    ; importedQuotientFourPointStillOpen =
        QuotientProxy.fourPointCancellationProved_is_false
    ; importedQuotientTerminalPromotionFalse =
        QuotientProxy.terminalPromotion_is_false
    ; importedResidualFourPointStillOpen =
        Residual.canonicalFourPointDefectStillOpen
    ; importedResidualParallelogramStillOpen =
        Residual.canonicalParallelogramLawStillOpen
    ; importedResidualQuadraticEmergenceStillOpen =
        Residual.canonicalQuadraticFormEmergenceStillBlocked
    ; importedResidualTerminalPromotionFalse =
        Residual.canonicalTerminalUnificationPromotionFalse
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
-- Harness cases.

data StressCaseKind : Set where
  goodCase :
    StressCaseKind
  badCase :
    StressCaseKind

data UnificationQuotientFourPointStressCase : Set where
  quadratic_quotient_representative_invariant :
    UnificationQuotientFourPointStressCase
  representative_shift_leak :
    UnificationQuotientFourPointStressCase
  nonlinear_gluing_quotient :
    UnificationQuotientFourPointStressCase
  p_norm_nonquadratic_near_miss :
    UnificationQuotientFourPointStressCase
  asymmetric_cross_term :
    UnificationQuotientFourPointStressCase

caseName : UnificationQuotientFourPointStressCase → String
caseName quadratic_quotient_representative_invariant =
  "quadratic_quotient_representative_invariant"
caseName representative_shift_leak =
  "representative_shift_leak"
caseName nonlinear_gluing_quotient =
  "nonlinear_gluing_quotient"
caseName p_norm_nonquadratic_near_miss =
  "p_norm_nonquadratic_near_miss"
caseName asymmetric_cross_term =
  "asymmetric_cross_term"

caseKind : UnificationQuotientFourPointStressCase → StressCaseKind
caseKind quadratic_quotient_representative_invariant =
  goodCase
caseKind representative_shift_leak =
  badCase
caseKind nonlinear_gluing_quotient =
  badCase
caseKind p_norm_nonquadratic_near_miss =
  badCase
caseKind asymmetric_cross_term =
  badCase

expectedObservedPass : UnificationQuotientFourPointStressCase → Bool
expectedObservedPass quadratic_quotient_representative_invariant =
  true
expectedObservedPass representative_shift_leak =
  false
expectedObservedPass nonlinear_gluing_quotient =
  false
expectedObservedPass p_norm_nonquadratic_near_miss =
  false
expectedObservedPass asymmetric_cross_term =
  false

record StressCaseReceipt : Set where
  field
    stressCase :
      UnificationQuotientFourPointStressCase
    sourceName :
      String
    kind :
      StressCaseKind
    kindIsCanonical :
      kind ≡ caseKind stressCase
    observedPass :
      Bool
    observedPassIsExpected :
      observedPass ≡ expectedObservedPass stressCase
    theoremProvedHere :
      Bool
    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

mkStressCaseReceipt :
  (stressCase : UnificationQuotientFourPointStressCase) →
  StressCaseReceipt
mkStressCaseReceipt stressCase =
  record
    { stressCase =
        stressCase
    ; sourceName =
        caseName stressCase
    ; kind =
        caseKind stressCase
    ; kindIsCanonical =
        refl
    ; observedPass =
        expectedObservedPass stressCase
    ; observedPassIsExpected =
        refl
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    }

canonicalStressCaseReceipts : List StressCaseReceipt
canonicalStressCaseReceipts =
  mkStressCaseReceipt quadratic_quotient_representative_invariant
  ∷ mkStressCaseReceipt representative_shift_leak
  ∷ mkStressCaseReceipt nonlinear_gluing_quotient
  ∷ mkStressCaseReceipt p_norm_nonquadratic_near_miss
  ∷ mkStressCaseReceipt asymmetric_cross_term
  ∷ []

stressCaseCount : Nat
stressCaseCount =
  listLength canonicalStressCaseReceipts

stressCaseCountIs5 :
  stressCaseCount ≡ 5
stressCaseCountIs5 =
  refl

------------------------------------------------------------------------
-- Receipt record.

record UnificationQuotientFourPointStressProxyHarnessResult : Setω where
  field
    importedSupport :
      ImportedUnificationFourPointStressSupport
    sourceHarnessPathField :
      String
    jsonReceiptPathField :
      String
    manifestChildReceiptPathField :
      String
    receiptScopeField :
      String
    caseReceipts :
      List StressCaseReceipt
    caseCount :
      Nat
    caseCountIs5 :
      caseCount ≡ 5
    caseCountMatchesRows :
      caseCount ≡ listLength caseReceipts
    okObserved :
      Bool
    okObservedIsTrue :
      okObserved ≡ true
    diagnosticOnly :
      Bool
    diagnosticOnlyIsTrue :
      diagnosticOnly ≡ true
    promotionFlag :
      Bool
    promotionFlagIsFalse :
      promotionFlag ≡ false
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
    summary :
      String

canonicalUnificationQuotientFourPointStressProxyHarnessResult :
  UnificationQuotientFourPointStressProxyHarnessResult
canonicalUnificationQuotientFourPointStressProxyHarnessResult =
  record
    { importedSupport =
        canonicalImportedUnificationFourPointStressSupport
    ; sourceHarnessPathField =
        sourceHarnessPath
    ; jsonReceiptPathField =
        jsonReceiptPath
    ; manifestChildReceiptPathField =
        manifestChildReceiptPath
    ; receiptScopeField =
        receiptScope
    ; caseReceipts =
        canonicalStressCaseReceipts
    ; caseCount =
        stressCaseCount
    ; caseCountIs5 =
        stressCaseCountIs5
    ; caseCountMatchesRows =
        refl
    ; okObserved =
        ok_observed
    ; okObservedIsTrue =
        ok_observed_is_true
    ; diagnosticOnly =
        diagnostic_only
    ; diagnosticOnlyIsTrue =
        diagnostic_only_is_true
    ; promotionFlag =
        promotion
    ; promotionFlagIsFalse =
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
    ; summary =
        summaryText
    }

------------------------------------------------------------------------
-- Compact governance card.

governanceSummaryRows : List String
governanceSummaryRows =
  "O: Lane 1 / Noether receipt for the quotient four-point stress proxy harness."
  ∷ "R: bind scripts/unification_quotient_four_point_stress_harness.py to a fail-closed Agda receipt."
  ∷ "C: records source path, direct output, manifest child output, one good quadratic case, and four bad obstruction cases."
  ∷ "S: ok_observed=true, diagnostic_only=true, promotion=false."
  ∷ "L: executable diagnostic -> Agda receipt -> future manifest/Everything wiring; no theorem promotion."
  ∷ "P: use the stress harness as a quotient/four-point near-miss separator only."
  ∷ "G: quotientAdmissibilityProved=false, gluingLinearityProved=false, fourPointCancellationProved=false, parallelogramProved=false, quadraticEmergenceProved=false, terminalPromotion=false."
  ∷ "F: real quotient admissibility, gluing linearity, four-point cancellation, parallelogram, and quadratic emergence remain open."
  ∷ []

governanceSummaryRowCount : Nat
governanceSummaryRowCount =
  listLength governanceSummaryRows

governanceSummaryRowCountIs8 :
  governanceSummaryRowCount ≡ 8
governanceSummaryRowCountIs8 =
  refl

promotionImpossibleHere :
  terminalPromotion ≡ true →
  false ≡ true
promotionImpossibleHere ()
