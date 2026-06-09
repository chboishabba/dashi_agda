module DASHI.Physics.Closure.YMDominationSpectralMarginProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ym_domination_spectral_margin_proxy_harness.py
--
-- The harness is a finite symmetric-matrix diagnostic for the Yang-Mills
-- Hamiltonian domination spectral-margin budget
--
--   H_d >= c_delta Delta_YM,d + c_hol Hol_d - E_d
--
-- on a projected quotient sector.  It records three passing synthetic cases
-- and three failing synthetic countercases.  This module is a receipt only:
-- it does not prove a uniform spectral-margin theorem, Hamiltonian
-- domination, reflection positivity, OS transfer, continuum no-pollution, YM
-- Clay, or terminal promotion.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHamiltonianDominationErrorBudgetBoundary
  as ErrorBudget
import DASHI.Physics.Closure.YMHamiltonianDominationCompositeBoundary
  as Composite
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination
import DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult
  as Proxy

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Harness identity and run configuration.

sourceHarnessPath : String
sourceHarnessPath =
  "scripts/ym_domination_spectral_margin_proxy_harness.py"

jsonReceiptPath : String
jsonReceiptPath =
  "outputs/ym_domination_spectral_margin_proxy_smoke.json"

manifestChildReceiptPath : String
manifestChildReceiptPath =
  "outputs/local_clay_harness_manifest_children/ym_domination_spectral_margin_proxy_smoke.json"

receiptScope : String
receiptScope =
  "finite_spectral_margin_domination_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/ym_domination_spectral_margin_proxy_harness.py --dimension 6 --quotient-dimension 4 --json-output outputs/ym_domination_spectral_margin_proxy_smoke.json --json"

manifestCommandText : String
manifestCommandText =
  "python scripts/ym_domination_spectral_margin_proxy_harness.py --dimension 6 --quotient-dimension 4 --json-output outputs/local_clay_harness_manifest_children/ym_domination_spectral_margin_proxy_smoke.json --json"

defaultParameterText : String
defaultParameterText =
  "dimension=6, quotient_dimension=4, c_delta=0.72, c_hol=0.64, tolerance=1e-9, jacobi_sweeps=100"

spectralMarginProxyText : String
spectralMarginProxyText =
  "finite quotient matrix diagnostic for domination residual, holonomy floor, kinetic gap, E_d margin, and near-zero pollution"

------------------------------------------------------------------------
-- Imported YM domination/error-budget support.

errorBudgetReference : String
errorBudgetReference =
  "DASHI.Physics.Closure.YMHamiltonianDominationErrorBudgetBoundary"

compositeReference : String
compositeReference =
  "DASHI.Physics.Closure.YMHamiltonianDominationCompositeBoundary"

hodgeDominationReference : String
hodgeDominationReference =
  "DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary"

proxyReference : String
proxyReference =
  "DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult"

importsObserved : Bool
importsObserved =
  true

record ImportedYMSpectralMarginProxySupport : Setω where
  field
    errorBudgetBoundary :
      ErrorBudget.YMHamiltonianDominationErrorBudgetBoundary

    compositeBoundary :
      Composite.YMHamiltonianDominationCompositeBoundary

    finiteHodgeDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    dominationProxyHarnessResult :
      Proxy.YMHamiltonianDominationProxyHarnessResult

    importsObservedIsTrue :
      importsObserved ≡ true

    importedErrorBudgetStillOpen :
      ErrorBudget.errorBudgetClosedField errorBudgetBoundary ≡ false

    importedErrorBudgetDominationStillFalse :
      ErrorBudget.hamiltonianDominatesDefectPlusHolonomyProvedField
        errorBudgetBoundary
      ≡ false

    importedErrorBudgetReflectionStillFalse :
      ErrorBudget.reflectionPositiveTransferProvedField
        errorBudgetBoundary
      ≡ false

    importedErrorBudgetOSStillFalse :
      ErrorBudget.osContinuumTransferProvedField errorBudgetBoundary ≡ false

    importedErrorBudgetClayStillFalse :
      ErrorBudget.ymClayPromotedField errorBudgetBoundary ≡ false

    importedErrorBudgetTerminalStillFalse :
      ErrorBudget.terminalPromotionField errorBudgetBoundary ≡ false

    importedCompositeDominationStillFalse :
      Composite.dominationTheoremField compositeBoundary ≡ false

    importedCompositeOSTransferStillFalse :
      Composite.osTransferTheoremField compositeBoundary ≡ false

    importedCompositeContinuumStillFalse :
      Composite.continuumNoSpectralPollutionTheoremField
        compositeBoundary
      ≡ false

    importedHodgePlusHolonomyStillFalse :
      Domination.dominationPlusHolonomyProvedField
        finiteHodgeDominationBoundary
      ≡ false

    importedProxyPromotionStillFalse :
      Proxy.promotionField dominationProxyHarnessResult ≡ false

canonicalImportedYMSpectralMarginProxySupport :
  ImportedYMSpectralMarginProxySupport
canonicalImportedYMSpectralMarginProxySupport =
  record
    { errorBudgetBoundary =
        ErrorBudget.canonicalYMHamiltonianDominationErrorBudgetBoundary
    ; compositeBoundary =
        Composite.canonicalYMHamiltonianDominationCompositeBoundary
    ; finiteHodgeDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; dominationProxyHarnessResult =
        Proxy.canonicalYMHamiltonianDominationProxyHarnessResult
    ; importsObservedIsTrue =
        refl
    ; importedErrorBudgetStillOpen =
        ErrorBudget.canonicalErrorBudgetClosedFalse
    ; importedErrorBudgetDominationStillFalse =
        ErrorBudget.canonicalErrorBudgetDominationFalse
    ; importedErrorBudgetReflectionStillFalse =
        ErrorBudget.canonicalErrorBudgetReflectionPositiveTransferFalse
    ; importedErrorBudgetOSStillFalse =
        ErrorBudget.canonicalErrorBudgetOSContinuumTransferFalse
    ; importedErrorBudgetClayStillFalse =
        ErrorBudget.canonicalErrorBudgetYMClayFalse
    ; importedErrorBudgetTerminalStillFalse =
        ErrorBudget.canonicalErrorBudgetTerminalFalse
    ; importedCompositeDominationStillFalse =
        Composite.canonicalCompositeDominationFalse
    ; importedCompositeOSTransferStillFalse =
        Composite.canonicalCompositeOSTransferFalse
    ; importedCompositeContinuumStillFalse =
        Composite.canonicalCompositeContinuumNoSpectralPollutionFalse
    ; importedHodgePlusHolonomyStillFalse =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; importedProxyPromotionStillFalse =
        Proxy.canonicalHamiltonianDominationProxyPromotionFalse
    }

------------------------------------------------------------------------
-- Harness fields and cases.

data YMSpectralMarginHarnessField : Set where
  harnessIdentityField :
    YMSpectralMarginHarnessField
  outputPathField :
    YMSpectralMarginHarnessField
  manifestChildPathField :
    YMSpectralMarginHarnessField
  parameterField :
    YMSpectralMarginHarnessField
  importedSupportField :
    YMSpectralMarginHarnessField
  goodCaseField :
    YMSpectralMarginHarnessField
  badCaseField :
    YMSpectralMarginHarnessField
  quotientProjectionCheckField :
    YMSpectralMarginHarnessField
  dominationResidualCheckField :
    YMSpectralMarginHarnessField
  holonomyGapCheckField :
    YMSpectralMarginHarnessField
  kineticGapCheckField :
    YMSpectralMarginHarnessField
  stableEdMarginCheckField :
    YMSpectralMarginHarnessField
  noNearZeroPollutionCheckField :
    YMSpectralMarginHarnessField
  theoremFlagField :
    YMSpectralMarginHarnessField
  promotionFlagField :
    YMSpectralMarginHarnessField

canonicalYMSpectralMarginHarnessFields :
  List YMSpectralMarginHarnessField
canonicalYMSpectralMarginHarnessFields =
  harnessIdentityField
  ∷ outputPathField
  ∷ manifestChildPathField
  ∷ parameterField
  ∷ importedSupportField
  ∷ goodCaseField
  ∷ badCaseField
  ∷ quotientProjectionCheckField
  ∷ dominationResidualCheckField
  ∷ holonomyGapCheckField
  ∷ kineticGapCheckField
  ∷ stableEdMarginCheckField
  ∷ noNearZeroPollutionCheckField
  ∷ theoremFlagField
  ∷ promotionFlagField
  ∷ []

harnessFieldCount : Nat
harnessFieldCount =
  listCount canonicalYMSpectralMarginHarnessFields

harnessFieldCountIs15 :
  harnessFieldCount ≡ 15
harnessFieldCountIs15 =
  refl

data YMSpectralMarginCaseKind : Set where
  goodExpectedPassCase :
    YMSpectralMarginCaseKind
  badExpectedFailCase :
    YMSpectralMarginCaseKind

expectedPassForKind :
  YMSpectralMarginCaseKind →
  Bool
expectedPassForKind goodExpectedPassCase =
  true
expectedPassForKind badExpectedFailCase =
  false

record YMSpectralMarginCaseReceipt : Set where
  field
    caseName :
      String

    kind :
      YMSpectralMarginCaseKind

    expectedPass :
      Bool

    expectedPassMatchesKind :
      expectedPass ≡ expectedPassForKind kind

    diagnosticMeaning :
      String

open YMSpectralMarginCaseReceipt public

dominatedQuotientSectorCase :
  YMSpectralMarginCaseReceipt
dominatedQuotientSectorCase =
  record
    { caseName =
        "dominated_quotient_sector"
    ; kind =
        goodExpectedPassCase
    ; expectedPass =
        true
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "H dominates c_delta Delta plus c_hol Hol minus E on the quotient sector"
    }

holonomyControlledGapCase :
  YMSpectralMarginCaseReceipt
holonomyControlledGapCase =
  record
    { caseName =
        "holonomy_controlled_gap"
    ; kind =
        goodExpectedPassCase
    ; expectedPass =
        true
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "holonomy floor supplies a visible quotient gap budget"
    }

stableEdMarginCase :
  YMSpectralMarginCaseReceipt
stableEdMarginCase =
  record
    { caseName =
        "stable_Ed_margin"
    ; kind =
        goodExpectedPassCase
    ; expectedPass =
        true
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "small E_d leaves a positive Delta/Hol margin after row-sum budget subtraction"
    }

weakKineticTermCase :
  YMSpectralMarginCaseReceipt
weakKineticTermCase =
  record
    { caseName =
        "weak_kinetic_term"
    ; kind =
        badExpectedFailCase
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "kinetic Delta gap is too weak for the spectral-margin gate"
    }

missingHolonomyControlCase :
  YMSpectralMarginCaseReceipt
missingHolonomyControlCase =
  record
    { caseName =
        "missing_holonomy_control"
    ; kind =
        badExpectedFailCase
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "holonomy floor is missing in the vacuum-adjacent quotient sector"
    }

spectralPollutionNearZeroCase :
  YMSpectralMarginCaseReceipt
spectralPollutionNearZeroCase =
  record
    { caseName =
        "spectral_pollution_near_zero"
    ; kind =
        badExpectedFailCase
    ; expectedPass =
        false
    ; expectedPassMatchesKind =
        refl
    ; diagnosticMeaning =
        "near-zero H eigenvalue pollutes the quotient spectrum"
    }

canonicalGoodCases :
  List YMSpectralMarginCaseReceipt
canonicalGoodCases =
  dominatedQuotientSectorCase
  ∷ holonomyControlledGapCase
  ∷ stableEdMarginCase
  ∷ []

canonicalBadCases :
  List YMSpectralMarginCaseReceipt
canonicalBadCases =
  weakKineticTermCase
  ∷ missingHolonomyControlCase
  ∷ spectralPollutionNearZeroCase
  ∷ []

goodCaseCount : Nat
goodCaseCount =
  listCount canonicalGoodCases

badCaseCount : Nat
badCaseCount =
  listCount canonicalBadCases

goodCaseCountIs3 :
  goodCaseCount ≡ 3
goodCaseCountIs3 =
  refl

badCaseCountIs3 :
  badCaseCount ≡ 3
badCaseCountIs3 =
  refl

------------------------------------------------------------------------
-- Observed flags and non-claims.

ok_observed : Bool
ok_observed =
  true

diagnostic_only : Bool
diagnostic_only =
  true

promotion : Bool
promotion =
  false

spectralMarginTheoremProved : Bool
spectralMarginTheoremProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

reflectionPositiveTransferProved : Bool
reflectionPositiveTransferProved =
  false

osTransferProved : Bool
osTransferProved =
  false

continuumNoPollutionProved : Bool
continuumNoPollutionProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
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

spectralMarginTheoremProvedIsFalse :
  spectralMarginTheoremProved ≡ false
spectralMarginTheoremProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

reflectionPositiveTransferProvedIsFalse :
  reflectionPositiveTransferProved ≡ false
reflectionPositiveTransferProvedIsFalse =
  refl

osTransferProvedIsFalse :
  osTransferProved ≡ false
osTransferProvedIsFalse =
  refl

continuumNoPollutionProvedIsFalse :
  continuumNoPollutionProved ≡ false
continuumNoPollutionProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

data YMSpectralMarginNonClaimBoundary : Set where
  diagnosticOnlyNotSpectralMarginTheorem :
    YMSpectralMarginNonClaimBoundary
  finiteMatrixNotGaugeQuotientHamiltonian :
    YMSpectralMarginNonClaimBoundary
  noUniformEdAbsorptionEstimate :
    YMSpectralMarginNonClaimBoundary
  noHamiltonianDominationTheorem :
    YMSpectralMarginNonClaimBoundary
  noReflectionPositiveTransfer :
    YMSpectralMarginNonClaimBoundary
  noOSContinuumTransfer :
    YMSpectralMarginNonClaimBoundary
  noContinuumNoPollutionTheorem :
    YMSpectralMarginNonClaimBoundary
  noYMClayOrTerminalPromotion :
    YMSpectralMarginNonClaimBoundary

canonicalYMSpectralMarginNonClaimBoundaries :
  List YMSpectralMarginNonClaimBoundary
canonicalYMSpectralMarginNonClaimBoundaries =
  diagnosticOnlyNotSpectralMarginTheorem
  ∷ finiteMatrixNotGaugeQuotientHamiltonian
  ∷ noUniformEdAbsorptionEstimate
  ∷ noHamiltonianDominationTheorem
  ∷ noReflectionPositiveTransfer
  ∷ noOSContinuumTransfer
  ∷ noContinuumNoPollutionTheorem
  ∷ noYMClayOrTerminalPromotion
  ∷ []

nonClaimBoundaryCount : Nat
nonClaimBoundaryCount =
  listCount canonicalYMSpectralMarginNonClaimBoundaries

nonClaimBoundaryCountIs8 :
  nonClaimBoundaryCount ≡ 8
nonClaimBoundaryCountIs8 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record YMDominationSpectralMarginProxyHarnessResult : Setω where
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

    manifestCommand :
      String

    defaultParameters :
      String

    proxyMeaning :
      String

    importedSupport :
      ImportedYMSpectralMarginProxySupport

    fields :
      List YMSpectralMarginHarnessField

    fieldsAreCanonical :
      fields ≡ canonicalYMSpectralMarginHarnessFields

    fieldCount :
      Nat

    fieldCountIs15 :
      fieldCount ≡ 15

    goodCases :
      List YMSpectralMarginCaseReceipt

    goodCasesAreCanonical :
      goodCases ≡ canonicalGoodCases

    goodCaseCountField :
      Nat

    goodCaseCountFieldIs3 :
      goodCaseCountField ≡ 3

    badCases :
      List YMSpectralMarginCaseReceipt

    badCasesAreCanonical :
      badCases ≡ canonicalBadCases

    badCaseCountField :
      Nat

    badCaseCountFieldIs3 :
      badCaseCountField ≡ 3

    nonClaimBoundaries :
      List YMSpectralMarginNonClaimBoundary

    nonClaimBoundariesAreCanonical :
      nonClaimBoundaries ≡ canonicalYMSpectralMarginNonClaimBoundaries

    nonClaimBoundaryCountField :
      Nat

    nonClaimBoundaryCountFieldIs8 :
      nonClaimBoundaryCountField ≡ 8

    okObservedField :
      Bool

    okObservedFieldIsTrue :
      okObservedField ≡ true

    diagnosticOnlyField :
      Bool

    diagnosticOnlyFieldIsTrue :
      diagnosticOnlyField ≡ true

    promotionField :
      Bool

    promotionFieldIsFalse :
      promotionField ≡ false

    spectralMarginTheoremProvedField :
      Bool

    spectralMarginTheoremProvedFieldIsFalse :
      spectralMarginTheoremProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    reflectionPositiveTransferProvedField :
      Bool

    reflectionPositiveTransferProvedFieldIsFalse :
      reflectionPositiveTransferProvedField ≡ false

    osTransferProvedField :
      Bool

    osTransferProvedFieldIsFalse :
      osTransferProvedField ≡ false

    continuumNoPollutionProvedField :
      Bool

    continuumNoPollutionProvedFieldIsFalse :
      continuumNoPollutionProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    theoremFlagSummary :
      String

    boundaryNotes :
      List String

    noPromotionEliminator :
      promotionField ≡ true → ⊥

open YMDominationSpectralMarginProxyHarnessResult public

canonicalYMDominationSpectralMarginProxyHarnessResult :
  YMDominationSpectralMarginProxyHarnessResult
canonicalYMDominationSpectralMarginProxyHarnessResult =
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
    ; manifestCommand =
        manifestCommandText
    ; defaultParameters =
        defaultParameterText
    ; proxyMeaning =
        spectralMarginProxyText
    ; importedSupport =
        canonicalImportedYMSpectralMarginProxySupport
    ; fields =
        canonicalYMSpectralMarginHarnessFields
    ; fieldsAreCanonical =
        refl
    ; fieldCount =
        harnessFieldCount
    ; fieldCountIs15 =
        harnessFieldCountIs15
    ; goodCases =
        canonicalGoodCases
    ; goodCasesAreCanonical =
        refl
    ; goodCaseCountField =
        goodCaseCount
    ; goodCaseCountFieldIs3 =
        goodCaseCountIs3
    ; badCases =
        canonicalBadCases
    ; badCasesAreCanonical =
        refl
    ; badCaseCountField =
        badCaseCount
    ; badCaseCountFieldIs3 =
        badCaseCountIs3
    ; nonClaimBoundaries =
        canonicalYMSpectralMarginNonClaimBoundaries
    ; nonClaimBoundariesAreCanonical =
        refl
    ; nonClaimBoundaryCountField =
        nonClaimBoundaryCount
    ; nonClaimBoundaryCountFieldIs8 =
        nonClaimBoundaryCountIs8
    ; okObservedField =
        ok_observed
    ; okObservedFieldIsTrue =
        ok_observed_is_true
    ; diagnosticOnlyField =
        diagnostic_only
    ; diagnosticOnlyFieldIsTrue =
        diagnostic_only_is_true
    ; promotionField =
        promotion
    ; promotionFieldIsFalse =
        promotion_is_false
    ; spectralMarginTheoremProvedField =
        spectralMarginTheoremProved
    ; spectralMarginTheoremProvedFieldIsFalse =
        spectralMarginTheoremProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; reflectionPositiveTransferProvedField =
        reflectionPositiveTransferProved
    ; reflectionPositiveTransferProvedFieldIsFalse =
        reflectionPositiveTransferProvedIsFalse
    ; osTransferProvedField =
        osTransferProved
    ; osTransferProvedFieldIsFalse =
        osTransferProvedIsFalse
    ; continuumNoPollutionProvedField =
        continuumNoPollutionProved
    ; continuumNoPollutionProvedFieldIsFalse =
        continuumNoPollutionProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; theoremFlagSummary =
        "ok_observed=true; diagnostic_only=true; promotion=false; spectral margin theorem, Hamiltonian domination, reflection-positive transfer, OS transfer, continuum no-pollution, YM Clay, and terminal promotion are false"
    ; boundaryNotes =
        "Good case dominated_quotient_sector records a positive quotient domination residual in the synthetic matrix proxy"
        ∷ "Good case holonomy_controlled_gap records a visible holonomy-controlled quotient gap"
        ∷ "Good case stable_Ed_margin records positive synthetic E_d margin after row-sum budget subtraction"
        ∷ "Bad case weak_kinetic_term fails the kinetic gap gate"
        ∷ "Bad case missing_holonomy_control fails the holonomy floor gate"
        ∷ "Bad case spectral_pollution_near_zero fails the no-near-zero-pollution gate"
        ∷ "The receipt imports the YM Hamiltonian domination error-budget boundary and keeps all imported theorem gates false"
        ∷ []
    ; noPromotionEliminator =
        λ ()
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalSpectralMarginProxyOkObservedTrue :
  okObservedField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  true
canonicalSpectralMarginProxyOkObservedTrue =
  refl

canonicalSpectralMarginProxyDiagnosticOnlyTrue :
  diagnosticOnlyField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  true
canonicalSpectralMarginProxyDiagnosticOnlyTrue =
  refl

canonicalSpectralMarginProxyPromotionFalse :
  promotionField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginProxyPromotionFalse =
  refl

canonicalSpectralMarginTheoremFalse :
  spectralMarginTheoremProvedField
    canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginTheoremFalse =
  refl

canonicalSpectralMarginHamiltonianDominationFalse :
  hamiltonianDominationProvedField
    canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginHamiltonianDominationFalse =
  refl

canonicalSpectralMarginReflectionPositiveTransferFalse :
  reflectionPositiveTransferProvedField
    canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginReflectionPositiveTransferFalse =
  refl

canonicalSpectralMarginOSTransferFalse :
  osTransferProvedField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginOSTransferFalse =
  refl

canonicalSpectralMarginContinuumNoPollutionFalse :
  continuumNoPollutionProvedField
    canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginContinuumNoPollutionFalse =
  refl

canonicalSpectralMarginYMClayFalse :
  ymClayPromotedField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginYMClayFalse =
  refl

canonicalSpectralMarginTerminalFalse :
  terminalPromotionField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  false
canonicalSpectralMarginTerminalFalse =
  refl

noSpectralMarginPromotionFromProxyReceipt :
  promotionField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  true →
  ⊥
noSpectralMarginPromotionFromProxyReceipt ()

noYMClayPromotionFromSpectralMarginProxyReceipt :
  ymClayPromotedField canonicalYMDominationSpectralMarginProxyHarnessResult
  ≡
  true →
  ⊥
noYMClayPromotionFromSpectralMarginProxyReceipt ()
