module DASHI.Physics.Closure.YMHamiltonianDominationProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ym_hamiltonian_domination_proxy_harness.py
--
-- The harness is a deterministic finite matrix diagnostic for the boundary
-- recorded in:
--
--   YMHamiltonianDominatesFiniteHodgeDefectBoundary
--
-- It checks one PSD-dominated finite quotient case, one weak-H
-- counterexample, and one non-holonomy-controlled near-zero sector
-- counterexample for the proxy inequality:
--
--   H >= c1 * Delta + c2 * Hol - E.
--
-- This module records the diagnostic result only.  It does not prove the
-- Yang-Mills Hamiltonian domination theorem, OS transfer, continuum transfer,
-- Clay Yang-Mills, or terminal promotion.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Boundary

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
  "scripts/ym_hamiltonian_domination_proxy_harness.py"

defaultJsonReceiptPath : String
defaultJsonReceiptPath =
  "outputs/ym_hamiltonian_domination_proxy_harness.json"

receiptScope : String
receiptScope =
  "finite_quotient_matrix_hamiltonian_domination_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/ym_hamiltonian_domination_proxy_harness.py --json-output outputs/ym_hamiltonian_domination_proxy_harness.json --json"

defaultParameterText : String
defaultParameterText =
  "dimension=5, quotient_dimension=3, c1=0.6, c2=0.8, energy_shift=0.05, tolerance=1e-9, holonomy_floor=0.05, near_zero_floor=0.05, jacobi_sweeps=80"

claimScopeText : String
claimScopeText =
  "finite quotient matrix diagnostic proxy only"

------------------------------------------------------------------------
-- Imported Hamiltonian domination boundary support.

boundaryReference : String
boundaryReference =
  "DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary"

boundaryImported : Bool
boundaryImported =
  true

record ImportedHamiltonianDominationBoundarySupport : Setω where
  field
    dominationBoundary :
      Boundary.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    boundaryImportedIsTrue :
      boundaryImported ≡ true

    importedHamiltonianDominationTheoremStillFalse :
      Boundary.dominationPlusHolonomyProvedField
        dominationBoundary
      ≡
      false

    importedFiniteHodgeDominationStillFalse :
      Boundary.hamiltonianDominatesFiniteHodgeDefectProvedField
        dominationBoundary
      ≡
      false

    importedOSTransferStillFalse :
      Boundary.reflectionPositivityOSOnGaugeQuotientProvedField
        dominationBoundary
      ≡
      false

    importedContinuumTransferStillFalse :
      Boundary.continuumTransferNoSpectralPollutionProvedField
        dominationBoundary
      ≡
      false

    importedYMClayStillFalse :
      Boundary.clayYangMillsPromotedField
        dominationBoundary
      ≡
      false

    importedTerminalPromotionStillFalse :
      Boundary.terminalPromotionField
        dominationBoundary
      ≡
      false

canonicalImportedHamiltonianDominationBoundarySupport :
  ImportedHamiltonianDominationBoundarySupport
canonicalImportedHamiltonianDominationBoundarySupport =
  record
    { dominationBoundary =
        Boundary.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; boundaryImportedIsTrue =
        refl
    ; importedHamiltonianDominationTheoremStillFalse =
        Boundary.dominationPlusHolonomyProvedIsFalse
    ; importedFiniteHodgeDominationStillFalse =
        Boundary.hamiltonianDominatesFiniteHodgeDefectProvedIsFalse
    ; importedOSTransferStillFalse =
        Boundary.reflectionPositivityOSOnGaugeQuotientProvedIsFalse
    ; importedContinuumTransferStillFalse =
        Boundary.continuumTransferNoSpectralPollutionProvedIsFalse
    ; importedYMClayStillFalse =
        Boundary.clayYangMillsPromotedIsFalse
    ; importedTerminalPromotionStillFalse =
        Boundary.terminalPromotionIsFalse
    }

------------------------------------------------------------------------
-- Top-level harness fields and governance booleans.

data YMHamiltonianDominationProxyHarnessField : Set where
  harnessIdentityField :
    YMHamiltonianDominationProxyHarnessField
  parametersField :
    YMHamiltonianDominationProxyHarnessField
  importedBoundaryField :
    YMHamiltonianDominationProxyHarnessField
  casesField :
    YMHamiltonianDominationProxyHarnessField
  checksField :
    YMHamiltonianDominationProxyHarnessField
  marginFieldsField :
    YMHamiltonianDominationProxyHarnessField
  validationFlagsField :
    YMHamiltonianDominationProxyHarnessField
  theoremFlagsField :
    YMHamiltonianDominationProxyHarnessField
  nonClaimBoundaryField :
    YMHamiltonianDominationProxyHarnessField
  summaryField :
    YMHamiltonianDominationProxyHarnessField

canonicalYMHamiltonianDominationProxyHarnessFields :
  List YMHamiltonianDominationProxyHarnessField
canonicalYMHamiltonianDominationProxyHarnessFields =
  harnessIdentityField
  ∷ parametersField
  ∷ importedBoundaryField
  ∷ casesField
  ∷ checksField
  ∷ marginFieldsField
  ∷ validationFlagsField
  ∷ theoremFlagsField
  ∷ nonClaimBoundaryField
  ∷ summaryField
  ∷ []

harnessFieldCount : Nat
harnessFieldCount =
  listCount canonicalYMHamiltonianDominationProxyHarnessFields

harnessFieldCountIs10 :
  harnessFieldCount ≡ 10
harnessFieldCountIs10 =
  refl

ok_observed : Bool
ok_observed =
  true

promotion : Bool
promotion =
  false

hamiltonianDominationTheoremProved : Bool
hamiltonianDominationTheoremProved =
  false

osTransferUnlocked : Bool
osTransferUnlocked =
  false

continuumTransferUnlocked : Bool
continuumTransferUnlocked =
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

promotion_is_false :
  promotion ≡ false
promotion_is_false =
  refl

hamiltonianDominationTheoremProvedIsFalse :
  hamiltonianDominationTheoremProved ≡ false
hamiltonianDominationTheoremProvedIsFalse =
  refl

osTransferUnlockedIsFalse :
  osTransferUnlocked ≡ false
osTransferUnlockedIsFalse =
  refl

continuumTransferUnlockedIsFalse :
  continuumTransferUnlocked ≡ false
continuumTransferUnlockedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Proxy cases, checks, and expected outcomes.

data YMHamiltonianDominationProxyCase : Set where
  goodPSDDominatedFiniteQuotientCase :
    YMHamiltonianDominationProxyCase
  badWeakHCase :
    YMHamiltonianDominationProxyCase
  badNonHolonomyControlledNearZeroSectorCase :
    YMHamiltonianDominationProxyCase

caseName : YMHamiltonianDominationProxyCase → String
caseName goodPSDDominatedFiniteQuotientCase =
  "good_psd_dominated"
caseName badWeakHCase =
  "bad_weak_h"
caseName badNonHolonomyControlledNearZeroSectorCase =
  "bad_non_holonomy_controlled_near_zero"

caseDescription : YMHamiltonianDominationProxyCase → String
caseDescription goodPSDDominatedFiniteQuotientCase =
  "PSD surplus over c1*Delta + c2*Hol - E on the quotient; expected to pass."
caseDescription badWeakHCase =
  "Hamiltonian weakened in one quotient direction so H - comparison has a negative eigenvalue."
caseDescription badNonHolonomyControlledNearZeroSectorCase =
  "Near-zero Hamiltonian direction with tiny holonomy floor; expected to fail control and domination."

expectedCasePass : YMHamiltonianDominationProxyCase → Bool
expectedCasePass goodPSDDominatedFiniteQuotientCase =
  true
expectedCasePass badWeakHCase =
  false
expectedCasePass badNonHolonomyControlledNearZeroSectorCase =
  false

data YMHamiltonianDominationProxyCheck : Set where
  symmetricFormsCheck :
    YMHamiltonianDominationProxyCheck
  quotientStableCheck :
    YMHamiltonianDominationProxyCheck
  dominationPSDMarginCheck :
    YMHamiltonianDominationProxyCheck
  holonomyControlledOrNoNearZeroHSectorCheck :
    YMHamiltonianDominationProxyCheck

checkName : YMHamiltonianDominationProxyCheck → String
checkName symmetricFormsCheck =
  "symmetric_forms"
checkName quotientStableCheck =
  "quotient_stable"
checkName dominationPSDMarginCheck =
  "domination_psd_margin"
checkName holonomyControlledOrNoNearZeroHSectorCheck =
  "holonomy_controlled_or_no_near_zero_h_sector"

canonicalYMHamiltonianDominationProxyChecks :
  List YMHamiltonianDominationProxyCheck
canonicalYMHamiltonianDominationProxyChecks =
  symmetricFormsCheck
  ∷ quotientStableCheck
  ∷ dominationPSDMarginCheck
  ∷ holonomyControlledOrNoNearZeroHSectorCheck
  ∷ []

proxyCheckCount : Nat
proxyCheckCount =
  listCount canonicalYMHamiltonianDominationProxyChecks

proxyCheckCountIs4 :
  proxyCheckCount ≡ 4
proxyCheckCountIs4 =
  refl

expectedCheckOutcome :
  YMHamiltonianDominationProxyCase →
  YMHamiltonianDominationProxyCheck →
  Bool
expectedCheckOutcome goodPSDDominatedFiniteQuotientCase symmetricFormsCheck =
  true
expectedCheckOutcome goodPSDDominatedFiniteQuotientCase quotientStableCheck =
  true
expectedCheckOutcome goodPSDDominatedFiniteQuotientCase dominationPSDMarginCheck =
  true
expectedCheckOutcome
  goodPSDDominatedFiniteQuotientCase
  holonomyControlledOrNoNearZeroHSectorCheck =
  true
expectedCheckOutcome badWeakHCase symmetricFormsCheck =
  true
expectedCheckOutcome badWeakHCase quotientStableCheck =
  true
expectedCheckOutcome badWeakHCase dominationPSDMarginCheck =
  false
expectedCheckOutcome badWeakHCase holonomyControlledOrNoNearZeroHSectorCheck =
  true
expectedCheckOutcome
  badNonHolonomyControlledNearZeroSectorCase
  symmetricFormsCheck =
  true
expectedCheckOutcome
  badNonHolonomyControlledNearZeroSectorCase
  quotientStableCheck =
  true
expectedCheckOutcome
  badNonHolonomyControlledNearZeroSectorCase
  dominationPSDMarginCheck =
  false
expectedCheckOutcome
  badNonHolonomyControlledNearZeroSectorCase
  holonomyControlledOrNoNearZeroHSectorCheck =
  false

record YMHamiltonianDominationProxyCheckReceipt : Set where
  field
    case :
      YMHamiltonianDominationProxyCase

    check :
      YMHamiltonianDominationProxyCheck

    observedOutcome :
      Bool

    observedOutcomeIsExpected :
      observedOutcome ≡ expectedCheckOutcome case check

    checkLabel :
      String

open YMHamiltonianDominationProxyCheckReceipt public

mkYMHamiltonianDominationProxyCheckReceipt :
  (case : YMHamiltonianDominationProxyCase) →
  (check : YMHamiltonianDominationProxyCheck) →
  YMHamiltonianDominationProxyCheckReceipt
mkYMHamiltonianDominationProxyCheckReceipt case check =
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

goodPSDDominatedCheckReceipts :
  List YMHamiltonianDominationProxyCheckReceipt
goodPSDDominatedCheckReceipts =
  mkYMHamiltonianDominationProxyCheckReceipt
    goodPSDDominatedFiniteQuotientCase
    symmetricFormsCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    goodPSDDominatedFiniteQuotientCase
    quotientStableCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    goodPSDDominatedFiniteQuotientCase
    dominationPSDMarginCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    goodPSDDominatedFiniteQuotientCase
    holonomyControlledOrNoNearZeroHSectorCheck
  ∷ []

badWeakHCheckReceipts :
  List YMHamiltonianDominationProxyCheckReceipt
badWeakHCheckReceipts =
  mkYMHamiltonianDominationProxyCheckReceipt
    badWeakHCase
    symmetricFormsCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badWeakHCase
    quotientStableCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badWeakHCase
    dominationPSDMarginCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badWeakHCase
    holonomyControlledOrNoNearZeroHSectorCheck
  ∷ []

badNonHolonomyControlledNearZeroCheckReceipts :
  List YMHamiltonianDominationProxyCheckReceipt
badNonHolonomyControlledNearZeroCheckReceipts =
  mkYMHamiltonianDominationProxyCheckReceipt
    badNonHolonomyControlledNearZeroSectorCase
    symmetricFormsCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badNonHolonomyControlledNearZeroSectorCase
    quotientStableCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badNonHolonomyControlledNearZeroSectorCase
    dominationPSDMarginCheck
  ∷ mkYMHamiltonianDominationProxyCheckReceipt
    badNonHolonomyControlledNearZeroSectorCase
    holonomyControlledOrNoNearZeroHSectorCheck
  ∷ []

goodPSDDominatedCheckReceiptCountIs4 :
  listCount goodPSDDominatedCheckReceipts ≡ 4
goodPSDDominatedCheckReceiptCountIs4 =
  refl

badWeakHCheckReceiptCountIs4 :
  listCount badWeakHCheckReceipts ≡ 4
badWeakHCheckReceiptCountIs4 =
  refl

badNonHolonomyControlledNearZeroCheckReceiptCountIs4 :
  listCount badNonHolonomyControlledNearZeroCheckReceipts ≡ 4
badNonHolonomyControlledNearZeroCheckReceiptCountIs4 =
  refl

------------------------------------------------------------------------
-- Margin fields.

data YMHamiltonianDominationMarginField : Set where
  dominationMarginField :
    YMHamiltonianDominationMarginField
  hMinEigenvalueField :
    YMHamiltonianDominationMarginField
  deltaMinEigenvalueField :
    YMHamiltonianDominationMarginField
  holMinEigenvalueField :
    YMHamiltonianDominationMarginField
  comparisonMinEigenvalueField :
    YMHamiltonianDominationMarginField
  quotientCommutatorErrorField :
    YMHamiltonianDominationMarginField
  maxSymmetryErrorField :
    YMHamiltonianDominationMarginField
  hMinusComparisonMinField :
    YMHamiltonianDominationMarginField

canonicalYMHamiltonianDominationMarginFields :
  List YMHamiltonianDominationMarginField
canonicalYMHamiltonianDominationMarginFields =
  dominationMarginField
  ∷ hMinEigenvalueField
  ∷ deltaMinEigenvalueField
  ∷ holMinEigenvalueField
  ∷ comparisonMinEigenvalueField
  ∷ quotientCommutatorErrorField
  ∷ maxSymmetryErrorField
  ∷ hMinusComparisonMinField
  ∷ []

marginFieldCount : Nat
marginFieldCount =
  listCount canonicalYMHamiltonianDominationMarginFields

marginFieldCountIs8 :
  marginFieldCount ≡ 8
marginFieldCountIs8 =
  refl

record YMHamiltonianDominationCaseMargins : Set where
  field
    dominationMarginText :
      String

    hMinEigenvalueText :
      String

    deltaMinEigenvalueText :
      String

    holMinEigenvalueText :
      String

    comparisonMinEigenvalueText :
      String

    quotientCommutatorErrorText :
      String

    maxSymmetryErrorText :
      String

    hMinusComparisonMinText :
      String

open YMHamiltonianDominationCaseMargins public

goodPSDDominatedCaseMargins :
  YMHamiltonianDominationCaseMargins
goodPSDDominatedCaseMargins =
  record
    { dominationMarginText =
        "domination_margin >= 0; PSD surplus is observed on the finite quotient"
    ; hMinEigenvalueText =
        "h_min_eigenvalue is above the near_zero_floor"
    ; deltaMinEigenvalueText =
        "delta_min_eigenvalue is the positive finite quotient defect scale"
    ; holMinEigenvalueText =
        "hol_min_eigenvalue is above holonomy_floor"
    ; comparisonMinEigenvalueText =
        "comparison_min_eigenvalue is recorded for c1*Delta+c2*Hol-E"
    ; quotientCommutatorErrorText =
        "quotient_commutator_error <= tolerance"
    ; maxSymmetryErrorText =
        "max_symmetry_error <= tolerance"
    ; hMinusComparisonMinText =
        "h_min_minus_comparison_min is recorded as an eigenvalue margin proxy"
    }

badWeakHCaseMargins :
  YMHamiltonianDominationCaseMargins
badWeakHCaseMargins =
  record
    { dominationMarginText =
        "domination_margin < 0 after weakening one Hamiltonian quotient direction"
    ; hMinEigenvalueText =
        "h_min_eigenvalue remains recorded but does not rescue failed domination"
    ; deltaMinEigenvalueText =
        "delta_min_eigenvalue remains the same positive finite quotient defect scale"
    ; holMinEigenvalueText =
        "hol_min_eigenvalue remains above holonomy_floor"
    ; comparisonMinEigenvalueText =
        "comparison_min_eigenvalue remains the finite comparison scale"
    ; quotientCommutatorErrorText =
        "quotient_commutator_error <= tolerance"
    ; maxSymmetryErrorText =
        "max_symmetry_error <= tolerance"
    ; hMinusComparisonMinText =
        "h_min_minus_comparison_min is recorded while domination_psd_margin fails"
    }

badNonHolonomyControlledNearZeroCaseMargins :
  YMHamiltonianDominationCaseMargins
badNonHolonomyControlledNearZeroCaseMargins =
  record
    { dominationMarginText =
        "domination_margin < 0 in the near-zero Hamiltonian sector"
    ; hMinEigenvalueText =
        "h_min_eigenvalue < near_zero_floor"
    ; deltaMinEigenvalueText =
        "delta_min_eigenvalue remains the positive finite quotient defect scale"
    ; holMinEigenvalueText =
        "hol_min_eigenvalue < holonomy_floor"
    ; comparisonMinEigenvalueText =
        "comparison_min_eigenvalue records the weak-holonomy comparison scale"
    ; quotientCommutatorErrorText =
        "quotient_commutator_error <= tolerance"
    ; maxSymmetryErrorText =
        "max_symmetry_error <= tolerance"
    ; hMinusComparisonMinText =
        "h_min_minus_comparison_min is recorded while holonomy control fails"
    }

------------------------------------------------------------------------
-- Case-level receipts.

record YMHamiltonianDominationProxyCaseReceipt : Set where
  field
    case :
      YMHamiltonianDominationProxyCase

    name :
      String

    description :
      String

    expectedPassedProxyChecks :
      Bool

    passedProxyChecks :
      Bool

    passedProxyChecksIsExpected :
      passedProxyChecks ≡ expectedPassedProxyChecks

    dimension :
      Nat

    dimensionIsDefault :
      dimension ≡ 5

    quotientDimension :
      Nat

    quotientDimensionIsDefault :
      quotientDimension ≡ 3

    checkReceipts :
      List YMHamiltonianDominationProxyCheckReceipt

    checkReceiptCountIs4 :
      listCount checkReceipts ≡ 4

    margins :
      YMHamiltonianDominationCaseMargins

    holonomyControlled :
      Bool

    nearZeroHSector :
      Bool

    promotionForCase :
      Bool

    promotionForCaseIsFalse :
      promotionForCase ≡ false

    failureSummary :
      String

    interpretation :
      String

open YMHamiltonianDominationProxyCaseReceipt public

goodPSDDominatedFiniteQuotientCaseReceipt :
  YMHamiltonianDominationProxyCaseReceipt
goodPSDDominatedFiniteQuotientCaseReceipt =
  record
    { case =
        goodPSDDominatedFiniteQuotientCase
    ; name =
        caseName goodPSDDominatedFiniteQuotientCase
    ; description =
        caseDescription goodPSDDominatedFiniteQuotientCase
    ; expectedPassedProxyChecks =
        expectedCasePass goodPSDDominatedFiniteQuotientCase
    ; passedProxyChecks =
        true
    ; passedProxyChecksIsExpected =
        refl
    ; dimension =
        5
    ; dimensionIsDefault =
        refl
    ; quotientDimension =
        3
    ; quotientDimensionIsDefault =
        refl
    ; checkReceipts =
        goodPSDDominatedCheckReceipts
    ; checkReceiptCountIs4 =
        goodPSDDominatedCheckReceiptCountIs4
    ; margins =
        goodPSDDominatedCaseMargins
    ; holonomyControlled =
        true
    ; nearZeroHSector =
        false
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "no proxy failure: symmetric forms, quotient stability, PSD domination margin, and holonomy/near-zero control all pass"
    ; interpretation =
        "good finite quotient diagnostic case only; PSD domination margin is observed in the finite matrix proxy"
    }

badWeakHCaseReceipt :
  YMHamiltonianDominationProxyCaseReceipt
badWeakHCaseReceipt =
  record
    { case =
        badWeakHCase
    ; name =
        caseName badWeakHCase
    ; description =
        caseDescription badWeakHCase
    ; expectedPassedProxyChecks =
        expectedCasePass badWeakHCase
    ; passedProxyChecks =
        false
    ; passedProxyChecksIsExpected =
        refl
    ; dimension =
        5
    ; dimensionIsDefault =
        refl
    ; quotientDimension =
        3
    ; quotientDimensionIsDefault =
        refl
    ; checkReceipts =
        badWeakHCheckReceipts
    ; checkReceiptCountIs4 =
        badWeakHCheckReceiptCountIs4
    ; margins =
        badWeakHCaseMargins
    ; holonomyControlled =
        true
    ; nearZeroHSector =
        false
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "detected domination_psd_margin failure from negative eigenvalue of H - comparison"
    ; interpretation =
        "weak-H finite proxy cannot certify Hamiltonian domination"
    }

badNonHolonomyControlledNearZeroSectorCaseReceipt :
  YMHamiltonianDominationProxyCaseReceipt
badNonHolonomyControlledNearZeroSectorCaseReceipt =
  record
    { case =
        badNonHolonomyControlledNearZeroSectorCase
    ; name =
        caseName badNonHolonomyControlledNearZeroSectorCase
    ; description =
        caseDescription badNonHolonomyControlledNearZeroSectorCase
    ; expectedPassedProxyChecks =
        expectedCasePass badNonHolonomyControlledNearZeroSectorCase
    ; passedProxyChecks =
        false
    ; passedProxyChecksIsExpected =
        refl
    ; dimension =
        5
    ; dimensionIsDefault =
        refl
    ; quotientDimension =
        3
    ; quotientDimensionIsDefault =
        refl
    ; checkReceipts =
        badNonHolonomyControlledNearZeroCheckReceipts
    ; checkReceiptCountIs4 =
        badNonHolonomyControlledNearZeroCheckReceiptCountIs4
    ; margins =
        badNonHolonomyControlledNearZeroCaseMargins
    ; holonomyControlled =
        false
    ; nearZeroHSector =
        true
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "detected domination_psd_margin and holonomy_controlled_or_no_near_zero_h_sector failures"
    ; interpretation =
        "near-zero Hamiltonian sector without holonomy control fails closed"
    }

canonicalYMHamiltonianDominationProxyCaseReceipts :
  List YMHamiltonianDominationProxyCaseReceipt
canonicalYMHamiltonianDominationProxyCaseReceipts =
  goodPSDDominatedFiniteQuotientCaseReceipt
  ∷ badWeakHCaseReceipt
  ∷ badNonHolonomyControlledNearZeroSectorCaseReceipt
  ∷ []

caseReceiptCount : Nat
caseReceiptCount =
  listCount canonicalYMHamiltonianDominationProxyCaseReceipts

caseReceiptCountIs3 :
  caseReceiptCount ≡ 3
caseReceiptCountIs3 =
  refl

goodPSDDominatedFiniteQuotientCasePassed :
  passedProxyChecks goodPSDDominatedFiniteQuotientCaseReceipt ≡ true
goodPSDDominatedFiniteQuotientCasePassed =
  refl

badWeakHCaseFailed :
  passedProxyChecks badWeakHCaseReceipt ≡ false
badWeakHCaseFailed =
  refl

badNonHolonomyControlledNearZeroSectorCaseFailed :
  passedProxyChecks
    badNonHolonomyControlledNearZeroSectorCaseReceipt
  ≡
  false
badNonHolonomyControlledNearZeroSectorCaseFailed =
  refl

badNearZeroSectorRecordsFailedHolonomyControl :
  holonomyControlled
    badNonHolonomyControlledNearZeroSectorCaseReceipt
  ≡
  false
badNearZeroSectorRecordsFailedHolonomyControl =
  refl

badNearZeroSectorRecordsNearZeroH :
  nearZeroHSector
    badNonHolonomyControlledNearZeroSectorCaseReceipt
  ≡
  true
badNearZeroSectorRecordsNearZeroH =
  refl

------------------------------------------------------------------------
-- Summary observations and non-claim boundaries.

data YMHamiltonianDominationProxySummaryObservation : Set where
  goodPSDDominatedFiniteQuotientCasePassesObserved :
    YMHamiltonianDominationProxySummaryObservation
  badWeakHCaseFailsObserved :
    YMHamiltonianDominationProxySummaryObservation
  badNonHolonomyControlledNearZeroSectorFailsObserved :
    YMHamiltonianDominationProxySummaryObservation
  marginFieldsRecordedObserved :
    YMHamiltonianDominationProxySummaryObservation
  allExpectedOutcomesObserved :
    YMHamiltonianDominationProxySummaryObservation
  theoremAndPromotionFlagsFalseObserved :
    YMHamiltonianDominationProxySummaryObservation

canonicalYMHamiltonianDominationProxySummaryObservations :
  List YMHamiltonianDominationProxySummaryObservation
canonicalYMHamiltonianDominationProxySummaryObservations =
  goodPSDDominatedFiniteQuotientCasePassesObserved
  ∷ badWeakHCaseFailsObserved
  ∷ badNonHolonomyControlledNearZeroSectorFailsObserved
  ∷ marginFieldsRecordedObserved
  ∷ allExpectedOutcomesObserved
  ∷ theoremAndPromotionFlagsFalseObserved
  ∷ []

summaryObservationCount : Nat
summaryObservationCount =
  listCount canonicalYMHamiltonianDominationProxySummaryObservations

summaryObservationCountIs6 :
  summaryObservationCount ≡ 6
summaryObservationCountIs6 =
  refl

data YMHamiltonianDominationProxyNonClaimBoundary : Set where
  diagnosticOnlyNotHamiltonianDominationTheorem :
    YMHamiltonianDominationProxyNonClaimBoundary
  noFiniteGaugeQuotientCarrierConstruction :
    YMHamiltonianDominationProxyNonClaimBoundary
  noTransferMatrixPhysicalHamiltonianIdentification :
    YMHamiltonianDominationProxyNonClaimBoundary
  noOSReflectionPositivityTransfer :
    YMHamiltonianDominationProxyNonClaimBoundary
  noContinuumTransfer :
    YMHamiltonianDominationProxyNonClaimBoundary
  noYMClayOrTerminalPromotion :
    YMHamiltonianDominationProxyNonClaimBoundary

canonicalYMHamiltonianDominationProxyNonClaimBoundaries :
  List YMHamiltonianDominationProxyNonClaimBoundary
canonicalYMHamiltonianDominationProxyNonClaimBoundaries =
  diagnosticOnlyNotHamiltonianDominationTheorem
  ∷ noFiniteGaugeQuotientCarrierConstruction
  ∷ noTransferMatrixPhysicalHamiltonianIdentification
  ∷ noOSReflectionPositivityTransfer
  ∷ noContinuumTransfer
  ∷ noYMClayOrTerminalPromotion
  ∷ []

nonClaimBoundaryCount : Nat
nonClaimBoundaryCount =
  listCount canonicalYMHamiltonianDominationProxyNonClaimBoundaries

nonClaimBoundaryCountIs6 :
  nonClaimBoundaryCount ≡ 6
nonClaimBoundaryCountIs6 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record YMHamiltonianDominationProxyHarnessResult : Setω where
  field
    sourceHarness :
      String

    jsonReceipt :
      String

    scope :
      String

    runCommand :
      String

    defaultParameters :
      String

    importedSupport :
      ImportedHamiltonianDominationBoundarySupport

    fields :
      List YMHamiltonianDominationProxyHarnessField

    fieldsAreCanonical :
      fields ≡ canonicalYMHamiltonianDominationProxyHarnessFields

    fieldCount :
      Nat

    fieldCountIs10 :
      fieldCount ≡ 10

    checks :
      List YMHamiltonianDominationProxyCheck

    checksAreCanonical :
      checks ≡ canonicalYMHamiltonianDominationProxyChecks

    checkCount :
      Nat

    checkCountIs4 :
      checkCount ≡ 4

    marginFields :
      List YMHamiltonianDominationMarginField

    marginFieldsAreCanonical :
      marginFields ≡ canonicalYMHamiltonianDominationMarginFields

    marginFieldCountField :
      Nat

    marginFieldCountFieldIs8 :
      marginFieldCountField ≡ 8

    cases :
      List YMHamiltonianDominationProxyCaseReceipt

    casesAreCanonical :
      cases ≡ canonicalYMHamiltonianDominationProxyCaseReceipts

    caseCount :
      Nat

    caseCountIs3 :
      caseCount ≡ 3

    observations :
      List YMHamiltonianDominationProxySummaryObservation

    observationsAreCanonical :
      observations ≡ canonicalYMHamiltonianDominationProxySummaryObservations

    observationCount :
      Nat

    observationCountIs6 :
      observationCount ≡ 6

    nonClaimBoundaries :
      List YMHamiltonianDominationProxyNonClaimBoundary

    nonClaimBoundariesAreCanonical :
      nonClaimBoundaries ≡ canonicalYMHamiltonianDominationProxyNonClaimBoundaries

    nonClaimBoundaryCountField :
      Nat

    nonClaimBoundaryCountFieldIs6 :
      nonClaimBoundaryCountField ≡ 6

    okObservedField :
      Bool

    okObservedFieldIsTrue :
      okObservedField ≡ true

    promotionField :
      Bool

    promotionFieldIsFalse :
      promotionField ≡ false

    hamiltonianDominationTheoremProvedField :
      Bool

    hamiltonianDominationTheoremProvedFieldIsFalse :
      hamiltonianDominationTheoremProvedField ≡ false

    osTransferUnlockedField :
      Bool

    osTransferUnlockedFieldIsFalse :
      osTransferUnlockedField ≡ false

    continuumTransferUnlockedField :
      Bool

    continuumTransferUnlockedFieldIsFalse :
      continuumTransferUnlockedField ≡ false

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

    boundary :
      List String

    noPromotionEliminator :
      promotionField ≡ true → ⊥

open YMHamiltonianDominationProxyHarnessResult public

canonicalYMHamiltonianDominationProxyHarnessResult :
  YMHamiltonianDominationProxyHarnessResult
canonicalYMHamiltonianDominationProxyHarnessResult =
  record
    { sourceHarness =
        sourceHarnessPath
    ; jsonReceipt =
        defaultJsonReceiptPath
    ; scope =
        receiptScope
    ; runCommand =
        runCommandText
    ; defaultParameters =
        defaultParameterText
    ; importedSupport =
        canonicalImportedHamiltonianDominationBoundarySupport
    ; fields =
        canonicalYMHamiltonianDominationProxyHarnessFields
    ; fieldsAreCanonical =
        refl
    ; fieldCount =
        harnessFieldCount
    ; fieldCountIs10 =
        harnessFieldCountIs10
    ; checks =
        canonicalYMHamiltonianDominationProxyChecks
    ; checksAreCanonical =
        refl
    ; checkCount =
        proxyCheckCount
    ; checkCountIs4 =
        proxyCheckCountIs4
    ; marginFields =
        canonicalYMHamiltonianDominationMarginFields
    ; marginFieldsAreCanonical =
        refl
    ; marginFieldCountField =
        marginFieldCount
    ; marginFieldCountFieldIs8 =
        marginFieldCountIs8
    ; cases =
        canonicalYMHamiltonianDominationProxyCaseReceipts
    ; casesAreCanonical =
        refl
    ; caseCount =
        caseReceiptCount
    ; caseCountIs3 =
        caseReceiptCountIs3
    ; observations =
        canonicalYMHamiltonianDominationProxySummaryObservations
    ; observationsAreCanonical =
        refl
    ; observationCount =
        summaryObservationCount
    ; observationCountIs6 =
        summaryObservationCountIs6
    ; nonClaimBoundaries =
        canonicalYMHamiltonianDominationProxyNonClaimBoundaries
    ; nonClaimBoundariesAreCanonical =
        refl
    ; nonClaimBoundaryCountField =
        nonClaimBoundaryCount
    ; nonClaimBoundaryCountFieldIs6 =
        nonClaimBoundaryCountIs6
    ; okObservedField =
        ok_observed
    ; okObservedFieldIsTrue =
        ok_observed_is_true
    ; promotionField =
        promotion
    ; promotionFieldIsFalse =
        promotion_is_false
    ; hamiltonianDominationTheoremProvedField =
        hamiltonianDominationTheoremProved
    ; hamiltonianDominationTheoremProvedFieldIsFalse =
        hamiltonianDominationTheoremProvedIsFalse
    ; osTransferUnlockedField =
        osTransferUnlocked
    ; osTransferUnlockedFieldIsFalse =
        osTransferUnlockedIsFalse
    ; continuumTransferUnlockedField =
        continuumTransferUnlocked
    ; continuumTransferUnlockedFieldIsFalse =
        continuumTransferUnlockedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; theoremFlagSummary =
        "promotion=false; Hamiltonian domination theorem, OS transfer, continuum transfer, YM Clay, and terminal promotion are all false"
    ; boundary =
        "Finite matrix PSD domination proxy is recorded only"
        ∷ "Good case: good_psd_dominated passes expected checks"
        ∷ "Bad case: bad_weak_h fails the PSD domination margin"
        ∷ "Bad case: bad_non_holonomy_controlled_near_zero fails domination and holonomy/near-zero control"
        ∷ "Margin fields are diagnostic strings, not analytic estimates"
        ∷ "No Hamiltonian domination theorem, OS transfer, continuum transfer, YM Clay, or terminal promotion follows"
        ∷ []
    ; noPromotionEliminator =
        λ ()
    }

canonicalHamiltonianDominationProxyPromotionFalse :
  promotionField canonicalYMHamiltonianDominationProxyHarnessResult ≡ false
canonicalHamiltonianDominationProxyPromotionFalse =
  refl

canonicalHamiltonianDominationProxyTheoremFalse :
  hamiltonianDominationTheoremProvedField
    canonicalYMHamiltonianDominationProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationProxyTheoremFalse =
  refl

canonicalHamiltonianDominationProxyOSFalse :
  osTransferUnlockedField
    canonicalYMHamiltonianDominationProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationProxyOSFalse =
  refl

canonicalHamiltonianDominationProxyContinuumFalse :
  continuumTransferUnlockedField
    canonicalYMHamiltonianDominationProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationProxyContinuumFalse =
  refl

canonicalHamiltonianDominationProxyClayFalse :
  ymClayPromotedField
    canonicalYMHamiltonianDominationProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationProxyClayFalse =
  refl

canonicalHamiltonianDominationProxyTerminalFalse :
  terminalPromotionField
    canonicalYMHamiltonianDominationProxyHarnessResult
  ≡
  false
canonicalHamiltonianDominationProxyTerminalFalse =
  refl
