module DASHI.Physics.Closure.YMFiniteSelfAdjointHamiltonianProxyHarnessResult where

-- Fail-closed receipt for:
--
--   scripts/ym_finite_selfadjoint_hamiltonian_proxy_harness.py
--
-- The harness is a finite diagnostic for the boundary recorded in:
--
--   YMSelfAdjointFiniteHamiltonianBoundary
--
-- It checks one symmetric quotient-stable finite matrix proxy, one
-- nonsymmetric counterexample, and one symmetric but quotient/domain-unstable
-- counterexample.  The good case records a finite eigenvalue/discrete-spectrum
-- proxy only.
--
-- This module records that diagnostic result only.  It does not construct the
-- true finite Yang-Mills Hamiltonian domain, prove gauge quotient descent,
-- prove finite self-adjointness, unlock Hamiltonian domination, prove OS or
-- continuum transfer, or promote Clay Yang-Mills.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
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
  "scripts/ym_finite_selfadjoint_hamiltonian_proxy_harness.py"

defaultJsonReceiptPath : String
defaultJsonReceiptPath =
  "outputs/ym_finite_selfadjoint_hamiltonian_proxy_harness.json"

receiptScope : String
receiptScope =
  "finite_self_adjoint_hamiltonian_proxy_diagnostic_only"

runCommandText : String
runCommandText =
  "python scripts/ym_finite_selfadjoint_hamiltonian_proxy_harness.py --json-output outputs/ym_finite_selfadjoint_hamiltonian_proxy_harness.json --json"

defaultParameterText : String
defaultParameterText =
  "dimension=6, quotient_dimension=4, tolerance=1e-9, jacobi_sweeps=80"

claimScopeText : String
claimScopeText =
  "finite diagnostic proxy only"

------------------------------------------------------------------------
-- Imported finite self-adjointness boundary support.

boundaryReference : String
boundaryReference =
  "DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary"

boundaryImported : Bool
boundaryImported =
  true

record ImportedFiniteSelfAdjointBoundarySupport : Setω where
  field
    finiteSelfAdjointBoundary :
      Boundary.YMSelfAdjointFiniteHamiltonianBoundary

    boundaryImportedIsTrue :
      boundaryImported ≡ true

    importedFiniteSelfAdjointTheoremStillFalse :
      Boundary.selfAdjointFiniteHamiltonianProvedField
        finiteSelfAdjointBoundary
      ≡ false

    importedHamiltonianDominationStillFalse :
      Boundary.hamiltonianDominationUnlockedField
        finiteSelfAdjointBoundary
      ≡ false

    importedOSTransferStillFalse :
      Boundary.osContinuumTransferUnlockedField
        finiteSelfAdjointBoundary
      ≡ false

    importedYMClayStillFalse :
      Boundary.clayYangMillsPromotedField
        finiteSelfAdjointBoundary
      ≡ false

    importedTerminalPromotionStillFalse :
      Boundary.terminalPromotionField
        finiteSelfAdjointBoundary
      ≡ false

canonicalImportedFiniteSelfAdjointBoundarySupport :
  ImportedFiniteSelfAdjointBoundarySupport
canonicalImportedFiniteSelfAdjointBoundarySupport =
  record
    { finiteSelfAdjointBoundary =
        Boundary.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; boundaryImportedIsTrue =
        refl
    ; importedFiniteSelfAdjointTheoremStillFalse =
        Boundary.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; importedHamiltonianDominationStillFalse =
        Boundary.canonicalHamiltonianDominationUnlockedFalse
    ; importedOSTransferStillFalse =
        Boundary.canonicalOSContinuumTransferUnlockedFalse
    ; importedYMClayStillFalse =
        Boundary.canonicalClayYangMillsPromotedFalse
    ; importedTerminalPromotionStillFalse =
        Boundary.canonicalTerminalPromotionFalse
    }

------------------------------------------------------------------------
-- Top-level harness fields.

data YMHamiltonianProxyHarnessField : Set where
  harnessIdentityField :
    YMHamiltonianProxyHarnessField
  parametersField :
    YMHamiltonianProxyHarnessField
  importedBoundaryField :
    YMHamiltonianProxyHarnessField
  casesField :
    YMHamiltonianProxyHarnessField
  checksField :
    YMHamiltonianProxyHarnessField
  eigenvalueProxyField :
    YMHamiltonianProxyHarnessField
  theoremFlagsField :
    YMHamiltonianProxyHarnessField
  nonClaimBoundaryField :
    YMHamiltonianProxyHarnessField
  summaryField :
    YMHamiltonianProxyHarnessField

canonicalYMHamiltonianProxyHarnessFields :
  List YMHamiltonianProxyHarnessField
canonicalYMHamiltonianProxyHarnessFields =
  harnessIdentityField
  ∷ parametersField
  ∷ importedBoundaryField
  ∷ casesField
  ∷ checksField
  ∷ eigenvalueProxyField
  ∷ theoremFlagsField
  ∷ nonClaimBoundaryField
  ∷ summaryField
  ∷ []

harnessFieldCount : Nat
harnessFieldCount =
  listCount canonicalYMHamiltonianProxyHarnessFields

harnessFieldCountIs9 :
  harnessFieldCount ≡ 9
harnessFieldCountIs9 =
  refl

ok_observed : Bool
ok_observed =
  true

promotion : Bool
promotion =
  false

finiteSelfAdjointTheoremProved : Bool
finiteSelfAdjointTheoremProved =
  false

hamiltonianDominationUnlocked : Bool
hamiltonianDominationUnlocked =
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

finiteSelfAdjointTheoremProvedIsFalse :
  finiteSelfAdjointTheoremProved ≡ false
finiteSelfAdjointTheoremProvedIsFalse =
  refl

hamiltonianDominationUnlockedIsFalse :
  hamiltonianDominationUnlocked ≡ false
hamiltonianDominationUnlockedIsFalse =
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
-- Proxy cases and expected check outcomes.

data YMHamiltonianProxyCase : Set where
  symmetricQuotientStableCase :
    YMHamiltonianProxyCase
  badNonsymmetricCase :
    YMHamiltonianProxyCase
  badDomainUnstableCase :
    YMHamiltonianProxyCase

caseName : YMHamiltonianProxyCase → String
caseName symmetricQuotientStableCase =
  "symmetric_quotient_stable"
caseName badNonsymmetricCase =
  "bad_nonsymmetric"
caseName badDomainUnstableCase =
  "bad_domain_unstable"

caseDescription : YMHamiltonianProxyCase → String
caseDescription symmetricQuotientStableCase =
  "Symmetric block-preserving finite Hamiltonian proxy; expected to descend to the quotient."
caseDescription badNonsymmetricCase =
  "Domain-stable matrix with an asymmetric quotient block; expected to fail finite-form self-adjointness."
caseDescription badDomainUnstableCase =
  "Symmetric full matrix with off-block coupling; expected to fail quotient/domain stability because [H,P] is nonzero."

expectedCasePass : YMHamiltonianProxyCase → Bool
expectedCasePass symmetricQuotientStableCase =
  true
expectedCasePass badNonsymmetricCase =
  false
expectedCasePass badDomainUnstableCase =
  false

data YMHamiltonianProxyCheck : Set where
  orthogonalProjectorCheck :
    YMHamiltonianProxyCheck
  finiteFormSymmetricCheck :
    YMHamiltonianProxyCheck
  quotientDomainStableCheck :
    YMHamiltonianProxyCheck
  quotientMatrixSymmetricCheck :
    YMHamiltonianProxyCheck
  finiteDiscreteSpectrumProxyCheck :
    YMHamiltonianProxyCheck

checkName : YMHamiltonianProxyCheck → String
checkName orthogonalProjectorCheck =
  "orthogonal_projector"
checkName finiteFormSymmetricCheck =
  "finite_form_symmetric"
checkName quotientDomainStableCheck =
  "quotient_domain_stable"
checkName quotientMatrixSymmetricCheck =
  "quotient_matrix_symmetric"
checkName finiteDiscreteSpectrumProxyCheck =
  "finite_discrete_spectrum_proxy"

canonicalYMHamiltonianProxyChecks :
  List YMHamiltonianProxyCheck
canonicalYMHamiltonianProxyChecks =
  orthogonalProjectorCheck
  ∷ finiteFormSymmetricCheck
  ∷ quotientDomainStableCheck
  ∷ quotientMatrixSymmetricCheck
  ∷ finiteDiscreteSpectrumProxyCheck
  ∷ []

proxyCheckCount : Nat
proxyCheckCount =
  listCount canonicalYMHamiltonianProxyChecks

proxyCheckCountIs5 :
  proxyCheckCount ≡ 5
proxyCheckCountIs5 =
  refl

expectedCheckOutcome :
  YMHamiltonianProxyCase →
  YMHamiltonianProxyCheck →
  Bool
expectedCheckOutcome symmetricQuotientStableCase orthogonalProjectorCheck =
  true
expectedCheckOutcome symmetricQuotientStableCase finiteFormSymmetricCheck =
  true
expectedCheckOutcome symmetricQuotientStableCase quotientDomainStableCheck =
  true
expectedCheckOutcome symmetricQuotientStableCase quotientMatrixSymmetricCheck =
  true
expectedCheckOutcome symmetricQuotientStableCase finiteDiscreteSpectrumProxyCheck =
  true
expectedCheckOutcome badNonsymmetricCase orthogonalProjectorCheck =
  true
expectedCheckOutcome badNonsymmetricCase finiteFormSymmetricCheck =
  false
expectedCheckOutcome badNonsymmetricCase quotientDomainStableCheck =
  true
expectedCheckOutcome badNonsymmetricCase quotientMatrixSymmetricCheck =
  false
expectedCheckOutcome badNonsymmetricCase finiteDiscreteSpectrumProxyCheck =
  false
expectedCheckOutcome badDomainUnstableCase orthogonalProjectorCheck =
  true
expectedCheckOutcome badDomainUnstableCase finiteFormSymmetricCheck =
  true
expectedCheckOutcome badDomainUnstableCase quotientDomainStableCheck =
  false
expectedCheckOutcome badDomainUnstableCase quotientMatrixSymmetricCheck =
  true
expectedCheckOutcome badDomainUnstableCase finiteDiscreteSpectrumProxyCheck =
  false

record YMHamiltonianProxyCheckReceipt : Set where
  field
    case :
      YMHamiltonianProxyCase

    check :
      YMHamiltonianProxyCheck

    observedOutcome :
      Bool

    observedOutcomeIsExpected :
      observedOutcome ≡ expectedCheckOutcome case check

    checkLabel :
      String

open YMHamiltonianProxyCheckReceipt public

mkYMHamiltonianProxyCheckReceipt :
  (case : YMHamiltonianProxyCase) →
  (check : YMHamiltonianProxyCheck) →
  YMHamiltonianProxyCheckReceipt
mkYMHamiltonianProxyCheckReceipt case check =
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

symmetricQuotientStableCheckReceipts :
  List YMHamiltonianProxyCheckReceipt
symmetricQuotientStableCheckReceipts =
  mkYMHamiltonianProxyCheckReceipt
    symmetricQuotientStableCase
    orthogonalProjectorCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    symmetricQuotientStableCase
    finiteFormSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    symmetricQuotientStableCase
    quotientDomainStableCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    symmetricQuotientStableCase
    quotientMatrixSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    symmetricQuotientStableCase
    finiteDiscreteSpectrumProxyCheck
  ∷ []

badNonsymmetricCheckReceipts :
  List YMHamiltonianProxyCheckReceipt
badNonsymmetricCheckReceipts =
  mkYMHamiltonianProxyCheckReceipt
    badNonsymmetricCase
    orthogonalProjectorCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badNonsymmetricCase
    finiteFormSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badNonsymmetricCase
    quotientDomainStableCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badNonsymmetricCase
    quotientMatrixSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badNonsymmetricCase
    finiteDiscreteSpectrumProxyCheck
  ∷ []

badDomainUnstableCheckReceipts :
  List YMHamiltonianProxyCheckReceipt
badDomainUnstableCheckReceipts =
  mkYMHamiltonianProxyCheckReceipt
    badDomainUnstableCase
    orthogonalProjectorCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badDomainUnstableCase
    finiteFormSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badDomainUnstableCase
    quotientDomainStableCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badDomainUnstableCase
    quotientMatrixSymmetricCheck
  ∷ mkYMHamiltonianProxyCheckReceipt
    badDomainUnstableCase
    finiteDiscreteSpectrumProxyCheck
  ∷ []

symmetricQuotientStableCheckReceiptCountIs5 :
  listCount symmetricQuotientStableCheckReceipts ≡ 5
symmetricQuotientStableCheckReceiptCountIs5 =
  refl

badNonsymmetricCheckReceiptCountIs5 :
  listCount badNonsymmetricCheckReceipts ≡ 5
badNonsymmetricCheckReceiptCountIs5 =
  refl

badDomainUnstableCheckReceiptCountIs5 :
  listCount badDomainUnstableCheckReceipts ≡ 5
badDomainUnstableCheckReceiptCountIs5 =
  refl

------------------------------------------------------------------------
-- Case-level receipts.

record YMHamiltonianProxyCaseReceipt : Set where
  field
    case :
      YMHamiltonianProxyCase

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

    checkReceipts :
      List YMHamiltonianProxyCheckReceipt

    checkReceiptCountIs5 :
      listCount checkReceipts ≡ 5

    eigenvalueCount :
      Nat

    eigenvalueCountIsQuotientDimensionWhenGood :
      String

    finiteEigenvalueDiscreteSpectrumProxyObserved :
      Bool

    finiteEigenvalueDiscreteSpectrumProxyObservedIsExpected :
      finiteEigenvalueDiscreteSpectrumProxyObserved
      ≡
      expectedCheckOutcome case finiteDiscreteSpectrumProxyCheck

    promotionForCase :
      Bool

    promotionForCaseIsFalse :
      promotionForCase ≡ false

    failureSummary :
      String

    interpretation :
      String

open YMHamiltonianProxyCaseReceipt public

symmetricQuotientStableCaseReceipt :
  YMHamiltonianProxyCaseReceipt
symmetricQuotientStableCaseReceipt =
  record
    { case =
        symmetricQuotientStableCase
    ; name =
        caseName symmetricQuotientStableCase
    ; description =
        caseDescription symmetricQuotientStableCase
    ; expectedPassedProxyChecks =
        expectedCasePass symmetricQuotientStableCase
    ; passedProxyChecks =
        true
    ; passedProxyChecksIsExpected =
        refl
    ; checkReceipts =
        symmetricQuotientStableCheckReceipts
    ; checkReceiptCountIs5 =
        symmetricQuotientStableCheckReceiptCountIs5
    ; eigenvalueCount =
        4
    ; eigenvalueCountIsQuotientDimensionWhenGood =
        "eigenvalue_count=quotient_dimension=4 for the symmetric quotient-stable finite matrix proxy"
    ; finiteEigenvalueDiscreteSpectrumProxyObserved =
        true
    ; finiteEigenvalueDiscreteSpectrumProxyObservedIsExpected =
        refl
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "no proxy failure: orthogonal projector, finite-form symmetry, quotient-domain stability, quotient matrix symmetry, and finite discrete spectrum proxy all pass"
    ; interpretation =
        "good finite diagnostic case only; symmetry and quotient stability make the finite eigenvalue proxy available"
    }

badNonsymmetricCaseReceipt :
  YMHamiltonianProxyCaseReceipt
badNonsymmetricCaseReceipt =
  record
    { case =
        badNonsymmetricCase
    ; name =
        caseName badNonsymmetricCase
    ; description =
        caseDescription badNonsymmetricCase
    ; expectedPassedProxyChecks =
        expectedCasePass badNonsymmetricCase
    ; passedProxyChecks =
        false
    ; passedProxyChecksIsExpected =
        refl
    ; checkReceipts =
        badNonsymmetricCheckReceipts
    ; checkReceiptCountIs5 =
        badNonsymmetricCheckReceiptCountIs5
    ; eigenvalueCount =
        0
    ; eigenvalueCountIsQuotientDimensionWhenGood =
        "eigenvalues suppressed because the quotient block is not symmetric"
    ; finiteEigenvalueDiscreteSpectrumProxyObserved =
        false
    ; finiteEigenvalueDiscreteSpectrumProxyObservedIsExpected =
        refl
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "detected finite_form_symmetric and quotient_matrix_symmetric failures; finite_discrete_spectrum_proxy fails closed"
    ; interpretation =
        "nonsymmetric finite operator proxy cannot certify self-adjointness"
    }

badDomainUnstableCaseReceipt :
  YMHamiltonianProxyCaseReceipt
badDomainUnstableCaseReceipt =
  record
    { case =
        badDomainUnstableCase
    ; name =
        caseName badDomainUnstableCase
    ; description =
        caseDescription badDomainUnstableCase
    ; expectedPassedProxyChecks =
        expectedCasePass badDomainUnstableCase
    ; passedProxyChecks =
        false
    ; passedProxyChecksIsExpected =
        refl
    ; checkReceipts =
        badDomainUnstableCheckReceipts
    ; checkReceiptCountIs5 =
        badDomainUnstableCheckReceiptCountIs5
    ; eigenvalueCount =
        4
    ; eigenvalueCountIsQuotientDimensionWhenGood =
        "quotient block eigenvalues exist but do not rescue failed quotient-domain stability"
    ; finiteEigenvalueDiscreteSpectrumProxyObserved =
        false
    ; finiteEigenvalueDiscreteSpectrumProxyObservedIsExpected =
        refl
    ; promotionForCase =
        false
    ; promotionForCaseIsFalse =
        refl
    ; failureSummary =
        "detected quotient_domain_stable failure from nonzero [H,P]; finite_discrete_spectrum_proxy fails closed"
    ; interpretation =
        "symmetric full matrix is insufficient when it does not preserve the quotient/domain"
    }

canonicalYMHamiltonianProxyCaseReceipts :
  List YMHamiltonianProxyCaseReceipt
canonicalYMHamiltonianProxyCaseReceipts =
  symmetricQuotientStableCaseReceipt
  ∷ badNonsymmetricCaseReceipt
  ∷ badDomainUnstableCaseReceipt
  ∷ []

caseReceiptCount : Nat
caseReceiptCount =
  listCount canonicalYMHamiltonianProxyCaseReceipts

caseReceiptCountIs3 :
  caseReceiptCount ≡ 3
caseReceiptCountIs3 =
  refl

goodSymmetricQuotientStableCasePassed :
  passedProxyChecks symmetricQuotientStableCaseReceipt ≡ true
goodSymmetricQuotientStableCasePassed =
  refl

badNonsymmetricCaseFailed :
  passedProxyChecks badNonsymmetricCaseReceipt ≡ false
badNonsymmetricCaseFailed =
  refl

badDomainUnstableCaseFailed :
  passedProxyChecks badDomainUnstableCaseReceipt ≡ false
badDomainUnstableCaseFailed =
  refl

goodFiniteEigenvalueProxyObserved :
  finiteEigenvalueDiscreteSpectrumProxyObserved
    symmetricQuotientStableCaseReceipt
  ≡
  true
goodFiniteEigenvalueProxyObserved =
  refl

badNonsymmetricFiniteEigenvalueProxyRejected :
  finiteEigenvalueDiscreteSpectrumProxyObserved
    badNonsymmetricCaseReceipt
  ≡
  false
badNonsymmetricFiniteEigenvalueProxyRejected =
  refl

badDomainUnstableFiniteEigenvalueProxyRejected :
  finiteEigenvalueDiscreteSpectrumProxyObserved
    badDomainUnstableCaseReceipt
  ≡
  false
badDomainUnstableFiniteEigenvalueProxyRejected =
  refl

------------------------------------------------------------------------
-- Summary observations and non-claim boundaries.

data YMHamiltonianProxySummaryObservation : Set where
  goodSymmetricQuotientStableCasePassesObserved :
    YMHamiltonianProxySummaryObservation
  badNonsymmetricCaseFailsObserved :
    YMHamiltonianProxySummaryObservation
  badDomainUnstableCaseFailsObserved :
    YMHamiltonianProxySummaryObservation
  finiteEigenvalueDiscreteSpectrumProxySummaryObserved :
    YMHamiltonianProxySummaryObservation
  allExpectedOutcomesObserved :
    YMHamiltonianProxySummaryObservation
  theoremAndPromotionFlagsFalseObserved :
    YMHamiltonianProxySummaryObservation

canonicalYMHamiltonianProxySummaryObservations :
  List YMHamiltonianProxySummaryObservation
canonicalYMHamiltonianProxySummaryObservations =
  goodSymmetricQuotientStableCasePassesObserved
  ∷ badNonsymmetricCaseFailsObserved
  ∷ badDomainUnstableCaseFailsObserved
  ∷ finiteEigenvalueDiscreteSpectrumProxySummaryObserved
  ∷ allExpectedOutcomesObserved
  ∷ theoremAndPromotionFlagsFalseObserved
  ∷ []

summaryObservationCount : Nat
summaryObservationCount =
  listCount canonicalYMHamiltonianProxySummaryObservations

summaryObservationCountIs6 :
  summaryObservationCount ≡ 6
summaryObservationCountIs6 =
  refl

data YMHamiltonianProxyNonClaimBoundary : Set where
  diagnosticOnlyNotFiniteDomainConstruction :
    YMHamiltonianProxyNonClaimBoundary
  noGaugeQuotientDescentProof :
    YMHamiltonianProxyNonClaimBoundary
  noFiniteSelfAdjointHamiltonianTheorem :
    YMHamiltonianProxyNonClaimBoundary
  noHamiltonianDominationUnlock :
    YMHamiltonianProxyNonClaimBoundary
  noOSTransferProof :
    YMHamiltonianProxyNonClaimBoundary
  noContinuumTransferProof :
    YMHamiltonianProxyNonClaimBoundary
  noYMClayOrTerminalPromotion :
    YMHamiltonianProxyNonClaimBoundary

canonicalYMHamiltonianProxyNonClaimBoundaries :
  List YMHamiltonianProxyNonClaimBoundary
canonicalYMHamiltonianProxyNonClaimBoundaries =
  diagnosticOnlyNotFiniteDomainConstruction
  ∷ noGaugeQuotientDescentProof
  ∷ noFiniteSelfAdjointHamiltonianTheorem
  ∷ noHamiltonianDominationUnlock
  ∷ noOSTransferProof
  ∷ noContinuumTransferProof
  ∷ noYMClayOrTerminalPromotion
  ∷ []

nonClaimBoundaryCount : Nat
nonClaimBoundaryCount =
  listCount canonicalYMHamiltonianProxyNonClaimBoundaries

nonClaimBoundaryCountIs7 :
  nonClaimBoundaryCount ≡ 7
nonClaimBoundaryCountIs7 =
  refl

------------------------------------------------------------------------
-- Canonical receipt.

record YMFiniteSelfAdjointHamiltonianProxyHarnessResult : Setω where
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
      ImportedFiniteSelfAdjointBoundarySupport

    fields :
      List YMHamiltonianProxyHarnessField

    fieldsAreCanonical :
      fields ≡ canonicalYMHamiltonianProxyHarnessFields

    fieldCount :
      Nat

    fieldCountIs9 :
      fieldCount ≡ 9

    checks :
      List YMHamiltonianProxyCheck

    checksAreCanonical :
      checks ≡ canonicalYMHamiltonianProxyChecks

    checkCount :
      Nat

    checkCountIs5 :
      checkCount ≡ 5

    cases :
      List YMHamiltonianProxyCaseReceipt

    casesAreCanonical :
      cases ≡ canonicalYMHamiltonianProxyCaseReceipts

    caseCount :
      Nat

    caseCountIs3 :
      caseCount ≡ 3

    observations :
      List YMHamiltonianProxySummaryObservation

    observationsAreCanonical :
      observations ≡ canonicalYMHamiltonianProxySummaryObservations

    observationCount :
      Nat

    observationCountIs6 :
      observationCount ≡ 6

    nonClaimBoundaries :
      List YMHamiltonianProxyNonClaimBoundary

    nonClaimBoundariesAreCanonical :
      nonClaimBoundaries ≡ canonicalYMHamiltonianProxyNonClaimBoundaries

    nonClaimBoundaryCountField :
      Nat

    nonClaimBoundaryCountFieldIs7 :
      nonClaimBoundaryCountField ≡ 7

    okObservedField :
      Bool

    okObservedFieldIsTrue :
      okObservedField ≡ true

    promotionField :
      Bool

    promotionFieldIsFalse :
      promotionField ≡ false

    finiteSelfAdjointTheoremProvedField :
      Bool

    finiteSelfAdjointTheoremProvedFieldIsFalse :
      finiteSelfAdjointTheoremProvedField ≡ false

    hamiltonianDominationUnlockedField :
      Bool

    hamiltonianDominationUnlockedFieldIsFalse :
      hamiltonianDominationUnlockedField ≡ false

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

    notes :
      List String

open YMFiniteSelfAdjointHamiltonianProxyHarnessResult public

canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult :
  YMFiniteSelfAdjointHamiltonianProxyHarnessResult
canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult =
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
        canonicalImportedFiniteSelfAdjointBoundarySupport
    ; fields =
        canonicalYMHamiltonianProxyHarnessFields
    ; fieldsAreCanonical =
        refl
    ; fieldCount =
        harnessFieldCount
    ; fieldCountIs9 =
        harnessFieldCountIs9
    ; checks =
        canonicalYMHamiltonianProxyChecks
    ; checksAreCanonical =
        refl
    ; checkCount =
        proxyCheckCount
    ; checkCountIs5 =
        proxyCheckCountIs5
    ; cases =
        canonicalYMHamiltonianProxyCaseReceipts
    ; casesAreCanonical =
        refl
    ; caseCount =
        caseReceiptCount
    ; caseCountIs3 =
        caseReceiptCountIs3
    ; observations =
        canonicalYMHamiltonianProxySummaryObservations
    ; observationsAreCanonical =
        refl
    ; observationCount =
        summaryObservationCount
    ; observationCountIs6 =
        summaryObservationCountIs6
    ; nonClaimBoundaries =
        canonicalYMHamiltonianProxyNonClaimBoundaries
    ; nonClaimBoundariesAreCanonical =
        refl
    ; nonClaimBoundaryCountField =
        nonClaimBoundaryCount
    ; nonClaimBoundaryCountFieldIs7 =
        nonClaimBoundaryCountIs7
    ; okObservedField =
        ok_observed
    ; okObservedFieldIsTrue =
        ok_observed_is_true
    ; promotionField =
        promotion
    ; promotionFieldIsFalse =
        promotion_is_false
    ; finiteSelfAdjointTheoremProvedField =
        finiteSelfAdjointTheoremProved
    ; finiteSelfAdjointTheoremProvedFieldIsFalse =
        finiteSelfAdjointTheoremProvedIsFalse
    ; hamiltonianDominationUnlockedField =
        hamiltonianDominationUnlocked
    ; hamiltonianDominationUnlockedFieldIsFalse =
        hamiltonianDominationUnlockedIsFalse
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
    ; notes =
        "The good symmetric quotient-stable proxy passes and records a finite eigenvalue/discrete-spectrum proxy."
        ∷ "The nonsymmetric counterexample fails finite-form and quotient-matrix symmetry."
        ∷ "The domain-unstable counterexample fails quotient-domain stability even though the full matrix is symmetric."
        ∷ "Finite self-adjoint theorem, Hamiltonian domination, OS transfer, continuum transfer, YM Clay, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas and no-promotion contradictions.

canonicalHarnessFieldCountIs9 :
  fieldCount canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult ≡ 9
canonicalHarnessFieldCountIs9 =
  refl

canonicalHarnessCheckCountIs5 :
  checkCount canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult ≡ 5
canonicalHarnessCheckCountIs5 =
  refl

canonicalHarnessCaseCountIs3 :
  caseCount canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult ≡ 3
canonicalHarnessCaseCountIs3 =
  refl

canonicalHarnessObservationCountIs6 :
  observationCount
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  6
canonicalHarnessObservationCountIs6 =
  refl

canonicalHarnessNonClaimBoundaryCountIs7 :
  nonClaimBoundaryCountField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  7
canonicalHarnessNonClaimBoundaryCountIs7 =
  refl

canonicalHarnessOkObservedTrue :
  okObservedField canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true
canonicalHarnessOkObservedTrue =
  refl

canonicalHarnessPromotionFalse :
  promotionField canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessPromotionFalse =
  refl

canonicalHarnessFiniteSelfAdjointTheoremFalse :
  finiteSelfAdjointTheoremProvedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessFiniteSelfAdjointTheoremFalse =
  refl

canonicalHarnessHamiltonianDominationFalse :
  hamiltonianDominationUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessHamiltonianDominationFalse =
  refl

canonicalHarnessOSTransferFalse :
  osTransferUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessOSTransferFalse =
  refl

canonicalHarnessContinuumTransferFalse :
  continuumTransferUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessContinuumTransferFalse =
  refl

canonicalHarnessYMClayFalse :
  ymClayPromotedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessYMClayFalse =
  refl

canonicalHarnessTerminalPromotionFalse :
  terminalPromotionField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  false
canonicalHarnessTerminalPromotionFalse =
  refl

noFiniteSelfAdjointTheoremFromProxyHarness :
  finiteSelfAdjointTheoremProvedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noFiniteSelfAdjointTheoremFromProxyHarness ()

noHamiltonianDominationFromProxyHarness :
  hamiltonianDominationUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noHamiltonianDominationFromProxyHarness ()

noOSTransferFromProxyHarness :
  osTransferUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noOSTransferFromProxyHarness ()

noContinuumTransferFromProxyHarness :
  continuumTransferUnlockedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noContinuumTransferFromProxyHarness ()

noYMClayFromProxyHarness :
  ymClayPromotedField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noYMClayFromProxyHarness ()

noTerminalPromotionFromProxyHarness :
  terminalPromotionField
    canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult
  ≡
  true →
  ⊥
noTerminalPromotionFromProxyHarness ()

canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessRecordNames :
  List String
canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessRecordNames =
  "YMFiniteSelfAdjointHamiltonianProxyHarnessResult"
  ∷ "YMHamiltonianProxyCase"
  ∷ "YMHamiltonianProxyCheck"
  ∷ "YMHamiltonianProxyCaseReceipt"
  ∷ "ImportedFiniteSelfAdjointBoundarySupport"
  ∷ "canonicalYMFiniteSelfAdjointHamiltonianProxyHarnessResult"
  ∷ []
