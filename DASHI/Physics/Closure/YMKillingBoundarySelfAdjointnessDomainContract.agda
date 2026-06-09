module DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessDomainContract where

-- Domain/self-adjointness contract for the first YM rung after the finite
-- boundary-sensitivity diagnostics.
--
-- The current BT/YM route uses the full-degree/Killing boundary convention
-- as the admissible candidate after induced-ball truncations were observed to
-- collapse the proxy gap signal.  This module records the exact operator
-- obligations that must be proved before that convention can feed a genuine
-- self-adjoint finite Hamiltonian on the gauge quotient.
--
-- It is a contract boundary only.  It imports the existing admissible
-- boundary, finite quotient precondition, finite self-adjointness, domination,
-- and spectral-margin surfaces, but it does not prove the domain theorem,
-- does not prove Hamiltonian domination, does not prove OS/continuum transfer,
-- and keeps YM Clay / terminal promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMAdmissibleBTBoundaryConventionBoundary
  as Boundary
import DASHI.Physics.Closure.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary
  as Precondition
import DASHI.Physics.Closure.YMSelfAdjointFiniteHamiltonianBoundary
  as SelfAdjoint
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary
  as Domination
import DASHI.Physics.Closure.YMSpectralMarginErrorBudgetCompositeBoundary
  as SpectralBudget
import DASHI.Physics.Closure.YMSpectralMarginBoundarySensitivityProxyHarnessResult
  as BoundarySensitivity

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

data YMKillingBoundaryDomainImportedSupport : Set where
  admissibleBTBoundaryConventionImported :
    YMKillingBoundaryDomainImportedSupport

  finiteGaugeQuotientPreconditionImported :
    YMKillingBoundaryDomainImportedSupport

  finiteSelfAdjointBoundaryImported :
    YMKillingBoundaryDomainImportedSupport

  hamiltonianDominationBoundaryImported :
    YMKillingBoundaryDomainImportedSupport

  spectralMarginErrorBudgetImported :
    YMKillingBoundaryDomainImportedSupport

  boundarySensitivityProxyReceiptImported :
    YMKillingBoundaryDomainImportedSupport

canonicalYMKillingBoundaryDomainImportedSupport :
  List YMKillingBoundaryDomainImportedSupport
canonicalYMKillingBoundaryDomainImportedSupport =
  admissibleBTBoundaryConventionImported
  ∷ finiteGaugeQuotientPreconditionImported
  ∷ finiteSelfAdjointBoundaryImported
  ∷ hamiltonianDominationBoundaryImported
  ∷ spectralMarginErrorBudgetImported
  ∷ boundarySensitivityProxyReceiptImported
  ∷ []

------------------------------------------------------------------------
-- Contract stages and obligations.

data YMKillingBoundaryDomainStatus : Set where
  domainContractRecordedTheoremStillOpen :
    YMKillingBoundaryDomainStatus

data YMKillingBoundaryDomainStage : Set where
  fullDegreeKillingConventionStage :
    YMKillingBoundaryDomainStage

  finiteBTCellDomainStage :
    YMKillingBoundaryDomainStage

  boundaryFluxCancellationStage :
    YMKillingBoundaryDomainStage

  finiteHodgeAdjointCompatibilityStage :
    YMKillingBoundaryDomainStage

  gaugeInvariantDomainStage :
    YMKillingBoundaryDomainStage

  quotientDomainDescentStage :
    YMKillingBoundaryDomainStage

  symmetricFiniteHamiltonianStage :
    YMKillingBoundaryDomainStage

  selfAdjointFiniteQuotientStage :
    YMKillingBoundaryDomainStage

  spectralMarginInputStage :
    YMKillingBoundaryDomainStage

  clayPromotionGuardStage :
    YMKillingBoundaryDomainStage

canonicalYMKillingBoundaryDomainStages :
  List YMKillingBoundaryDomainStage
canonicalYMKillingBoundaryDomainStages =
  fullDegreeKillingConventionStage
  ∷ finiteBTCellDomainStage
  ∷ boundaryFluxCancellationStage
  ∷ finiteHodgeAdjointCompatibilityStage
  ∷ gaugeInvariantDomainStage
  ∷ quotientDomainDescentStage
  ∷ symmetricFiniteHamiltonianStage
  ∷ selfAdjointFiniteQuotientStage
  ∷ spectralMarginInputStage
  ∷ clayPromotionGuardStage
  ∷ []

data YMKillingBoundaryDomainObligation : Set where
  requireFullDegreeKillingBoundaryConvention :
    YMKillingBoundaryDomainObligation

  defineFiniteCellDomainClosedUnderBoundary :
    YMKillingBoundaryDomainObligation

  proveBoundaryFluxCancellationForIBP :
    YMKillingBoundaryDomainObligation

  routeFiniteHodgeAdjointnessThroughBoundary :
    YMKillingBoundaryDomainObligation

  proveGaugeActionPreservesDomain :
    YMKillingBoundaryDomainObligation

  proveGaugeInvariantProjectionPreservesDomain :
    YMKillingBoundaryDomainObligation

  proveHamiltonianConstantOnGaugeOrbits :
    YMKillingBoundaryDomainObligation

  proveQuotientDomainWellDefined :
    YMKillingBoundaryDomainObligation

  proveSymmetricFiniteMatrixOnQuotient :
    YMKillingBoundaryDomainObligation

  proveSelfAdjointFiniteMatrixOnQuotient :
    YMKillingBoundaryDomainObligation

  feedOnlyAsInputToDominationAndSpectralMargin :
    YMKillingBoundaryDomainObligation

  keepOSContinuumAndClayPromotionSeparate :
    YMKillingBoundaryDomainObligation

canonicalYMKillingBoundaryDomainObligations :
  List YMKillingBoundaryDomainObligation
canonicalYMKillingBoundaryDomainObligations =
  requireFullDegreeKillingBoundaryConvention
  ∷ defineFiniteCellDomainClosedUnderBoundary
  ∷ proveBoundaryFluxCancellationForIBP
  ∷ routeFiniteHodgeAdjointnessThroughBoundary
  ∷ proveGaugeActionPreservesDomain
  ∷ proveGaugeInvariantProjectionPreservesDomain
  ∷ proveHamiltonianConstantOnGaugeOrbits
  ∷ proveQuotientDomainWellDefined
  ∷ proveSymmetricFiniteMatrixOnQuotient
  ∷ proveSelfAdjointFiniteMatrixOnQuotient
  ∷ feedOnlyAsInputToDominationAndSpectralMargin
  ∷ keepOSContinuumAndClayPromotionSeparate
  ∷ []

data YMKillingBoundaryDomainBlocker : Set where
  missingFiniteBTCellDomainClosure :
    YMKillingBoundaryDomainBlocker

  missingKillingBoundaryFluxCancellation :
    YMKillingBoundaryDomainBlocker

  missingFiniteHodgeAdjointnessBoundaryRouting :
    YMKillingBoundaryDomainBlocker

  missingGaugeActionDomainInvariance :
    YMKillingBoundaryDomainBlocker

  missingGaugeInvariantProjectionDomainInvariance :
    YMKillingBoundaryDomainBlocker

  missingHamiltonianGaugeOrbitCompatibility :
    YMKillingBoundaryDomainBlocker

  missingQuotientDomainDescent :
    YMKillingBoundaryDomainBlocker

  missingSymmetricFiniteMatrixProof :
    YMKillingBoundaryDomainBlocker

  missingSelfAdjointFiniteQuotientProof :
    YMKillingBoundaryDomainBlocker

  missingHamiltonianDominationUseOfSelfAdjointInput :
    YMKillingBoundaryDomainBlocker

  missingReflectionPositiveOSTransfer :
    YMKillingBoundaryDomainBlocker

  missingContinuumNoSpectralPollution :
    YMKillingBoundaryDomainBlocker

  missingClayYangMillsAuthorityToken :
    YMKillingBoundaryDomainBlocker

canonicalYMKillingBoundaryDomainBlockers :
  List YMKillingBoundaryDomainBlocker
canonicalYMKillingBoundaryDomainBlockers =
  missingFiniteBTCellDomainClosure
  ∷ missingKillingBoundaryFluxCancellation
  ∷ missingFiniteHodgeAdjointnessBoundaryRouting
  ∷ missingGaugeActionDomainInvariance
  ∷ missingGaugeInvariantProjectionDomainInvariance
  ∷ missingHamiltonianGaugeOrbitCompatibility
  ∷ missingQuotientDomainDescent
  ∷ missingSymmetricFiniteMatrixProof
  ∷ missingSelfAdjointFiniteQuotientProof
  ∷ missingHamiltonianDominationUseOfSelfAdjointInput
  ∷ missingReflectionPositiveOSTransfer
  ∷ missingContinuumNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMKillingBoundaryDomainObligationRow : Set where
  field
    obligation :
      YMKillingBoundaryDomainObligation

    label :
      String

    contractText :
      String

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

open YMKillingBoundaryDomainObligationRow public

mkYMKillingBoundaryDomainObligationRow :
  YMKillingBoundaryDomainObligation →
  String →
  String →
  YMKillingBoundaryDomainObligationRow
mkYMKillingBoundaryDomainObligationRow obligation label contractText =
  record
    { obligation =
        obligation
    ; label =
        label
    ; contractText =
        contractText
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    }

canonicalYMKillingBoundaryDomainObligationRows :
  List YMKillingBoundaryDomainObligationRow
canonicalYMKillingBoundaryDomainObligationRows =
  mkYMKillingBoundaryDomainObligationRow
    requireFullDegreeKillingBoundaryConvention
    "boundary convention"
    "Use full-degree/Killing BT boundary convention; induced finite-ball convention is not accepted as current gap carrier."
  ∷ mkYMKillingBoundaryDomainObligationRow
    defineFiniteCellDomainClosedUnderBoundary
    "finite domain"
    "Define a finite BT cell/configuration domain closed under all boundary faces included by the Killing convention."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveBoundaryFluxCancellationForIBP
    "IBP cancellation"
    "Prove the finite boundary flux terms vanish or pair symmetrically so <H_d phi, psi> = <phi, H_d psi> has no boundary residual."
  ∷ mkYMKillingBoundaryDomainObligationRow
    routeFiniteHodgeAdjointnessThroughBoundary
    "Hodge adjointness"
    "Route finite d_A / d_A* compatibility through the same domain instead of a proxy or induced-ball domain."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveGaugeActionPreservesDomain
    "gauge action"
    "Show the finite gauge action maps the Killing-boundary domain to itself."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveGaugeInvariantProjectionPreservesDomain
    "gauge projection"
    "Show the gauge-invariant projection is well-defined on the Killing-boundary domain."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveHamiltonianConstantOnGaugeOrbits
    "orbit compatibility"
    "Show H_d is compatible with gauge orbits and has a well-defined quotient action."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveQuotientDomainWellDefined
    "quotient domain"
    "Construct the finite quotient domain and prove representatives give identical H_d action."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveSymmetricFiniteMatrixOnQuotient
    "symmetric matrix"
    "Represent H_d as a finite symmetric matrix/operator on the quotient domain."
  ∷ mkYMKillingBoundaryDomainObligationRow
    proveSelfAdjointFiniteMatrixOnQuotient
    "self-adjoint quotient"
    "Use finite-dimensional symmetry on the quotient Hilbert carrier to obtain self-adjointness and real finite spectrum."
  ∷ mkYMKillingBoundaryDomainObligationRow
    feedOnlyAsInputToDominationAndSpectralMargin
    "domination input"
    "Feed this theorem only as an input to H_d >= c1 Delta_YM + c2 Hol_d - E_d and spectral-margin budgets."
  ∷ mkYMKillingBoundaryDomainObligationRow
    keepOSContinuumAndClayPromotionSeparate
    "promotion guard"
    "Do not promote OS transfer, continuum no-pollution, YM Clay, or terminal unification from this domain contract."
  ∷ []

------------------------------------------------------------------------
-- Contract flags.

contractRecorded : Bool
contractRecorded =
  true

admissibleBoundaryImported : Bool
admissibleBoundaryImported =
  true

boundarySensitivityRecorded : Bool
boundarySensitivityRecorded =
  true

fullDegreeKillingAcceptedAsCandidate : Bool
fullDegreeKillingAcceptedAsCandidate =
  true

domainClosureProved : Bool
domainClosureProved =
  false

boundaryFluxCancellationProved : Bool
boundaryFluxCancellationProved =
  false

gaugeCompatibilityProved : Bool
gaugeCompatibilityProved =
  false

quotientDomainDescentProved : Bool
quotientDomainDescentProved =
  false

symmetricFiniteHamiltonianProved : Bool
symmetricFiniteHamiltonianProved =
  false

selfAdjointQuotientHamiltonianProved : Bool
selfAdjointQuotientHamiltonianProved =
  false

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
  false

spectralMarginPromoted : Bool
spectralMarginPromoted =
  false

osContinuumTransferProved : Bool
osContinuumTransferProved =
  false

ymClayPromoted : Bool
ymClayPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

contractRecordedIsTrue :
  contractRecorded ≡ true
contractRecordedIsTrue =
  refl

admissibleBoundaryImportedIsTrue :
  admissibleBoundaryImported ≡ true
admissibleBoundaryImportedIsTrue =
  refl

boundarySensitivityRecordedIsTrue :
  boundarySensitivityRecorded ≡ true
boundarySensitivityRecordedIsTrue =
  refl

fullDegreeKillingAcceptedAsCandidateIsTrue :
  fullDegreeKillingAcceptedAsCandidate ≡ true
fullDegreeKillingAcceptedAsCandidateIsTrue =
  refl

domainClosureProvedIsFalse :
  domainClosureProved ≡ false
domainClosureProvedIsFalse =
  refl

boundaryFluxCancellationProvedIsFalse :
  boundaryFluxCancellationProved ≡ false
boundaryFluxCancellationProvedIsFalse =
  refl

gaugeCompatibilityProvedIsFalse :
  gaugeCompatibilityProved ≡ false
gaugeCompatibilityProvedIsFalse =
  refl

quotientDomainDescentProvedIsFalse :
  quotientDomainDescentProved ≡ false
quotientDomainDescentProvedIsFalse =
  refl

symmetricFiniteHamiltonianProvedIsFalse :
  symmetricFiniteHamiltonianProved ≡ false
symmetricFiniteHamiltonianProvedIsFalse =
  refl

selfAdjointQuotientHamiltonianProvedIsFalse :
  selfAdjointQuotientHamiltonianProved ≡ false
selfAdjointQuotientHamiltonianProvedIsFalse =
  refl

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
  refl

spectralMarginPromotedIsFalse :
  spectralMarginPromoted ≡ false
spectralMarginPromotedIsFalse =
  refl

osContinuumTransferProvedIsFalse :
  osContinuumTransferProved ≡ false
osContinuumTransferProvedIsFalse =
  refl

ymClayPromotedIsFalse :
  ymClayPromoted ≡ false
ymClayPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

domainContractFormula : String
domainContractFormula =
  "<H_d phi, psi>_Killing = <phi, H_d psi>_Killing on the finite gauge-quotient domain"

------------------------------------------------------------------------
-- Canonical contract receipt.

record YMKillingBoundarySelfAdjointnessDomainContract : Setω where
  field
    status :
      YMKillingBoundaryDomainStatus

    admissibleBoundary :
      Boundary.YMAdmissibleBTBoundaryConventionBoundary

    admissibleBoundaryCanonical :
      Bool

    admissibleBoundaryCanonicalIsTrue :
      admissibleBoundaryCanonical ≡ true

    finiteGaugeQuotientPrecondition :
      Precondition.YMFiniteGaugeQuotientHamiltonianPreconditionBoundary

    finiteGaugeQuotientPreconditionCanonical :
      Bool

    finiteGaugeQuotientPreconditionCanonicalIsTrue :
      finiteGaugeQuotientPreconditionCanonical ≡ true

    finiteSelfAdjointBoundary :
      SelfAdjoint.YMSelfAdjointFiniteHamiltonianBoundary

    finiteSelfAdjointBoundaryCanonical :
      Bool

    finiteSelfAdjointBoundaryCanonicalIsTrue :
      finiteSelfAdjointBoundaryCanonical ≡ true

    hamiltonianDominationBoundary :
      Domination.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    hamiltonianDominationBoundaryCanonical :
      Bool

    hamiltonianDominationBoundaryCanonicalIsTrue :
      hamiltonianDominationBoundaryCanonical ≡ true

    spectralMarginBudget :
      SpectralBudget.YMSpectralMarginErrorBudgetCompositeBoundary

    spectralMarginBudgetCanonical :
      Bool

    spectralMarginBudgetCanonicalIsTrue :
      spectralMarginBudgetCanonical ≡ true

    importedSupport :
      List YMKillingBoundaryDomainImportedSupport

    importedSupportIsCanonical :
      importedSupport ≡ canonicalYMKillingBoundaryDomainImportedSupport

    importedSupportCount :
      Nat

    importedSupportCountIs6 :
      importedSupportCount ≡ 6

    stages :
      List YMKillingBoundaryDomainStage

    stagesAreCanonical :
      stages ≡ canonicalYMKillingBoundaryDomainStages

    stageCount :
      Nat

    stageCountIs10 :
      stageCount ≡ 10

    obligations :
      List YMKillingBoundaryDomainObligation

    obligationsAreCanonical :
      obligations ≡ canonicalYMKillingBoundaryDomainObligations

    obligationCount :
      Nat

    obligationCountIs12 :
      obligationCount ≡ 12

    obligationRows :
      List YMKillingBoundaryDomainObligationRow

    obligationRowsAreCanonical :
      obligationRows ≡ canonicalYMKillingBoundaryDomainObligationRows

    obligationRowCount :
      Nat

    obligationRowCountIs12 :
      obligationRowCount ≡ 12

    blockers :
      List YMKillingBoundaryDomainBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMKillingBoundaryDomainBlockers

    blockerCount :
      Nat

    blockerCountIs13 :
      blockerCount ≡ 13

    firstBlocker :
      YMKillingBoundaryDomainBlocker

    firstBlockerIsDomainClosure :
      firstBlocker ≡ missingFiniteBTCellDomainClosure

    contractFormula :
      String

    contractFormulaIsCanonical :
      contractFormula ≡ domainContractFormula

    contractRecordedField :
      Bool

    contractRecordedFieldIsTrue :
      contractRecordedField ≡ true

    admissibleBoundaryImportedField :
      Bool

    admissibleBoundaryImportedFieldIsTrue :
      admissibleBoundaryImportedField ≡ true

    boundarySensitivityRecordedField :
      Bool

    boundarySensitivityRecordedFieldIsTrue :
      boundarySensitivityRecordedField ≡ true

    fullDegreeKillingAcceptedField :
      Bool

    fullDegreeKillingAcceptedFieldIsTrue :
      fullDegreeKillingAcceptedField ≡ true

    domainClosureProvedField :
      Bool

    domainClosureProvedFieldIsFalse :
      domainClosureProvedField ≡ false

    boundaryFluxCancellationProvedField :
      Bool

    boundaryFluxCancellationProvedFieldIsFalse :
      boundaryFluxCancellationProvedField ≡ false

    gaugeCompatibilityProvedField :
      Bool

    gaugeCompatibilityProvedFieldIsFalse :
      gaugeCompatibilityProvedField ≡ false

    quotientDomainDescentProvedField :
      Bool

    quotientDomainDescentProvedFieldIsFalse :
      quotientDomainDescentProvedField ≡ false

    symmetricFiniteHamiltonianProvedField :
      Bool

    symmetricFiniteHamiltonianProvedFieldIsFalse :
      symmetricFiniteHamiltonianProvedField ≡ false

    selfAdjointQuotientHamiltonianProvedField :
      Bool

    selfAdjointQuotientHamiltonianProvedFieldIsFalse :
      selfAdjointQuotientHamiltonianProvedField ≡ false

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

    spectralMarginPromotedField :
      Bool

    spectralMarginPromotedFieldIsFalse :
      spectralMarginPromotedField ≡ false

    osContinuumTransferProvedField :
      Bool

    osContinuumTransferProvedFieldIsFalse :
      osContinuumTransferProvedField ≡ false

    ymClayPromotedField :
      Bool

    ymClayPromotedFieldIsFalse :
      ymClayPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    importedBoundaryInducedBallStillRejected :
      Boundary.inducedBallAcceptedAsCurrentGapCarrierField
        admissibleBoundary
      ≡
      false

    importedPreconditionFiniteQuotientStillMissing :
      Precondition.finiteQuotientConstructedField
        finiteGaugeQuotientPrecondition
      ≡
      false

    importedPreconditionSelfAdjointStillMissing :
      Precondition.selfAdjointHamiltonianProvedField
        finiteGaugeQuotientPrecondition
      ≡
      false

    importedSelfAdjointBoundaryStillOpen :
      SelfAdjoint.selfAdjointFiniteHamiltonianProvedField
        finiteSelfAdjointBoundary
      ≡
      false

    importedDominationStillOpen :
      Domination.dominationPlusHolonomyProvedField
        hamiltonianDominationBoundary
      ≡
      false

    importedSpectralMarginStillOpen :
      SpectralBudget.spectralMarginTheoremProved
        spectralMarginBudget
      ≡
      false

    boundarySensitivityDiagnosticOnly :
      BoundarySensitivity.promotion ≡ false

    notes :
      List String

open YMKillingBoundarySelfAdjointnessDomainContract public

canonicalYMKillingBoundarySelfAdjointnessDomainContract :
  YMKillingBoundarySelfAdjointnessDomainContract
canonicalYMKillingBoundarySelfAdjointnessDomainContract =
  record
    { status =
        domainContractRecordedTheoremStillOpen
    ; admissibleBoundary =
        Boundary.canonicalYMAdmissibleBTBoundaryConventionBoundary
    ; admissibleBoundaryCanonical =
        true
    ; admissibleBoundaryCanonicalIsTrue =
        refl
    ; finiteGaugeQuotientPrecondition =
        Precondition.canonicalYMFiniteGaugeQuotientHamiltonianPreconditionBoundary
    ; finiteGaugeQuotientPreconditionCanonical =
        true
    ; finiteGaugeQuotientPreconditionCanonicalIsTrue =
        refl
    ; finiteSelfAdjointBoundary =
        SelfAdjoint.canonicalYMSelfAdjointFiniteHamiltonianBoundary
    ; finiteSelfAdjointBoundaryCanonical =
        true
    ; finiteSelfAdjointBoundaryCanonicalIsTrue =
        refl
    ; hamiltonianDominationBoundary =
        Domination.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; hamiltonianDominationBoundaryCanonical =
        true
    ; hamiltonianDominationBoundaryCanonicalIsTrue =
        refl
    ; spectralMarginBudget =
        SpectralBudget.canonicalYMSpectralMarginErrorBudgetCompositeBoundary
    ; spectralMarginBudgetCanonical =
        true
    ; spectralMarginBudgetCanonicalIsTrue =
        refl
    ; importedSupport =
        canonicalYMKillingBoundaryDomainImportedSupport
    ; importedSupportIsCanonical =
        refl
    ; importedSupportCount =
        listCount canonicalYMKillingBoundaryDomainImportedSupport
    ; importedSupportCountIs6 =
        refl
    ; stages =
        canonicalYMKillingBoundaryDomainStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMKillingBoundaryDomainStages
    ; stageCountIs10 =
        refl
    ; obligations =
        canonicalYMKillingBoundaryDomainObligations
    ; obligationsAreCanonical =
        refl
    ; obligationCount =
        listCount canonicalYMKillingBoundaryDomainObligations
    ; obligationCountIs12 =
        refl
    ; obligationRows =
        canonicalYMKillingBoundaryDomainObligationRows
    ; obligationRowsAreCanonical =
        refl
    ; obligationRowCount =
        listCount canonicalYMKillingBoundaryDomainObligationRows
    ; obligationRowCountIs12 =
        refl
    ; blockers =
        canonicalYMKillingBoundaryDomainBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMKillingBoundaryDomainBlockers
    ; blockerCountIs13 =
        refl
    ; firstBlocker =
        missingFiniteBTCellDomainClosure
    ; firstBlockerIsDomainClosure =
        refl
    ; contractFormula =
        domainContractFormula
    ; contractFormulaIsCanonical =
        refl
    ; contractRecordedField =
        contractRecorded
    ; contractRecordedFieldIsTrue =
        contractRecordedIsTrue
    ; admissibleBoundaryImportedField =
        admissibleBoundaryImported
    ; admissibleBoundaryImportedFieldIsTrue =
        admissibleBoundaryImportedIsTrue
    ; boundarySensitivityRecordedField =
        boundarySensitivityRecorded
    ; boundarySensitivityRecordedFieldIsTrue =
        boundarySensitivityRecordedIsTrue
    ; fullDegreeKillingAcceptedField =
        fullDegreeKillingAcceptedAsCandidate
    ; fullDegreeKillingAcceptedFieldIsTrue =
        fullDegreeKillingAcceptedAsCandidateIsTrue
    ; domainClosureProvedField =
        domainClosureProved
    ; domainClosureProvedFieldIsFalse =
        domainClosureProvedIsFalse
    ; boundaryFluxCancellationProvedField =
        boundaryFluxCancellationProved
    ; boundaryFluxCancellationProvedFieldIsFalse =
        boundaryFluxCancellationProvedIsFalse
    ; gaugeCompatibilityProvedField =
        gaugeCompatibilityProved
    ; gaugeCompatibilityProvedFieldIsFalse =
        gaugeCompatibilityProvedIsFalse
    ; quotientDomainDescentProvedField =
        quotientDomainDescentProved
    ; quotientDomainDescentProvedFieldIsFalse =
        quotientDomainDescentProvedIsFalse
    ; symmetricFiniteHamiltonianProvedField =
        symmetricFiniteHamiltonianProved
    ; symmetricFiniteHamiltonianProvedFieldIsFalse =
        symmetricFiniteHamiltonianProvedIsFalse
    ; selfAdjointQuotientHamiltonianProvedField =
        selfAdjointQuotientHamiltonianProved
    ; selfAdjointQuotientHamiltonianProvedFieldIsFalse =
        selfAdjointQuotientHamiltonianProvedIsFalse
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
        hamiltonianDominationProvedIsFalse
    ; spectralMarginPromotedField =
        spectralMarginPromoted
    ; spectralMarginPromotedFieldIsFalse =
        spectralMarginPromotedIsFalse
    ; osContinuumTransferProvedField =
        osContinuumTransferProved
    ; osContinuumTransferProvedFieldIsFalse =
        osContinuumTransferProvedIsFalse
    ; ymClayPromotedField =
        ymClayPromoted
    ; ymClayPromotedFieldIsFalse =
        ymClayPromotedIsFalse
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        terminalPromotionIsFalse
    ; importedBoundaryInducedBallStillRejected =
        Boundary.inducedBallAcceptedAsCurrentGapCarrierIsFalse
    ; importedPreconditionFiniteQuotientStillMissing =
        Precondition.canonicalFiniteQuotientConstructedFalse
    ; importedPreconditionSelfAdjointStillMissing =
        Precondition.canonicalSelfAdjointHamiltonianProvedFalse
    ; importedSelfAdjointBoundaryStillOpen =
        SelfAdjoint.canonicalSelfAdjointFiniteHamiltonianProvedFalse
    ; importedDominationStillOpen =
        Domination.canonicalYMHamiltonianDominationPlusHolonomyProvedFalse
    ; importedSpectralMarginStillOpen =
        SpectralBudget.spectralMarginTheoremProvedIsFalse
    ; boundarySensitivityDiagnosticOnly =
        BoundarySensitivity.promotion_is_false
    ; notes =
        "This contract hardens the first post-boundary-sensitivity YM rung: full-degree/Killing finite domain, IBP boundary cancellation, gauge-domain invariance, quotient descent, and finite self-adjointness."
        ∷ "The boundary-sensitivity harness is consumed only as a diagnostic receipt; it does not prove the domain theorem."
        ∷ "The contract may feed Hamiltonian domination only after domain closure, gauge compatibility, quotient descent, symmetry, and finite self-adjointness are proved."
        ∷ "Domination, spectral margin, OS transfer, continuum no-spectral-pollution, YM Clay, and terminal promotion remain false."
        ∷ []
    }

------------------------------------------------------------------------
-- Guard lemmas.

canonicalKillingBoundaryDomainImportedSupportCountIs6 :
  importedSupportCount canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  6
canonicalKillingBoundaryDomainImportedSupportCountIs6 =
  refl

canonicalKillingBoundaryDomainObligationCountIs12 :
  obligationCount canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  12
canonicalKillingBoundaryDomainObligationCountIs12 =
  refl

canonicalKillingBoundaryDomainFirstBlocker :
  firstBlocker canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  missingFiniteBTCellDomainClosure
canonicalKillingBoundaryDomainFirstBlocker =
  refl

canonicalKillingBoundaryDomainSelfAdjointStillFalse :
  selfAdjointQuotientHamiltonianProvedField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
canonicalKillingBoundaryDomainSelfAdjointStillFalse =
  refl

canonicalKillingBoundaryDomainDominationStillFalse :
  hamiltonianDominationProvedField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
canonicalKillingBoundaryDomainDominationStillFalse =
  refl

canonicalKillingBoundaryDomainYMClayStillFalse :
  ymClayPromotedField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
canonicalKillingBoundaryDomainYMClayStillFalse =
  refl

canonicalKillingBoundaryDomainTerminalStillFalse :
  terminalPromotionField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  false
canonicalKillingBoundaryDomainTerminalStillFalse =
  refl

data YMKillingBoundaryDomainPromotionToken : Set where

ymKillingBoundaryDomainPromotionTokenImpossibleHere :
  YMKillingBoundaryDomainPromotionToken →
  ⊥
ymKillingBoundaryDomainPromotionTokenImpossibleHere ()

noSelfAdjointPromotionFromKillingBoundaryDomainContractAlone :
  selfAdjointQuotientHamiltonianProvedField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  true →
  ⊥
noSelfAdjointPromotionFromKillingBoundaryDomainContractAlone ()

noYMClayPromotionFromKillingBoundaryDomainContractAlone :
  ymClayPromotedField
    canonicalYMKillingBoundarySelfAdjointnessDomainContract
  ≡
  true →
  ⊥
noYMClayPromotionFromKillingBoundaryDomainContractAlone ()
