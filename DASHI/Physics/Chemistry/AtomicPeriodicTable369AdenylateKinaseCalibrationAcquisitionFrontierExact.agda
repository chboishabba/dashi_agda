module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAcquisitionFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact as Ledger
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSupportingMaterialManifestationExact as Manifestation
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attribution
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseIntermediateGeometryTextAcquisitionExact as Intermediate
import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as Monster

------------------------------------------------------------------------
-- PROPOSITION-INDEXED ADK CALIBRATION ACQUISITION FRONTIER
--
-- This owner is a routing view over the existing cell-level ledger, not a new
-- calibration database.  It cross-pollinates the repo's recent acquisition-debt
-- and Monster 3B disciplines:
--
--   * debt is proposition-indexed;
--   * neighbouring/source-role evidence may partially pay a debt but cannot
--     manufacture the requested numeric cell;
--   * acquisition/access failure is a gap state, never evidence that the value
--     does not exist;
--   * consumer payment uses least privilege: same manifestation + compatible
--     observable + exact locator + value-role receipt;
--   * DOI/QID/PDB/UniProt remain provenance coordinates and are required only
--     when the particular same-object question actually needs them.
--
-- The Monster owner is a DASHI design donor only.  It transfers no AdK science,
-- authorship, numeric value, biological mechanism or authority.
--
-- Live-master correction: all eight Figure-5 relative energies and the six
-- forward Kramers-rate numerics are already paid by the merged #939 lineage.
-- The active numeric frontier is named-state intermediate geometry.
------------------------------------------------------------------------

data DebtStatus : Set where
  unpaid partiallyPaid paid : DebtStatus

data AcquisitionGapState : Set where
  noDeclaredGap exactLocatorGap sourceAccessGap sourceUnavailableGap : AcquisitionGapState

data CalibrationDebtCoordinate : Set where
  betaThetaOne betaThetaTwo betaDLn : CalibrationDebtCoordinate
  gammaThetaOne gammaThetaTwo gammaDLn : CalibrationDebtCoordinate
  deltaThetaOne deltaThetaTwo deltaDLn : CalibrationDebtCoordinate
  epsilonThetaOne epsilonThetaTwo epsilonDLn : CalibrationDebtCoordinate
  etaThetaOne etaThetaTwo etaDLn : CalibrationDebtCoordinate
  lambdaThetaOne lambdaThetaTwo lambdaDLn : CalibrationDebtCoordinate

record CalibrationAcquisitionDebt : Set where
  constructor calibration-acquisition-debt
  field
    coordinate : CalibrationDebtCoordinate
    status : DebtStatus
    ledgerCell : Ledger.CalibrationPaymentCell
    propositionNeeded : String
    preferredManifestation : String
    observableDefinition : String
    exactLocatorRequirement : String
    methodOrRateKind : String
    currentBoundary : String
    gapState : AcquisitionGapState
    externalIdentityRequirement : String
open CalibrationAcquisitionDebt public

partialGeometryDebt :
  CalibrationDebtCoordinate → Ledger.CalibrationPaymentCell →
  String → String → String → CalibrationAcquisitionDebt
partialGeometryDebt coordinate cell proposition observable boundary =
  calibration-acquisition-debt
    coordinate partiallyPaid cell proposition
    "same-object Li-Liu-Ji article text, Figure-5 panel, or PMC-attached same-article supplement"
    observable
    "exact named-state plus coordinate locator; region envelopes and neighbouring states do not suffice"
    "source-text or separately receipted figure/supplement readout preserving the Figure-1 observable definition"
    boundary
    exactLocatorGap
    "DOI/PMID/PMCID/QID/PDB/UniProt stay retained provenance coordinates; none is a universal numeric premise"

unpaidGeometryDebt :
  CalibrationDebtCoordinate → Ledger.CalibrationPaymentCell →
  String → String → String → CalibrationAcquisitionDebt
unpaidGeometryDebt coordinate cell proposition observable boundary =
  calibration-acquisition-debt
    coordinate unpaid cell proposition
    "same-object Li-Liu-Ji article/Figure-5/PMC-attached supplement"
    observable
    "exact named-state plus coordinate locator"
    "same observable definition as Li-Liu-Ji Figure-1 collective variable"
    boundary
    exactLocatorGap
    "external identifiers are provenance/navigation unless needed to establish the same-object manifestation"

------------------------------------------------------------------------
-- Active debts.  beta/gamma/delta/epsilon have a source-paid intermediate
-- three-coordinate region; eta/lambda have only near-closed qualitative roles.
-- 'partiallyPaid' therefore records paid constraints, not permission to infer a
-- named-state numeral.
------------------------------------------------------------------------

betaThetaOneDebt = partialGeometryDebt betaThetaOne Ledger.betaThetaOne
  "numeric theta1(beta)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "beta qualitative intermediate role paid; exact theta1(beta) unpaid"
betaThetaTwoDebt = partialGeometryDebt betaThetaTwo Ledger.betaThetaTwo
  "numeric theta2(beta)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "beta qualitative intermediate role paid; exact theta2(beta) unpaid"
betaDLnDebt = partialGeometryDebt betaDLn Ledger.betaDLn
  "numeric dLN(beta)" "LID--NMP domain center-of-mass distance"
  "intermediate dLN approximately 16--30 A paid only at region level"

gammaThetaOneDebt = partialGeometryDebt gammaThetaOne Ledger.gammaThetaOne
  "numeric theta1(gamma)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "gamma role and gamma-near structural references paid; exact theta1(gamma) unpaid"
gammaThetaTwoDebt = partialGeometryDebt gammaThetaTwo Ledger.gammaThetaTwo
  "numeric theta2(gamma)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "gamma role and gamma-near structural references paid; exact theta2(gamma) unpaid"
gammaDLnDebt = partialGeometryDebt gammaDLn Ledger.gammaDLn
  "numeric dLN(gamma)" "LID--NMP domain center-of-mass distance"
  "intermediate dLN approximately 16--30 A and gamma role paid; exact gamma dLN unpaid"

deltaThetaOneDebt = partialGeometryDebt deltaThetaOne Ledger.deltaThetaOne
  "numeric theta1(delta)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "delta intermediate role paid; exact theta1(delta) unpaid"
deltaThetaTwoDebt = partialGeometryDebt deltaThetaTwo Ledger.deltaThetaTwo
  "numeric theta2(delta)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "delta semi-open NMP role paid; exact theta2(delta) unpaid"
deltaDLnDebt = partialGeometryDebt deltaDLn Ledger.deltaDLn
  "numeric dLN(delta)" "LID--NMP domain center-of-mass distance"
  "intermediate dLN approximately 16--30 A paid only at region level"

epsilonThetaOneDebt = partialGeometryDebt epsilonThetaOne Ledger.epsilonThetaOne
  "numeric theta1(epsilon)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "epsilon alternative-route role paid; exact theta1(epsilon) unpaid"
epsilonThetaTwoDebt = partialGeometryDebt epsilonThetaTwo Ledger.epsilonThetaTwo
  "numeric theta2(epsilon)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "epsilon alternative-route role paid; exact theta2(epsilon) unpaid"
epsilonDLnDebt = partialGeometryDebt epsilonDLn Ledger.epsilonDLn
  "numeric dLN(epsilon)" "LID--NMP domain center-of-mass distance"
  "intermediate dLN approximately 16--30 A paid only at region level"

etaThetaOneDebt = partialGeometryDebt etaThetaOne Ledger.etaThetaOne
  "numeric theta1(eta)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "eta near-closed qualitative role paid; exact theta1(eta) unpaid"
etaThetaTwoDebt = partialGeometryDebt etaThetaTwo Ledger.etaThetaTwo
  "numeric theta2(eta)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "eta near-closed qualitative role paid; exact theta2(eta) unpaid"
etaDLnDebt = unpaidGeometryDebt etaDLn Ledger.etaDLn
  "numeric dLN(eta)" "LID--NMP domain center-of-mass distance"
  "near-closed role alone supplies no state-specific dLN numeral or interval"

lambdaThetaOneDebt = partialGeometryDebt lambdaThetaOne Ledger.lambdaThetaOne
  "numeric theta1(lambda)" "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "lambda near-closed qualitative role paid; exact theta1(lambda) unpaid"
lambdaThetaTwoDebt = partialGeometryDebt lambdaThetaTwo Ledger.lambdaThetaTwo
  "numeric theta2(lambda)" "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "lambda near-closed qualitative role paid; exact theta2(lambda) unpaid"
lambdaDLnDebt = unpaidGeometryDebt lambdaDLn Ledger.lambdaDLn
  "numeric dLN(lambda)" "LID--NMP domain center-of-mass distance"
  "near-closed role alone supplies no state-specific dLN numeral or interval"

activeGeometryDebts : List CalibrationAcquisitionDebt
activeGeometryDebts =
  betaThetaOneDebt ∷ betaThetaTwoDebt ∷ betaDLnDebt ∷
  gammaThetaOneDebt ∷ gammaThetaTwoDebt ∷ gammaDLnDebt ∷
  deltaThetaOneDebt ∷ deltaThetaTwoDebt ∷ deltaDLnDebt ∷
  epsilonThetaOneDebt ∷ epsilonThetaTwoDebt ∷ epsilonDLnDebt ∷
  etaThetaOneDebt ∷ etaThetaTwoDebt ∷ etaDLnDebt ∷
  lambdaThetaOneDebt ∷ lambdaThetaTwoDebt ∷ lambdaDLnDebt ∷ []

------------------------------------------------------------------------
-- Closed proposition families.  These aliases deliberately reuse the live
-- ledger rather than restating values in this owner.
------------------------------------------------------------------------

figureFiveFreeEnergyPayments : List Ledger.CalibrationPaymentCell
figureFiveFreeEnergyPayments =
  Ledger.alphaEnergy ∷ Ledger.betaEnergy ∷ Ledger.gammaEnergy ∷ Ledger.deltaEnergy ∷
  Ledger.epsilonEnergy ∷ Ledger.zetaEnergy ∷ Ledger.etaEnergy ∷ Ledger.lambdaEnergy ∷ []

forwardKramersRatePayments : List Ledger.CalibrationPaymentCell
forwardKramersRatePayments =
  Ledger.alphaBetaRate ∷ Ledger.betaGammaRate ∷ Ledger.gammaDeltaRate ∷
  Ledger.deltaTerminalRate ∷ Ledger.betaEpsilonRate ∷ Ledger.epsilonTerminalRate ∷ []

------------------------------------------------------------------------
-- Least-privilege numeric promotion.
--
-- The receipt's fields are exactly the facts consumed by numeric promotion.
-- External IDs are intentionally absent.  They remain in the attribution layer
-- and are consulted only when needed to prove same-object manifestation identity.
------------------------------------------------------------------------

record LeastPrivilegeNumericPromotionReceipt : Set₁ where
  field
    SameObjectManifestationPayment : Set
    sameObjectManifestationPayment : SameObjectManifestationPayment
    CompatibleObservableDefinition : Set
    compatibleObservableDefinition : CompatibleObservableDefinition
    ExactStateOrEdgeLocator : Set
    exactStateOrEdgeLocator : ExactStateOrEdgeLocator
    ValueRolePayment : Set
    valueRolePayment : ValueRolePayment
    numericValue : Nat
    sourceLocator : String
open LeastPrivilegeNumericPromotionReceipt public

promoteWithLeastPrivilegeReceipt :
  LeastPrivilegeNumericPromotionReceipt → Sparse.NumericPayment
promoteWithLeastPrivilegeReceipt receipt =
  Sparse.paidNumeric (numericValue receipt) (sourceLocator receipt)

------------------------------------------------------------------------
-- Reused live surfaces and explicit Monster design donor.
------------------------------------------------------------------------

supportingMaterialBoundary : Manifestation.SupportingMaterialManifestationBoundary
supportingMaterialBoundary = Manifestation.canonicalSupportingMaterialManifestationBoundary

guardedAcquisitionBoundary : Guard.GuardedCalibrationAcquisitionBoundary
guardedAcquisitionBoundary = Guard.canonicalGuardedCalibrationAcquisitionBoundary

articleAttributionBoundary : Attribution.AdKCalibrationAttributionBoundary
articleAttributionBoundary = Attribution.canonicalAdKCalibrationAttributionBoundary

collectiveVariableBoundary : CV.AdKCollectiveVariableDefinitionAcquisitionBoundary
collectiveVariableBoundary = CV.canonicalAdKCollectiveVariableDefinitionAcquisitionBoundary

intermediateGeometryBoundary : Intermediate.AdKIntermediateGeometryTextAcquisitionBoundary
intermediateGeometryBoundary = Intermediate.canonicalAdKIntermediateGeometryTextAcquisitionBoundary

monsterAcquisitionDesignDonor : Monster.ActualLinearMultiplicityAcquisitionFrontier
monsterAcquisitionDesignDonor = Monster.currentActualLinearMultiplicityAcquisitionFrontier

------------------------------------------------------------------------
-- WrongType / evidence-health / attribution firewalls.
------------------------------------------------------------------------

data PaidNeighbourCreatesTargetPayment : Set where
data AcquisitionFailureCreatesValueAbsence : Set where
data RegionEnvelopeCreatesNamedStateNumeral : Set where
data SameVariableLabelCreatesSameObservable : Set where
data ExternalIdentityCreatesNumericPayment : Set where
data MonsterAcquisitionCreatesAdKScientificAuthority : Set where

paidNeighbourDoesNotCreateTargetPayment : PaidNeighbourCreatesTargetPayment → ⊥
paidNeighbourDoesNotCreateTargetPayment ()

acquisitionFailureDoesNotCreateValueAbsence : AcquisitionFailureCreatesValueAbsence → ⊥
acquisitionFailureDoesNotCreateValueAbsence ()

regionEnvelopeDoesNotCreateNamedStateNumeral : RegionEnvelopeCreatesNamedStateNumeral → ⊥
regionEnvelopeDoesNotCreateNamedStateNumeral ()

sameLabelDoesNotCreateSameObservable : SameVariableLabelCreatesSameObservable → ⊥
sameLabelDoesNotCreateSameObservable ()

externalIdentityDoesNotCreateNumericPayment : ExternalIdentityCreatesNumericPayment → ⊥
externalIdentityDoesNotCreateNumericPayment ()

monsterCrossPollinationDoesNotCreateAdKAuthority : MonsterAcquisitionCreatesAdKScientificAuthority → ⊥
monsterCrossPollinationDoesNotCreateAdKAuthority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKCalibrationAcquisitionFrontierBoundary : Set where
  constructor adk-calibration-acquisition-frontier-boundary
  field
    propositionIndexedDebt : Bool
    intermediateGeometryDebtStillOpen : Bool
    figureFiveFreeEnergyDebtClosed : Bool
    forwardKramersRateDebtClosed : Bool
    sameObjectManifestationRequired : Bool
    compatibleObservableRequired : Bool
    exactLocatorRequired : Bool
    valueRoleRequired : Bool
    externalIdentityRequiredForEveryNumericPayment : Bool
    acquisitionGapMeansValueAbsent : Bool
    neighbouringPaymentPaysDebt : Bool
    qidDoiPdbUniProtCreateNumericPayment : Bool
    monsterCrossPollinationTransfersScientificAuthority : Bool
    currentShortestResidual : String
open AdKCalibrationAcquisitionFrontierBoundary public

canonicalAdKCalibrationAcquisitionFrontierBoundary : AdKCalibrationAcquisitionFrontierBoundary
canonicalAdKCalibrationAcquisitionFrontierBoundary =
  adk-calibration-acquisition-frontier-boundary
    true true true true
    true true true true
    false false false false false
    "acquire exact same-object named-state theta1/theta2/dLN cells only where a source manifestation exposes them with the retained Figure-1 observable definition and an exact state locator. Do not reopen already-paid Figure-5 energies/rates; do not infer eta/lambda dLN from neighbouring or region evidence; treat access/search failure as acquisition gap rather than value absence; retain DOI/QID/PDB/UniProt for provenance without making them universal numeric prerequisites."
