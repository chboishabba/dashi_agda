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
-- This owner does not create a second calibration ledger.  It routes the live
-- cells already owned by CalibrationPaymentLedgerExact through an acquisition-
-- debt view inspired by the repository's recent proposition-indexed acquisition
-- work and the Monster 3B acquisition discipline:
--
--   paid neighbouring facts do not pay the target proposition;
--   identifiers do not create the required mathematical/scientific object;
--   same labels do not create same-object identity;
--   source acquisition and theorem/payment promotion are separate gates.
--
-- The Monster owner is a DASHI design donor only.  It supplies no AdK science,
-- source authority, numeric value, or biological identity.
--
-- Live-master correction relative to the earlier roadmap snapshot:
-- Figure-5 panel-c acquisition has already paid all eight printed relative
-- energies and all six forward route-edge Kramers numerics.  Those debts remain
-- represented below as CLOSED receipts.  The active frontier is the named-state
-- intermediate geometry: theta1, theta2 and dLN for beta/gamma/delta/epsilon/
-- eta/lambda, at the semantic precision actually demanded by each consumer.
------------------------------------------------------------------------

data DebtStatus : Set where
  unpaid partiallyPaid paid : DebtStatus

data AcquisitionGapState : Set where
  noDeclaredGap : AcquisitionGapState
  exactLocatorGap : AcquisitionGapState
  sourceAccessGap : AcquisitionGapState
  sourceUnavailableGap : AcquisitionGapState
  observableCompatibilityGap : AcquisitionGapState

data CalibrationDebtCoordinate : Set where
  betaThetaOne betaThetaTwo betaDLn : CalibrationDebtCoordinate
  gammaThetaOne gammaThetaTwo gammaDLn : CalibrationDebtCoordinate
  deltaThetaOne deltaThetaTwo deltaDLn : CalibrationDebtCoordinate
  epsilonThetaOne epsilonThetaTwo epsilonDLn : CalibrationDebtCoordinate
  etaThetaOne etaThetaTwo etaDLn : CalibrationDebtCoordinate
  lambdaThetaOne lambdaThetaTwo lambdaDLn : CalibrationDebtCoordinate
  alphaDeltaG betaDeltaG gammaDeltaG deltaDeltaG epsilonDeltaG zetaDeltaG etaDeltaG lambdaDeltaG : CalibrationDebtCoordinate
  alphaBetaRate betaGammaRate gammaDeltaRate deltaTerminalRate betaEpsilonRate epsilonTerminalRate : CalibrationDebtCoordinate

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

------------------------------------------------------------------------
-- Helpers.
------------------------------------------------------------------------

partialGeometryDebt :
  CalibrationDebtCoordinate →
  Ledger.CalibrationPaymentCell →
  String → String → String →
  CalibrationAcquisitionDebt
partialGeometryDebt coordinate cell proposition observable boundary =
  calibration-acquisition-debt
    coordinate partiallyPaid cell proposition
    "same-object Li-Liu-Ji article text/Figure-5/PMC-attached supplement manifestation"
    observable
    "exact named-state + coordinate locator must identify this cell; a region envelope or neighbouring state is insufficient"
    "same observable definition as Li-Liu-Ji Figure-1 collective variable; source-text or separately receipted figure/supplement readout"
    boundary
    exactLocatorGap
    "DOI/PMID/PMCID/QID/PDB/UniProt remain retained provenance coordinates; none is an additional numeric premise unless required to establish the particular same-object manifestation"

unpaidGeometryDebt :
  CalibrationDebtCoordinate →
  Ledger.CalibrationPaymentCell →
  String → String → String →
  CalibrationAcquisitionDebt
unpaidGeometryDebt coordinate cell proposition observable boundary =
  calibration-acquisition-debt
    coordinate unpaid cell proposition
    "same-object Li-Liu-Ji article/Figure-5/PMC-attached supplement manifestation"
    observable
    "exact named-state + coordinate locator required"
    "same observable definition as Li-Liu-Ji Figure-1 collective variable"
    boundary
    exactLocatorGap
    "external identifiers are provenance/navigation only unless needed to establish same-object manifestation identity"

closedDebt :
  CalibrationDebtCoordinate →
  Ledger.CalibrationPaymentCell →
  String → String →
  CalibrationAcquisitionDebt
closedDebt coordinate cell proposition role =
  calibration-acquisition-debt
    coordinate paid cell proposition
    "same-object full-resolution Li-Liu-Ji Figure-5 panel-c manifestation already acquired"
    role
    "closed: exact printed cell/arrow association is already retained by CalibrationPaymentLedgerExact"
    role
    "paid at source precision; further precision would be a new proposition and new debt"
    noDeclaredGap
    "publication/protein/entity identifiers remain descriptive provenance and do not constitute the numeric payment"

------------------------------------------------------------------------
-- Active named-state geometry debt.
--
-- beta/gamma/delta/epsilon have a source-paid semi-open/semi-closed region and
-- dLN ~16--30 A region-level envelope; eta/lambda have source-paid near-closed
-- qualitative roles but no paid state-specific dLN interval.  'partiallyPaid'
-- therefore means some proposition premises/region constraints are paid, never
-- that the requested named-state numeral may be interpolated.
------------------------------------------------------------------------

betaThetaOneDebt = partialGeometryDebt betaThetaOne Ledger.betaThetaOne
  "numeric theta1(beta) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "beta has qualitative semi-open/semi-closed role; exact theta1(beta) remains unpaid"

betaThetaTwoDebt = partialGeometryDebt betaThetaTwo Ledger.betaThetaTwo
  "numeric theta2(beta) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "beta has qualitative semi-open/semi-closed role; exact theta2(beta) remains unpaid"

betaDLnDebt = partialGeometryDebt betaDLn Ledger.betaDLn
  "numeric dLN(beta)"
  "distance between LID and NMP domain centers of mass"
  "intermediate region dLN ~16--30 A is paid; exact beta dLN is not"

gammaThetaOneDebt = partialGeometryDebt gammaThetaOne Ledger.gammaThetaOne
  "numeric theta1(gamma) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "gamma role and gamma-near structural references are paid; exact theta1(gamma) is not"

gammaThetaTwoDebt = partialGeometryDebt gammaThetaTwo Ledger.gammaThetaTwo
  "numeric theta2(gamma) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "gamma role and gamma-near structural references are paid; exact theta2(gamma) is not"

gammaDLnDebt = partialGeometryDebt gammaDLn Ledger.gammaDLn
  "numeric dLN(gamma)"
  "distance between LID and NMP domain centers of mass"
  "intermediate region dLN ~16--30 A and gamma role are paid; exact gamma dLN is not"

deltaThetaOneDebt = partialGeometryDebt deltaThetaOne Ledger.deltaThetaOne
  "numeric theta1(delta) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "delta intermediate role is paid; exact theta1(delta) remains unpaid"

deltaThetaTwoDebt = partialGeometryDebt deltaThetaTwo Ledger.deltaThetaTwo
  "numeric theta2(delta) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "delta semi-open NMP role is paid; exact theta2(delta) remains unpaid"

deltaDLnDebt = partialGeometryDebt deltaDLn Ledger.deltaDLn
  "numeric dLN(delta)"
  "distance between LID and NMP domain centers of mass"
  "intermediate region dLN ~16--30 A is paid; exact delta dLN is not"

epsilonThetaOneDebt = partialGeometryDebt epsilonThetaOne Ledger.epsilonThetaOne
  "numeric theta1(epsilon) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "epsilon alternative-route role is paid; exact theta1(epsilon) remains unpaid"

epsilonThetaTwoDebt = partialGeometryDebt epsilonThetaTwo Ledger.epsilonThetaTwo
  "numeric theta2(epsilon) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "epsilon alternative-route role is paid; exact theta2(epsilon) remains unpaid"

epsilonDLnDebt = partialGeometryDebt epsilonDLn Ledger.epsilonDLn
  "numeric dLN(epsilon)"
  "distance between LID and NMP domain centers of mass"
  "intermediate region dLN ~16--30 A is paid; exact epsilon dLN is not"

etaThetaOneDebt = partialGeometryDebt etaThetaOne Ledger.etaThetaOne
  "numeric theta1(eta) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "eta near-closed qualitative region is paid; exact theta1(eta) remains unpaid"

etaThetaTwoDebt = partialGeometryDebt etaThetaTwo Ledger.etaThetaTwo
  "numeric theta2(eta) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "eta near-closed qualitative region is paid; exact theta2(eta) remains unpaid"

etaDLnDebt = unpaidGeometryDebt etaDLn Ledger.etaDLn
  "numeric dLN(eta)"
  "distance between LID and NMP domain centers of mass"
  "near-closed role alone supplies no state-specific dLN numeral or interval"

lambdaThetaOneDebt = partialGeometryDebt lambdaThetaOne Ledger.lambdaThetaOne
  "numeric theta1(lambda) at source-paid precision"
  "theta1 LID/hinge/CORE backbone-center-of-mass construction"
  "lambda near-closed qualitative region is paid; exact theta1(lambda) remains unpaid"

lambdaThetaTwoDebt = partialGeometryDebt lambdaThetaTwo Ledger.lambdaThetaTwo
  "numeric theta2(lambda) at source-paid precision"
  "theta2 NMP/CORE/hinge backbone-center-of-mass construction"
  "lambda near-closed qualitative region is paid; exact theta2(lambda) remains unpaid"

lambdaDLnDebt = unpaidGeometryDebt lambdaDLn Ledger.lambdaDLn
  "numeric dLN(lambda)"
  "distance between LID and NMP domain centers of mass"
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
-- Closed debts: live master already paid Figure-5 energies and the six forward
-- Kramers numerics.  Keeping them here prevents stale roadmaps from reopening
-- them merely because an earlier branch snapshot still called them unpaid.
------------------------------------------------------------------------

alphaEnergyDebt = closedDebt alphaDeltaG Ledger.alphaEnergy "Delta G(alpha) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
betaEnergyDebt = closedDebt betaDeltaG Ledger.betaEnergy "Delta G(beta) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
gammaEnergyDebt = closedDebt gammaDeltaG Ledger.gammaEnergy "Delta G(gamma) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
deltaEnergyDebt = closedDebt deltaDeltaG Ledger.deltaEnergy "Delta G(delta) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
epsilonEnergyDebt = closedDebt epsilonDeltaG Ledger.epsilonEnergy "Delta G(epsilon) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
zetaEnergyDebt = closedDebt zetaDeltaG Ledger.zetaEnergy "Delta G(zeta) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
etaEnergyDebt = closedDebt etaDeltaG Ledger.etaEnergy "Delta G(eta) relative Figure-5 reference" "BE-META relative free-energy state coordinate"
lambdaEnergyDebt = closedDebt lambdaDeltaG Ledger.lambdaEnergy "Delta G(lambda) relative Figure-5 reference" "BE-META relative free-energy state coordinate"

alphaBetaRateDebt = closedDebt alphaBetaRate Ledger.alphaBetaRate "Kramers rate alpha->beta" "Kramers-derived directed rate; not experimental kinetics"
betaGammaRateDebt = closedDebt betaGammaRate Ledger.betaGammaRate "Kramers rate beta->gamma" "Kramers-derived directed rate; not experimental kinetics"
gammaDeltaRateDebt = closedDebt gammaDeltaRate Ledger.gammaDeltaRate "Kramers rate gamma->delta" "Kramers-derived directed rate; not experimental kinetics"
deltaTerminalRateDebt = closedDebt deltaTerminalRate Ledger.deltaTerminalRate "Kramers rate delta->terminal zeta role" "Kramers-derived directed rate; xi/zeta notation history retained"
betaEpsilonRateDebt = closedDebt betaEpsilonRate Ledger.betaEpsilonRate "Kramers rate beta->epsilon" "Kramers-derived directed rate; not experimental kinetics"
epsilonTerminalRateDebt = closedDebt epsilonTerminalRate Ledger.epsilonTerminalRate "Kramers rate epsilon->terminal zeta role" "Kramers-derived directed rate; xi/zeta notation history retained"

closedFigureFiveDebts : List CalibrationAcquisitionDebt
closedFigureFiveDebts =
  alphaEnergyDebt ∷ betaEnergyDebt ∷ gammaEnergyDebt ∷ deltaEnergyDebt ∷
  epsilonEnergyDebt ∷ zetaEnergyDebt ∷ etaEnergyDebt ∷ lambdaEnergyDebt ∷
  alphaBetaRateDebt ∷ betaGammaRateDebt ∷ gammaDeltaRateDebt ∷
  deltaTerminalRateDebt ∷ betaEpsilonRateDebt ∷ epsilonTerminalRateDebt ∷ []

calibrationAcquisitionFrontier : List CalibrationAcquisitionDebt
calibrationAcquisitionFrontier = activeGeometryDebts ++ closedFigureFiveDebts

------------------------------------------------------------------------
-- Least-privilege numeric promotion rule.
--
-- A future numeric payment must carry witnesses for the four facts actually
-- consumed by the numeric promotion.  DOI/QID/PDB/UniProt are deliberately not
-- fields of this receipt.  They remain in the attribution/snowball layer and are
-- consulted only when a particular same-object manifestation question needs them.
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
-- Reused acquisition / attribution surfaces and Monster design donor.
------------------------------------------------------------------------

supportingMaterialBoundary : Manifestation.SupportingMaterialManifestationBoundary
supportingMaterialBoundary = Manifestation.canonicalSupportingMaterialManifestationBoundary

guardedAcquisitionBoundary : Guard.GuardedCalibrationAcquisitionBoundary
guardedAcquisitionBoundary = Guard.canonicalGuardedCalibrationAcquisitionBoundary

articleAttributionEnvelope = Attribution.canonicalCalibrationAttributionBoundary

collectiveVariableBoundary = CV.canonicalCollectiveVariableDefinitionBoundary

intermediateGeometryBoundary = Intermediate.canonicalIntermediateGeometryTextBoundary

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
