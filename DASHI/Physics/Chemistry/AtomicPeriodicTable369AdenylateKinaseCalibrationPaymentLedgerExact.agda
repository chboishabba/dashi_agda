module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact as ThreeCV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphExact as Provenance
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact as Full

------------------------------------------------------------------------
-- CELL-LEVEL CALIBRATION PAYMENT LEDGER
--
-- The provenance graph records dependency classes globally. This owner records
-- the current payment state of each concrete numerical consumer cell:
--
--   8 named Figure-state roles x (theta1, theta2, dLN, relative Delta G)
--   + 6 source-paid forward route edges x Kramers rate.
--
-- Figure-5 panel c now pays all eight printed relative free energies and all six
-- forward rate labels used by the existing route graph. Intermediate named-state
-- theta/dLN cells remain unpaid unless independently source-located.
------------------------------------------------------------------------

data CalibrationCoordinateRole : Set where
  thetaOneRole thetaTwoRole dLnRole relativeFreeEnergyRole edgeKramersRateRole :
    CalibrationCoordinateRole

data CellPaymentStatus : Set where
  paidFromSourceText : CellPaymentStatus
  paidBySourceFactComposition : CellPaymentStatus
  unpaidAwaitingLocatorSpecificReceipt : CellPaymentStatus

record CalibrationPaymentCell : Set where
  constructor calibration-payment-cell
  field
    subjectReference : String
    coordinateRole : CalibrationCoordinateRole
    paymentStatus : CellPaymentStatus
    sourceLocator : String
    sourceRole : String
    valueReading : String
    uncertaintyReading : String
    nextPayment : String
    externalIdentityAlonePaysValue : Bool
open CalibrationPaymentCell public

paidCell :
  String → CalibrationCoordinateRole → String → String → String → String →
  CalibrationPaymentCell
paidCell subject role locator sourceRole value uncertainty =
  calibration-payment-cell
    subject role paidFromSourceText locator sourceRole value uncertainty
    "already source-paid at the recorded semantic strength; further precision requires a new source receipt"
    false

composedPaidCell :
  String → CalibrationCoordinateRole → String → String → String → String →
  CalibrationPaymentCell
composedPaidCell subject role locator sourceRole value uncertainty =
  calibration-payment-cell
    subject role paidBySourceFactComposition locator sourceRole value uncertainty
    "same-object composition is paid; further precision or a different state identity requires a new receipt"
    false

unpaidCell :
  String → CalibrationCoordinateRole → String → String → String →
  CalibrationPaymentCell
unpaidCell subject role locator sourceRole next =
  calibration-payment-cell
    subject role unpaidAwaitingLocatorSpecificReceipt locator sourceRole
    "UNPAID" "unresolved" next false

------------------------------------------------------------------------
-- Canonical paid endpoint and Figure-5 objects remain live.
------------------------------------------------------------------------

openEndpoint = ThreeCV.openEndpoint
closedEndpoint = ThreeCV.closedEndpoint
freeEnergyUncertainty = Uncertainty.canonicalAdKMetadynamicsUncertaintyBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary
provenanceGraph = Provenance.calibrationProvenanceGraph
fullFigureFivePanelC = Full.canonicalFigureFivePanelCFullNumericBoundary

figureFivePanelCLocator : String
figureFivePanelCLocator = Full.figureFivePanelCLocator

figureFiveEnergyUncertainty : String
figureFiveEnergyUncertainty =
  "source reports approximately 0.5 kcal/mol metadynamics free-energy error; printed panel-c value retained at source precision"

figureFiveRateUncertainty : String
figureFiveRateUncertainty =
  "printed Kramers-derived rate at Figure-5 precision; no experimental-rate uncertainty is manufactured"

------------------------------------------------------------------------
-- State cells: alpha.
------------------------------------------------------------------------

alphaThetaOne : CalibrationPaymentCell
alphaThetaOne = composedPaidCell
  "alpha / open endpoint / 4AKE" thetaOneRole
  "Li-Liu-Ji endpoint text/Figure-5 open-role composition"
  "same-article endpoint geometry" "approximately 95 degrees"
  "printed approximate endpoint value"

alphaThetaTwo : CalibrationPaymentCell
alphaThetaTwo = composedPaidCell
  "alpha / open endpoint / 4AKE" thetaTwoRole
  "Li-Liu-Ji endpoint text/Figure-5 open-role composition"
  "same-article endpoint geometry" "approximately 61 degrees"
  "printed approximate endpoint value"

alphaDLn : CalibrationPaymentCell
alphaDLn = paidCell
  "alpha / open endpoint / 4AKE" dLnRole
  "Li-Liu-Ji Materials and Methods: dLN^O approximately 38 A in 4AKE"
  "article-text endpoint geometry" "approximately 38 angstrom"
  "printed approximate endpoint value"

alphaEnergy : CalibrationPaymentCell
alphaEnergy = paidCell
  "alpha" relativeFreeEnergyRole figureFivePanelCLocator
  "BE-META Figure-5 panel-c relative free-energy state coordinate"
  "0.1 kcal/mol" figureFiveEnergyUncertainty

------------------------------------------------------------------------
-- State cells: beta, gamma, delta, epsilon.
------------------------------------------------------------------------

betaThetaOne = unpaidCell "beta" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific beta theta1 numeric label if the source supplies one"
betaThetaTwo = unpaidCell "beta" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific beta theta2 numeric label if the source supplies one"
betaDLn = unpaidCell "beta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object beta dLN numeric value"
betaEnergy = paidCell "beta" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate" "0.0 kcal/mol" figureFiveEnergyUncertainty

gammaThetaOne = unpaidCell "gamma" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific gamma theta1 numeric label if supplied"
gammaThetaTwo = unpaidCell "gamma" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific gamma theta2 numeric label if supplied"
gammaDLn = unpaidCell "gamma" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object gamma dLN numeric value"
gammaEnergy = paidCell
  "gamma" relativeFreeEnergyRole figureFivePanelCLocator
  "Figure-5 declared relative free-energy reference minimum"
  "0.0 kcal/mol" "zero-reference convention; method uncertainty does not alter the chosen reference value"

deltaThetaOne = unpaidCell "delta" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific delta theta1 numeric label if supplied"
deltaThetaTwo = unpaidCell "delta" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific delta theta2 numeric label if supplied"
deltaDLn = unpaidCell "delta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object delta dLN numeric value"
deltaEnergy = paidCell "delta" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate" "0.6 kcal/mol" figureFiveEnergyUncertainty

epsilonThetaOne = unpaidCell "epsilon" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific epsilon theta1 numeric label if supplied"
epsilonThetaTwo = unpaidCell "epsilon" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific epsilon theta2 numeric label if supplied"
epsilonDLn = unpaidCell "epsilon" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object epsilon dLN numeric value"
epsilonEnergy = paidCell "epsilon" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate" "1.6 kcal/mol" figureFiveEnergyUncertainty

------------------------------------------------------------------------
-- State cells: zeta terminal/closed role, eta and lambda.
------------------------------------------------------------------------

zetaThetaOne : CalibrationPaymentCell
zetaThetaOne = composedPaidCell
  "zeta / closed Figure-state role / 1AKE endpoint" thetaOneRole
  "Li-Liu-Ji endpoint text/Figure-5 closed-role composition"
  "same-article endpoint geometry; does not identify equation-xi definitionally"
  "approximately 68 degrees" "printed approximate endpoint value"

zetaThetaTwo : CalibrationPaymentCell
zetaThetaTwo = composedPaidCell
  "zeta / closed Figure-state role / 1AKE endpoint" thetaTwoRole
  "Li-Liu-Ji endpoint text/Figure-5 closed-role composition"
  "same-article endpoint geometry; does not identify equation-xi definitionally"
  "approximately 28 degrees" "printed approximate endpoint value"

zetaDLn : CalibrationPaymentCell
zetaDLn = paidCell
  "zeta / closed Figure-state role / 1AKE endpoint" dLnRole
  "Li-Liu-Ji Materials and Methods: dLN^C approximately 20 A in 1AKE"
  "article-text closed endpoint geometry; role-level use does not assert xi=zeta"
  "approximately 20 angstrom" "printed approximate endpoint value"

zetaEnergy = paidCell "zeta" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate; Figure-zeta role retained separately from equation-xi notation" "1.2 kcal/mol" figureFiveEnergyUncertainty

etaThetaOne = unpaidCell "eta" thetaOneRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific eta theta1 numeric label if supplied"
etaThetaTwo = unpaidCell "eta" thetaTwoRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific eta theta2 numeric label if supplied"
etaDLn = unpaidCell "eta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object eta dLN numeric value"
etaEnergy = paidCell "eta" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate" "0.7 kcal/mol" figureFiveEnergyUncertainty

lambdaThetaOne = unpaidCell "lambda" thetaOneRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific lambda theta1 numeric label if supplied"
lambdaThetaTwo = unpaidCell "lambda" thetaTwoRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific lambda theta2 numeric label if supplied"
lambdaDLn = unpaidCell "lambda" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object lambda dLN numeric value"
lambdaEnergy = paidCell "lambda" relativeFreeEnergyRole figureFivePanelCLocator "BE-META Figure-5 panel-c relative free-energy state coordinate" "1.0 kcal/mol" figureFiveEnergyUncertainty

------------------------------------------------------------------------
-- Forward route-edge rate cells. The full-resolution same-object panel now
-- pays the arrowhead/value association used by the six-edge route graph.
------------------------------------------------------------------------

alphaBetaRate = paidCell "alpha->beta" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 directed rate; display unit 10^-2 ns^-1" "8.12 x 10^-2 ns^-1" figureFiveRateUncertainty
betaGammaRate = paidCell "beta->gamma" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 directed rate; display unit 10^-2 ns^-1" "2.59 x 10^-2 ns^-1" figureFiveRateUncertainty
gammaDeltaRate = paidCell "gamma->delta" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 directed rate; display unit 10^-2 ns^-1" "2.66 x 10^-2 ns^-1" figureFiveRateUncertainty
deltaTerminalRate = paidCell "delta->terminal zeta-role; equation-xi notation history retained" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 delta->zeta directed rate; role bridge does not assert xi=zeta" "3.85 x 10^-2 ns^-1" figureFiveRateUncertainty
betaEpsilonRate = paidCell "beta->epsilon" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 directed rate; display unit 10^-2 ns^-1" "0.31 x 10^-2 ns^-1" figureFiveRateUncertainty
epsilonTerminalRate = paidCell "epsilon->terminal zeta-role; equation-xi notation history retained" edgeKramersRateRole figureFivePanelCLocator "Kramers-derived Figure-5 epsilon->zeta directed rate; role bridge does not assert xi=zeta" "2.52 x 10^-2 ns^-1" figureFiveRateUncertainty

stateCells : List CalibrationPaymentCell
stateCells =
  alphaThetaOne ∷ alphaThetaTwo ∷ alphaDLn ∷ alphaEnergy ∷
  betaThetaOne ∷ betaThetaTwo ∷ betaDLn ∷ betaEnergy ∷
  gammaThetaOne ∷ gammaThetaTwo ∷ gammaDLn ∷ gammaEnergy ∷
  deltaThetaOne ∷ deltaThetaTwo ∷ deltaDLn ∷ deltaEnergy ∷
  epsilonThetaOne ∷ epsilonThetaTwo ∷ epsilonDLn ∷ epsilonEnergy ∷
  zetaThetaOne ∷ zetaThetaTwo ∷ zetaDLn ∷ zetaEnergy ∷
  etaThetaOne ∷ etaThetaTwo ∷ etaDLn ∷ etaEnergy ∷
  lambdaThetaOne ∷ lambdaThetaTwo ∷ lambdaDLn ∷ lambdaEnergy ∷ []

edgeRateCells : List CalibrationPaymentCell
edgeRateCells =
  alphaBetaRate ∷ betaGammaRate ∷ gammaDeltaRate ∷ deltaTerminalRate ∷
  betaEpsilonRate ∷ epsilonTerminalRate ∷ []

calibrationPaymentLedger : List CalibrationPaymentCell
calibrationPaymentLedger = stateCells ++ edgeRateCells

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data PaidEndpointCreatesIntermediateTable : Set where
data UncertaintyCreatesMissingEnergy : Set where
data IdentityCreatesNumericPayment : Set where
data LedgerCompletenessCreatesPhysicalCompleteness : Set where

paidEndpointDoesNotCreateIntermediateTable : PaidEndpointCreatesIntermediateTable → ⊥
paidEndpointDoesNotCreateIntermediateTable ()

uncertaintyDoesNotCreateMissingEnergy : UncertaintyCreatesMissingEnergy → ⊥
uncertaintyDoesNotCreateMissingEnergy ()

identityDoesNotCreateNumericPayment : IdentityCreatesNumericPayment → ⊥
identityDoesNotCreateNumericPayment ()

ledgerCompletenessDoesNotCreatePhysicalCompleteness : LedgerCompletenessCreatesPhysicalCompleteness → ⊥
ledgerCompletenessDoesNotCreatePhysicalCompleteness ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKCalibrationPaymentLedgerBoundary : Set where
  constructor adk-calibration-payment-ledger-boundary
  field
    endpointThreeCVCellsPaid : Bool
    gammaZeroReferencePaid : Bool
    intermediateDLnCellsPaid : Bool
    intermediateFreeEnergyCellsPaid : Bool
    perEdgeKramersNumericsPaid : Bool
    everyCellCarriesSourceRole : Bool
    everyUnpaidCellCarriesNextPayment : Bool
    ledgerReusesGuardedAcquisition : Bool
    ledgerReusesProvenanceGraph : Bool
    paidEndpointCreatesIntermediateTable : Bool
    uncertaintyCreatesMissingEnergy : Bool
    identityCreatesNumericPayment : Bool
    ledgerIsCompletePhysicalStateModel : Bool
open AdKCalibrationPaymentLedgerBoundary public

canonicalAdKCalibrationPaymentLedgerBoundary : AdKCalibrationPaymentLedgerBoundary
canonicalAdKCalibrationPaymentLedgerBoundary =
  adk-calibration-payment-ledger-boundary
    true true false true true
    true true true true
    false false false false
