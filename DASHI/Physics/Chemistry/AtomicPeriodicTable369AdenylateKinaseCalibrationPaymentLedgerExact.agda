module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourcePaidThreeCVEndpointExact as ThreeCV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationProvenanceGraphExact as Provenance

------------------------------------------------------------------------
-- CELL-LEVEL CALIBRATION PAYMENT LEDGER
--
-- The provenance graph records dependency classes globally.  This owner records
-- the current payment state of each concrete numerical consumer cell:
--
--   8 named Figure-state roles x (theta1, theta2, dLN, relative Delta G)
--   + 6 source-paid route edges x Kramers rate.
--
-- Paid endpoint values are retained at the source's approximate precision.
-- Qualitative regions do not become numeric cells.  Every unpaid row carries a
-- next-payment description so archive/supplement acquisition can update one cell
-- without totalising the rest of the graph.
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
-- Canonical paid endpoint objects remain live.
------------------------------------------------------------------------

openEndpoint = ThreeCV.openEndpoint
closedEndpoint = ThreeCV.closedEndpoint
freeEnergyUncertainty = Uncertainty.canonicalAdKMetadynamicsUncertaintyBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary
provenanceGraph = Provenance.calibrationProvenanceGraph

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
alphaEnergy = unpaidCell
  "alpha" relativeFreeEnergyRole
  "Figure 5c state-energy label"
  "BE-META relative free-energy state coordinate"
  "acquire exact same-article Figure/Table locator and numeric alpha relative-energy label; attach approximately 0.5 kcal/mol method uncertainty where applicable"

------------------------------------------------------------------------
-- State cells: beta, gamma, delta, epsilon.
------------------------------------------------------------------------

betaThetaOne = unpaidCell "beta" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific beta theta1 numeric label if the source supplies one"
betaThetaTwo = unpaidCell "beta" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific beta theta2 numeric label if the source supplies one"
betaDLn = unpaidCell "beta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object beta dLN numeric value"
betaEnergy = unpaidCell "beta" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object beta relative-energy label with method uncertainty"

gammaThetaOne = unpaidCell "gamma" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific gamma theta1 numeric label if supplied"
gammaThetaTwo = unpaidCell "gamma" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific gamma theta2 numeric label if supplied"
gammaDLn = unpaidCell "gamma" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object gamma dLN numeric value"
gammaEnergy = paidCell
  "gamma" relativeFreeEnergyRole
  "existing canonical free-energy receipt: gamma zero reference"
  "relative free-energy reference convention"
  "0 relative to the declared source/repository reference"
  "approximately 0.5 kcal/mol metadynamics method error does not alter the chosen zero convention"

deltaThetaOne = unpaidCell "delta" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific delta theta1 numeric label if supplied"
deltaThetaTwo = unpaidCell "delta" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific delta theta2 numeric label if supplied"
deltaDLn = unpaidCell "delta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object delta dLN numeric value"
deltaEnergy = unpaidCell "delta" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object delta relative-energy label with method uncertainty"

epsilonThetaOne = unpaidCell "epsilon" thetaOneRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific epsilon theta1 numeric label if supplied"
epsilonThetaTwo = unpaidCell "epsilon" thetaTwoRole "Figure 5 named-state geometry" "qualitative semi-open/semi-closed region only" "acquire locator-specific epsilon theta2 numeric label if supplied"
epsilonDLn = unpaidCell "epsilon" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object epsilon dLN numeric value"
epsilonEnergy = unpaidCell "epsilon" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object epsilon relative-energy label with method uncertainty"

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

zetaEnergy = unpaidCell "zeta" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object zeta relative-energy label with method uncertainty"

etaThetaOne = unpaidCell "eta" thetaOneRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific eta theta1 numeric label if supplied"
etaThetaTwo = unpaidCell "eta" thetaTwoRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific eta theta2 numeric label if supplied"
etaDLn = unpaidCell "eta" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object eta dLN numeric value"
etaEnergy = unpaidCell "eta" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object eta relative-energy label with method uncertainty"

lambdaThetaOne = unpaidCell "lambda" thetaOneRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific lambda theta1 numeric label if supplied"
lambdaThetaTwo = unpaidCell "lambda" thetaTwoRole "Figure 5 named-state geometry" "qualitative near-closed region only" "acquire locator-specific lambda theta2 numeric label if supplied"
lambdaDLn = unpaidCell "lambda" dLnRole "Figure 5 / supporting material" "three-CV state coordinate" "acquire same-object lambda dLN numeric value"
lambdaEnergy = unpaidCell "lambda" relativeFreeEnergyRole "Figure 5c state-energy label" "BE-META relative free-energy state coordinate" "acquire same-object lambda relative-energy label with method uncertainty"

------------------------------------------------------------------------
-- Edge-rate cells.  The rate role, unit and Kramers calibration are paid;
-- the six visual arrow numerals remain unpaid.
------------------------------------------------------------------------

alphaBetaRate = unpaidCell "alpha->beta" edgeKramersRateRole "Figure 5c alpha->beta arrow" "Kramers-derived rate; display unit 10^-2 ns^-1" "acquire exact same-object arrow numeric label"
betaGammaRate = unpaidCell "beta->gamma" edgeKramersRateRole "Figure 5c beta->gamma arrow" "Kramers-derived rate; display unit 10^-2 ns^-1" "acquire exact same-object arrow numeric label"
gammaDeltaRate = unpaidCell "gamma->delta" edgeKramersRateRole "Figure 5c gamma->delta arrow" "Kramers-derived rate; display unit 10^-2 ns^-1" "acquire exact same-object arrow numeric label"
deltaTerminalRate = unpaidCell "delta->terminal xi/zeta role" edgeKramersRateRole "Figure 5c terminal-route arrow" "Kramers-derived rate; xi/zeta notation history retained" "acquire exact arrow label without collapsing xi and zeta source objects"
betaEpsilonRate = unpaidCell "beta->epsilon" edgeKramersRateRole "Figure 5c beta->epsilon arrow" "Kramers-derived rate; display unit 10^-2 ns^-1" "acquire exact same-object arrow numeric label"
epsilonTerminalRate = unpaidCell "epsilon->terminal xi/zeta role" edgeKramersRateRole "Figure 5c terminal-route arrow" "Kramers-derived rate; xi/zeta notation history retained" "acquire exact arrow label without collapsing xi and zeta source objects"

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
    true true false false false
    true true true true
    false false false false
