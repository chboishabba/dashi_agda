module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard

------------------------------------------------------------------------
-- FULL-RESOLUTION FIGURE-5 PANEL-C NUMERIC ACQUISITION
--
-- This owner records only values directly legible in the same-object Figure-5
-- panel-c manifestation supplied for Li-Liu-Ji 2015.  The article caption pays
-- the semantics: state labels below structures are relative free energies in
-- kcal/mol; numbers adjacent to arrows are Kramers-derived transition-rate
-- constants in units of 10^-2 ns^-1, using D ~= 4.47e-3 rad^2/ns.
--
-- Attribution remains separated:
--   article DOI/PMID/PMCID/OpenAlex/QID/UniProt/PDB -> identity/provenance
--   Figure-5 panel-c manifestation                    -> printed numeric values
--   DASHI                                             -> typed acquisition object
--
-- No printed Kramers rate is promoted to an experimentally measured rate.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary

figureFivePanelCLocator : String
figureFivePanelCLocator =
  "Li-Liu-Ji 2015, DOI 10.1016/j.bpj.2015.06.059, Figure 5 panel c; same-object full-resolution source-image/PDF readout"

------------------------------------------------------------------------
-- State free energies.  The source labels are nonnegative relative energies;
-- gamma is the declared zero-reference minimum in the Figure-5 caption.
------------------------------------------------------------------------

data FigureState : Set where
  alpha beta gamma delta epsilon zeta eta lambda : FigureState

record RelativeEnergyTenths : Set where
  constructor relative-energy-tenths
  field
    state : FigureState
    tenthsKcalMol : Nat
    printedReading : String
    sourceLocator : String
    method : String
open RelativeEnergyTenths public

alphaEnergy : RelativeEnergyTenths
alphaEnergy = relative-energy-tenths alpha 1 "DeltaG = 0.1 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

betaEnergy : RelativeEnergyTenths
betaEnergy = relative-energy-tenths beta 0 "DeltaG = 0.0 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

gammaEnergy : RelativeEnergyTenths
gammaEnergy = relative-energy-tenths gamma 0 "DeltaG = 0.0 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout; declared reference minimum"

deltaEnergy : RelativeEnergyTenths
deltaEnergy = relative-energy-tenths delta 6 "DeltaG = 0.6 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

epsilonEnergy : RelativeEnergyTenths
epsilonEnergy = relative-energy-tenths epsilon 16 "DeltaG = 1.6 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

zetaEnergy : RelativeEnergyTenths
zetaEnergy = relative-energy-tenths zeta 12 "DeltaG = 1.2 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

etaEnergy : RelativeEnergyTenths
etaEnergy = relative-energy-tenths eta 7 "DeltaG = 0.7 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

lambdaEnergy : RelativeEnergyTenths
lambdaEnergy = relative-energy-tenths lambda 10 "DeltaG = 1.0 kcal/mol" figureFivePanelCLocator "direct full-resolution source-image readout"

stateEnergies : List RelativeEnergyTenths
stateEnergies =
  alphaEnergy ∷ betaEnergy ∷ gammaEnergy ∷ deltaEnergy ∷
  epsilonEnergy ∷ zetaEnergy ∷ etaEnergy ∷ lambdaEnergy ∷ []

stateEnergyCount : Nat
stateEnergyCount = 8

allEightStateEnergiesPaid : Bool
allEightStateEnergiesPaid = true

------------------------------------------------------------------------
-- Directed Kramers-rate labels.
--
-- Values are stored as hundredths of the DISPLAY UNIT 10^-2 ns^-1.  Example:
-- 8.12 is stored as 812.  Arrow direction is read from the visible arrowhead,
-- not inferred from detailed balance, free energy, path preference or symmetry.
------------------------------------------------------------------------

record DirectedKramersRate : Set where
  constructor directed-kramers-rate
  field
    fromState : FigureState
    toState : FigureState
    hundredthsOfDisplayUnit : Nat
    printedReading : String
    displayUnit : String
    sourceLocator : String
    rateKind : String
open DirectedKramersRate public

rate : FigureState → FigureState → Nat → String → DirectedKramersRate
rate from to n reading =
  directed-kramers-rate from to n reading "10^-2 ns^-1" figureFivePanelCLocator
    "Kramers-derived transition-rate constant; not an experimental kinetic measurement"

-- alpha <-> beta
alphaToBeta = rate alpha beta 812 "8.12"
betaToAlpha = rate beta alpha 685 "6.85"

-- beta <-> gamma
gammaToBeta = rate gamma beta 259 "2.59"
betaToGamma = rate beta gamma 259 "2.59"

-- gamma <-> delta
gammaToDelta = rate gamma delta 266 "2.66"
deltaToGamma = rate delta gamma 732 "7.32"

-- beta <-> epsilon
betaToEpsilon = rate beta epsilon 31 "0.31"
epsilonToBeta = rate epsilon beta 468 "4.68"

-- delta <-> epsilon
epsilonToDelta = rate epsilon delta 1156 "11.56"
deltaToEpsilon = rate delta epsilon 214 "2.14"

-- delta <-> eta
deltaToEta = rate delta eta 284 "2.84"
etaToDelta = rate eta delta 336 "3.36"

-- epsilon <-> zeta
epsilonToZeta = rate epsilon zeta 252 "2.52"
zetaToEpsilon = rate zeta epsilon 128 "1.28"

-- delta <-> zeta
deltaToZeta = rate delta zeta 385 "3.85"
zetaToDelta = rate zeta delta 1060 "10.60"

-- eta <-> zeta
etaToZeta = rate eta zeta 703 "7.03"
zetaToEta = rate zeta eta 1637 "16.37"

-- eta <-> lambda
etaToLambda = rate eta lambda 1357 "13.57"
lambdaToEta = rate lambda eta 2251 "22.51"

directedRates : List DirectedKramersRate
directedRates =
  alphaToBeta ∷ betaToAlpha ∷
  gammaToBeta ∷ betaToGamma ∷
  gammaToDelta ∷ deltaToGamma ∷
  betaToEpsilon ∷ epsilonToBeta ∷
  epsilonToDelta ∷ deltaToEpsilon ∷
  deltaToEta ∷ etaToDelta ∷
  epsilonToZeta ∷ zetaToEpsilon ∷
  deltaToZeta ∷ zetaToDelta ∷
  etaToZeta ∷ zetaToEta ∷
  etaToLambda ∷ lambdaToEta ∷ []

directedRateCount : Nat
directedRateCount = 20

------------------------------------------------------------------------
-- Existing weighted-route forward cells can now be paid directly.
-- The terminal role continues to preserve the equation-xi / Figure-zeta
-- notation history rather than asserting definitional equality.
------------------------------------------------------------------------

alphaBetaForward = alphaToBeta
betaGammaForward = betaToGamma
gammaDeltaForward = gammaToDelta
deltaTerminalForward = deltaToZeta
betaEpsilonForward = betaToEpsilon
epsilonTerminalForward = epsilonToZeta

allSixRouteForwardRatesPaid : Bool
allSixRouteForwardRatesPaid = true

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data FigureValueComesFromDOIIdentityAlone : Set where
data KramersRateIsExperimentalRate : Set where
data RelativeEnergyIsAbsoluteThermodynamicFreeEnergy : Set where
data FigureZetaIsDefinitionallyEquationXi : Set where

data FullPanelNumericsCreateCompleteProteinState : Set where

identityDoesNotCreateFigureValue : FigureValueComesFromDOIIdentityAlone → ⊥
identityDoesNotCreateFigureValue ()

kramersRateDoesNotBecomeExperimental : KramersRateIsExperimentalRate → ⊥
kramersRateDoesNotBecomeExperimental ()

relativeEnergyDoesNotBecomeAbsolute : RelativeEnergyIsAbsoluteThermodynamicFreeEnergy → ⊥
relativeEnergyDoesNotBecomeAbsolute ()

zetaDoesNotBecomeDefinitionallyXi : FigureZetaIsDefinitionallyEquationXi → ⊥
zetaDoesNotBecomeDefinitionallyXi ()

panelDoesNotCreateCompleteProteinState : FullPanelNumericsCreateCompleteProteinState → ⊥
panelDoesNotCreateCompleteProteinState ()

kramersRatesAreExperimental : Bool
kramersRatesAreExperimental = false

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FigureFivePanelCFullNumericBoundary : Set where
  constructor figure-five-panel-c-full-numeric-boundary
  field
    sameObjectPanelPaid : Bool
    allEightStateEnergiesPaidBoundary : Bool
    allTwentyDirectedRatesPaid : Bool
    allSixRouteForwardRatesPaidBoundary : Bool
    stateEnergiesNonnegativeRelativeToGammaReference : Bool
    directionalAssignmentReadFromVisibleArrowheads : Bool
    kramersRatesAreExperimentalBoundary : Bool
    figureZetaEqualsEquationXi : Bool
    articleIdentityAlonePaysNumerics : Bool
    completeProteinStateRecovered : Bool
open FigureFivePanelCFullNumericBoundary public

canonicalFigureFivePanelCFullNumericBoundary : FigureFivePanelCFullNumericBoundary
canonicalFigureFivePanelCFullNumericBoundary =
  figure-five-panel-c-full-numeric-boundary
    true true true true true true
    false false false false
