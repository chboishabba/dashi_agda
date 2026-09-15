module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureSixPanelCFullNumericAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact as Guard

------------------------------------------------------------------------
-- FULL-RESOLUTION FIGURE-6 PANEL-C NUMERIC ACQUISITION
--
-- Li-Liu-Ji Figure 6 is the ligand-bound BE-META analogue of Figure 5.
-- The same-object PDF/source rendering makes all eight printed relative free
-- energies and all sixteen visible directed Kramers labels readable.
--
-- The caption pays the semantics:
--   * relative state energies are in kcal/mol;
--   * arrow labels are Kramers-derived transition-rate constants;
--   * display unit is 10^-2 ns^-1;
--   * D ~= 5.13e-4 rad^2/ns is the ligand-bound diffusion calibration.
--
-- One alpha_L -> beta_L reverse-direction partner is printed as 9.34 x 10^-3.
-- We retain that literal printed coefficient rather than silently normalizing it
-- into the common decimal representation or guessing a typesetting convention.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Sparse.liLiuJi2015Source

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

attributionEnvelope = Attr.canonicalAdKCalibrationAttributionBoundary
acquisitionGuard = Guard.canonicalGuardedCalibrationAcquisitionBoundary

figureSixPanelCLocator : String
figureSixPanelCLocator =
  "Li-Liu-Ji 2015, DOI 10.1016/j.bpj.2015.06.059, Figure 6 panel c; same-object full-resolution PDF/source-image readout"

------------------------------------------------------------------------
-- Ligand-bound state energies.
------------------------------------------------------------------------

data LigandBoundFigureState : Set where
  alphaL betaL gammaL deltaL epsilonL zetaL muL lambdaL : LigandBoundFigureState

record RelativeEnergyTenths : Set where
  constructor relative-energy-tenths
  field
    state : LigandBoundFigureState
    tenthsKcalMol : Nat
    printedReading : String
    sourceLocator : String
    method : String
open RelativeEnergyTenths public

alphaLEnergy = relative-energy-tenths alphaL 80 "DeltaG = 8.0 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
betaLEnergy = relative-energy-tenths betaL 37 "DeltaG = 3.7 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
gammaLEnergy = relative-energy-tenths gammaL 28 "DeltaG = 2.8 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
deltaLEnergy = relative-energy-tenths deltaL 8 "DeltaG = 0.8 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
epsilonLEnergy = relative-energy-tenths epsilonL 41 "DeltaG = 4.1 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
zetaLEnergy = relative-energy-tenths zetaL 9 "DeltaG = 0.9 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
muLEnergy = relative-energy-tenths muL 33 "DeltaG = 3.3 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout"
lambdaLEnergy = relative-energy-tenths lambdaL 0 "DeltaG = 0.0 kcal/mol" figureSixPanelCLocator "direct full-resolution source-image/PDF readout; declared reference minimum"

stateEnergies : List RelativeEnergyTenths
stateEnergies =
  alphaLEnergy ∷ betaLEnergy ∷ gammaLEnergy ∷ deltaLEnergy ∷
  epsilonLEnergy ∷ zetaLEnergy ∷ muLEnergy ∷ lambdaLEnergy ∷ []

stateEnergyCount : Nat
stateEnergyCount = 8

allEightStateEnergiesPaid : Bool
allEightStateEnergiesPaid = true

------------------------------------------------------------------------
-- Directed Kramers-rate labels.
--
-- Decimal values are retained as printed strings. For ordinary decimal labels,
-- hundredthsOfDisplayUnit stores the printed coefficient x 100.  The exceptional
-- betaL->alphaL label is printed explicitly as 9.34 x 10^-3 and is therefore
-- retained in a separate literal field without arithmetic reinterpretation.
------------------------------------------------------------------------

record DirectedKramersRate : Set where
  constructor directed-kramers-rate
  field
    fromState : LigandBoundFigureState
    toState : LigandBoundFigureState
    printedReading : String
    displayUnit : String
    sourceLocator : String
    rateKind : String
open DirectedKramersRate public

rate : LigandBoundFigureState → LigandBoundFigureState → String → DirectedKramersRate
rate from to reading =
  directed-kramers-rate from to reading "10^-2 ns^-1" figureSixPanelCLocator
    "Kramers-derived transition-rate constant; not an experimental kinetic measurement"

-- alpha_L <-> beta_L
alphaLToBetaL = rate alphaL betaL "13.28"
betaLToAlphaL = rate betaL alphaL "9.34 x 10^-3"

-- beta_L <-> gamma_L
betaLToGammaL = rate betaL gammaL "1.37"
gammaLToBetaL = rate gammaL betaL "0.30"

-- gamma_L <-> delta_L
gammaLToDeltaL = rate gammaL deltaL "4.17"
deltaLToGammaL = rate deltaL gammaL "0.14"

-- gamma_L <-> epsilon_L
gammaLToEpsilonL = rate gammaL epsilonL "0.17"
epsilonLToGammaL = rate epsilonL gammaL "1.53"

-- delta_L <-> zeta_L
deltaLToZetaL = rate deltaL zetaL "1.11"
zetaLToDeltaL = rate zetaL deltaL "1.32"

-- zeta_L <-> lambda_L
zetaLToLambdaL = rate zetaL lambdaL "2.53"
lambdaLToZetaL = rate lambdaL zetaL "0.55"

-- zeta_L <-> mu_L
zetaLToMuL = rate zetaL muL "0.08"
muLToZetaL = rate muL zetaL "4.40"

-- epsilon_L <-> mu_L
-- Upper curved dashed arrow points epsilon_L -> mu_L; lower returns mu_L -> epsilon_L.
epsilonLToMuL = rate epsilonL muL "1.07"
muLToEpsilonL = rate muL epsilonL "0.28"

directedRates : List DirectedKramersRate
directedRates =
  alphaLToBetaL ∷ betaLToAlphaL ∷
  betaLToGammaL ∷ gammaLToBetaL ∷
  gammaLToDeltaL ∷ deltaLToGammaL ∷
  gammaLToEpsilonL ∷ epsilonLToGammaL ∷
  deltaLToZetaL ∷ zetaLToDeltaL ∷
  zetaLToLambdaL ∷ lambdaLToZetaL ∷
  zetaLToMuL ∷ muLToZetaL ∷
  epsilonLToMuL ∷ muLToEpsilonL ∷ []

directedRateCount : Nat
directedRateCount = 16

allDirectedRateLabelsPaid : Bool
allDirectedRateLabelsPaid = true

------------------------------------------------------------------------
-- Source-role and WrongType firewalls.
------------------------------------------------------------------------

data FigureSixValueComesFromIdentityMetadata : Set where
data LigandBoundKramersRateIsExperimentalRate : Set where
data FigureSixRelativeEnergyIsAbsoluteThermodynamics : Set where
data SameGreekLetterAcrossLigandContextsMeansSameState : Set where

data FigureSixPanelCreatesCompleteLigandMechanism : Set where

identityDoesNotCreateFigureSixValue : FigureSixValueComesFromIdentityMetadata → ⊥
identityDoesNotCreateFigureSixValue ()

kramersRateDoesNotBecomeExperimental : LigandBoundKramersRateIsExperimentalRate → ⊥
kramersRateDoesNotBecomeExperimental ()

relativeEnergyDoesNotBecomeAbsolute : FigureSixRelativeEnergyIsAbsoluteThermodynamics → ⊥
relativeEnergyDoesNotBecomeAbsolute ()

sameLetterDoesNotCreateCrossContextIdentity : SameGreekLetterAcrossLigandContextsMeansSameState → ⊥
sameLetterDoesNotCreateCrossContextIdentity ()

panelDoesNotCreateCompleteMechanism : FigureSixPanelCreatesCompleteLigandMechanism → ⊥
panelDoesNotCreateCompleteMechanism ()

kramersRatesAreExperimental : Bool
kramersRatesAreExperimental = false

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FigureSixPanelCFullNumericBoundary : Set where
  constructor figure-six-panel-c-full-numeric-boundary
  field
    sameObjectPanelPaid : Bool
    allEightStateEnergiesPaidBoundary : Bool
    allSixteenDirectedRatesPaid : Bool
    ligandBoundDiffusionCalibrationSourcePaid : Bool
    literalExceptionalRateReadingRetained : Bool
    kramersRatesAreExperimentalBoundary : Bool
    sameGreekLetterCreatesCrossContextIdentity : Bool
    identityMetadataAlonePaysNumerics : Bool
    completeLigandMechanismRecovered : Bool
open FigureSixPanelCFullNumericBoundary public

canonicalFigureSixPanelCFullNumericBoundary : FigureSixPanelCFullNumericBoundary
canonicalFigureSixPanelCFullNumericBoundary =
  figure-six-panel-c-full-numeric-boundary
    true true true true true
    false false false false
