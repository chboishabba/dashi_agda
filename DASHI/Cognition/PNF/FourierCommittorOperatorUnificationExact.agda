module DASHI.Cognition.PNF.FourierCommittorOperatorUnificationExact where

------------------------------------------------------------------------
-- OPERATOR-ADAPTED FUTURE COORDINATES
--
-- SOURCES ALREADY OWNED BY IMPORTED MODULES:
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted.
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted.
-- Daniel T. Gillespie, "Exact stochastic simulation of coupled chemical
-- reactions", J. Phys. Chem. 81 (1977), 2340--2361.
-- DOI: 10.1021/j100540a008.
--
-- Fourier characters and committors solve different operator equations, but
-- both are distinguished coordinates adapted to dynamics.  The common carrier
-- below records an observable together with the normal form produced when the
-- dynamical operator acts on it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as Cyclo
import DASHI.Biology.Physical.FiniteChemicalMasterGeneratorExact as Chemical
import DASHI.Cognition.PNF.GrokkingTaskCharacterPhaseExact as Character
import DASHI.Cognition.PNF.TaskActionRepresentationGeometryExact as Geometry
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

record OperatorAdaptedCoordinate (State Value : Set) : Set₁ where
  constructor operatorAdaptedCoordinate
  field
    operator : (State → Value) → State → Value
    coordinate : State → Value
    normalForm : State → Value
    adapted : (state : State) →
      operator coordinate state ≡ normalForm state

open OperatorAdaptedCoordinate public

------------------------------------------------------------------------
-- Fourier/character instance: translating the C3 state by phase one turns the
-- coordinate into multiplication by omega.
------------------------------------------------------------------------

Phase : Set
Phase = Wheel.DepthWheelPhase

phaseShiftOperator :
  (Phase → Cyclo.Cyclotomic3) → Phase → Cyclo.Cyclotomic3
phaseShiftOperator f phase =
  f (Character.phaseComposeC3 Wheel.phase-1 phase)

phaseNormalForm : Phase → Cyclo.Cyclotomic3
phaseNormalForm phase = Cyclo.omega Cyclo.*C Cyclo.root phase

fourierCharacterCoordinate : OperatorAdaptedCoordinate Phase Cyclo.Cyclotomic3
fourierCharacterCoordinate = operatorAdaptedCoordinate
  phaseShiftOperator
  Cyclo.root
  phaseNormalForm
  (λ phase →
    Geometry.actionCommutesWithEncoding
      Geometry.c3CyclotomicRepresentation Wheel.phase-1 phase)

fourierCharacterIsOperatorAdapted : (phase : Phase) →
  operator fourierCharacterCoordinate
    (coordinate fourierCharacterCoordinate) phase
  ≡ normalForm fourierCharacterCoordinate phase
fourierCharacterIsOperatorAdapted = adapted fourierCharacterCoordinate

------------------------------------------------------------------------
-- Committor instance: for the continuous-time chemical generator, q is
-- harmonic.  Its normal form is the zero observable rather than an oscillatory
-- eigenvalue multiple.
------------------------------------------------------------------------

chemicalZero : Chemical.ChemicalState → ℚ
chemicalZero state = 0ℚ

committorHarmonicCoordinate :
  OperatorAdaptedCoordinate Chemical.ChemicalState ℚ
committorHarmonicCoordinate = operatorAdaptedCoordinate
  Chemical.generator
  Chemical.committor
  chemicalZero
  Chemical.committorGeneratorHarmonic

committorIsOperatorAdapted : (state : Chemical.ChemicalState) →
  operator committorHarmonicCoordinate
    (coordinate committorHarmonicCoordinate) state
  ≡ normalForm committorHarmonicCoordinate state
committorIsOperatorAdapted = adapted committorHarmonicCoordinate

------------------------------------------------------------------------
-- The shared theorem surface is therefore not "Fourier = committor".  It is:
-- a consumer/task can privilege observables satisfying a simple closed operator
-- equation.  Oscillatory symmetry coordinates and absorbing-event harmonic
-- coordinates are two exact but different instances.
------------------------------------------------------------------------

data OperatorNormalFormKind : Set where
  oscillatoryMultiplicative harmonicZero : OperatorNormalFormKind

coordinateKind :
  ∀ {State Value} → OperatorAdaptedCoordinate State Value → OperatorNormalFormKind → Set
coordinateKind coordinate kind = ⊤

fourierAndCommittorAreDistinctNormalForms :
  oscillatoryMultiplicative ≢ harmonicZero
fourierAndCommittorAreDistinctNormalForms ()
