module DASHI.Physics.Foundations.ResonantFlightHarmonicCyclicBasisExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.ResonantFlightPhaseControlExact as Phase

------------------------------------------------------------------------
-- Generalized helicopter-cyclic representation:
-- a wing trajectory is reconstructed from a finite family of harmonic
-- coefficients indexed by wingbeat phase.
------------------------------------------------------------------------

record HarmonicBasis : Set₁ where
  constructor harmonic-basis
  field
    Harmonic Phase Scalar : Set
    basisCos basisSin : Harmonic → Phase → Scalar

open HarmonicBasis public

record HarmonicCoefficientSet (B : HarmonicBasis) : Set₁ where
  constructor harmonic-coefficient-set
  field
    offset : HarmonicBasis.Scalar B
    cosine sine :
      HarmonicBasis.Harmonic B →
      HarmonicBasis.Scalar B

open HarmonicCoefficientSet public

record HarmonicSynthesis (B : HarmonicBasis) : Set₁ where
  constructor harmonic-synthesis
  field
    State : Set
    synthesize :
      HarmonicCoefficientSet B →
      HarmonicBasis.Phase B →
      State

open HarmonicSynthesis public

record CyclicCoefficientControl
  (PilotInput : Set)
  (B : HarmonicBasis) : Set₁ where
  constructor cyclic-coefficient-control
  field
    coefficients : PilotInput → HarmonicCoefficientSet B
    neutral : PilotInput
    baseline : HarmonicCoefficientSet B
    neutral-is-baseline :
      coefficients neutral ≡ baseline

open CyclicCoefficientControl public

neutralCoefficientsRemainBaseline :
  {PilotInput : Set}
  {B : HarmonicBasis} →
  (C : CyclicCoefficientControl PilotInput B) →
  coefficients C (CyclicCoefficientControl.neutral C) ≡
  CyclicCoefficientControl.baseline C
neutralCoefficientsRemainBaseline C =
  CyclicCoefficientControl.neutral-is-baseline C

------------------------------------------------------------------------
-- Per-DOF coefficient bank: flap/pitch/fold/twist/span may each occupy a
-- different harmonic transfer function while sharing one carrier phase.
------------------------------------------------------------------------

record WingDOFHarmonicBank
  (B : HarmonicBasis) : Set₁ where
  constructor wing-dof-harmonic-bank
  field
    coefficients :
      Phase.WingDOF →
      HarmonicCoefficientSet B

open WingDOFHarmonicBank public
