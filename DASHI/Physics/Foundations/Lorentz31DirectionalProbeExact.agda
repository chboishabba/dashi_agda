{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact where

-- Source-owned, label-free finite orientation discriminator.
-- Reuses the mathematical question and finite signature owners in
-- DASHI.Algebra.Quantum.LorentzSignatureUniqueness,
-- DASHI.Physics.OrbitSignatureDiscriminant,
-- DASHI.Geometry.Signature31FromIntrinsicShellForcing, and
-- dashifine/40_generate_orbit_profiles.py.
--
-- The input is an independently measured four-axis cone/arrow probe.
-- Neither a "31" code nor a preselected Lorentzian mask occurs in the input.
-- The proof identifies 3 space / 1 time *conditional* on calibration between
-- the observed probe and the actual quadratic principal-axis signs.
-- The record RealizedDynamics is deliberately NOT inhabited here:
-- establishing physical dynamical probes, calibration, four-dimensionality,
-- and continuum transport is the outstanding theorem, not a consequence
-- of finite Boolean enumeration.
--
-- Historical Lorentz, Sylvester inertia, Minkowski, Malament and causal-set
-- results retain their original authorship. DASHI only owns this finite
-- executable-style theorem expression and its integration boundary.
-- No postulates, holes, TERMINATING pragma, or unchecked foreign proof.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

data ⊥ : Set where

data Axis : Set where
  axis0 axis1 axis2 axis3 : Axis

data AxisSign : Set where
  spatial temporal : AxisSign

classifyProbe : Bool → AxisSign
classifyProbe true  = temporal
classifyProbe false = spatial

spatialBit : AxisSign → Nat
spatialBit spatial  = 1
spatialBit temporal = 0

temporalBit : AxisSign → Nat
temporalBit spatial  = 0
temporalBit temporal = 1

record SignatureCounts : Set where
  constructor signature
  field
    spatialCount : Nat
    temporalCount : Nat

-- The count is computed from a supplied (not preselected) sign assignment.
actualAxisCounts : (Axis → AxisSign) → SignatureCounts
actualAxisCounts s =
  signature
    (spatialBit (s axis0) + spatialBit (s axis1) +
     spatialBit (s axis2) + spatialBit (s axis3))
    (temporalBit (s axis0) + temporalBit (s axis1) +
     temporalBit (s axis2) + temporalBit (s axis3))

-- Four possible independently indicated arrow axes. The Boolean probe
-- may come from an experimental/dynamical cone test; these constructors
-- do not insert an orientation/signature code into the measured profile.
data DirectionalProbe (probe : Axis → Bool) : Set where
  arrow0 : probe axis0 ≡ true  → probe axis1 ≡ false →
           probe axis2 ≡ false → probe axis3 ≡ false →
           DirectionalProbe probe
  arrow1 : probe axis0 ≡ false → probe axis1 ≡ true  →
           probe axis2 ≡ false → probe axis3 ≡ false →
           DirectionalProbe probe
  arrow2 : probe axis0 ≡ false → probe axis1 ≡ false →
           probe axis2 ≡ true  → probe axis3 ≡ false →
           DirectionalProbe probe
  arrow3 : probe axis0 ≡ false → probe axis1 ≡ false →
           probe axis2 ≡ false → probe axis3 ≡ true  →
           DirectionalProbe probe

selectedArrow : ∀ {p} → DirectionalProbe p → Axis
selectedArrow (arrow0 _ _ _ _) = axis0
selectedArrow (arrow1 _ _ _ _) = axis1
selectedArrow (arrow2 _ _ _ _) = axis2
selectedArrow (arrow3 _ _ _ _) = axis3

-- Explicit same-observable/physical-quadratic calibration is essential.
-- It cannot be fabricated from the fact that the profile has four axes.
record AxisCalibration
    (probe : Axis → Bool) (sign : Axis → AxisSign) : Set where
  field
    matchesActualQuadratic : ∀ a →
      sign a ≡ classifyProbe (probe a)

-- A genuinely orientation-sensitive 3+1 result, without 31 in input.
-- It is a FINITE CONDITIONAL theorem, not a dynamical/physical emergence proof.
calibratedProbeForcesThreePlusOne :
  ∀ {probe sign} →
  DirectionalProbe probe →
  AxisCalibration probe sign →
  actualAxisCounts sign ≡ signature 3 1
calibratedProbeForcesThreePlusOne (arrow0 h0 h1 h2 h3) c
  rewrite AxisCalibration.matchesActualQuadratic c axis0
        | AxisCalibration.matchesActualQuadratic c axis1
        | AxisCalibration.matchesActualQuadratic c axis2
        | AxisCalibration.matchesActualQuadratic c axis3
        | h0 | h1 | h2 | h3 = refl
calibratedProbeForcesThreePlusOne (arrow1 h0 h1 h2 h3) c
  rewrite AxisCalibration.matchesActualQuadratic c axis0
        | AxisCalibration.matchesActualQuadratic c axis1
        | AxisCalibration.matchesActualQuadratic c axis2
        | AxisCalibration.matchesActualQuadratic c axis3
        | h0 | h1 | h2 | h3 = refl
calibratedProbeForcesThreePlusOne (arrow2 h0 h1 h2 h3) c
  rewrite AxisCalibration.matchesActualQuadratic c axis0
        | AxisCalibration.matchesActualQuadratic c axis1
        | AxisCalibration.matchesActualQuadratic c axis2
        | AxisCalibration.matchesActualQuadratic c axis3
        | h0 | h1 | h2 | h3 = refl
calibratedProbeForcesThreePlusOne (arrow3 h0 h1 h2 h3) c
  rewrite AxisCalibration.matchesActualQuadratic c axis0
        | AxisCalibration.matchesActualQuadratic c axis1
        | AxisCalibration.matchesActualQuadratic c axis2
        | AxisCalibration.matchesActualQuadratic c axis3
        | h0 | h1 | h2 | h3 = refl

threePlusOneDiffersFromOnePlusThree :
  signature 3 1 ≡ signature 1 3 → ⊥
threePlusOneDiffersFromOnePlusThree ()

-- This is the exact physical front door. It binds observed arrow dynamics,
-- a physical quadratic's axis signs, and the same selected state.
-- The caller must provide the actual data, NOT a synthetic 31-coded profile.
record RealizedDynamics : Set₁ where
  field
    State : Set
    step : State → State
    observedConeArrow : State → Axis → Bool
    physicalQuadraticSigns : State → Axis → AxisSign
    selectedState : State
    directionalEvidence : DirectionalProbe (observedConeArrow selectedState)
    sameStateCalibration :
      AxisCalibration
        (observedConeArrow selectedState)
        (physicalQuadraticSigns selectedState)

realizedDynamicsThreePlusOne :
  (d : RealizedDynamics) →
  actualAxisCounts
    (RealizedDynamics.physicalQuadraticSigns d
      (RealizedDynamics.selectedState d))
  ≡ signature 3 1
realizedDynamicsThreePlusOne d =
  calibratedProbeForcesThreePlusOne
    (RealizedDynamics.directionalEvidence d)
    (RealizedDynamics.sameStateCalibration d)
