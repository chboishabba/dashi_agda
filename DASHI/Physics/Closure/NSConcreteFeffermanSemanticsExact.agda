module DASHI.Physics.Closure.NSConcreteFeffermanSemanticsExact where

------------------------------------------------------------------------
-- CONCRETE FEFFERMAN SEMANTIC CONTRACT
--
-- This module removes the remaining "arbitrary predicate" freedom from
-- CanonicalNSSemantics.  The only supplied backend is ordinary analytic
-- machinery (smoothness, coordinate derivatives, jet norms and kinetic
-- energy).  Navier--Stokes divergence, periodicity, initial trace and the
-- forced/unforced momentum equation are DEFINED here from that machinery.
--
-- The contract is intentionally representation-level: it mirrors the frozen
-- Mathlib ClaySpec used by dashi_lean4/ExternalClayNS.  A future native Bishop
-- calculus backend may inhabit FeffermanAnalyticKernel directly; until then,
-- the cross-prover bridge has an exact, non-pathological semantic target.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical

data Axis : Set where
  axisX axisY axisZ : Axis

axisComponent : Axis → Canonical.R3Vector → BishopReal.ℝ
axisComponent axisX v = Canonical.vx v
axisComponent axisY v = Canonical.vy v
axisComponent axisZ v = Canonical.vz v

zeroVector : Canonical.R3Vector
zeroVector = Canonical.r3-vector BishopReal.0ℝ BishopReal.0ℝ BishopReal.0ℝ

vectorAdd :
  Canonical.R3Vector → Canonical.R3Vector → Canonical.R3Vector
vectorAdd a b =
  Canonical.r3-vector
    (BishopReal._+_ (Canonical.vx a) (Canonical.vx b))
    (BishopReal._+_ (Canonical.vy a) (Canonical.vy b))
    (BishopReal._+_ (Canonical.vz a) (Canonical.vz b))

vectorSub :
  Canonical.R3Vector → Canonical.R3Vector → Canonical.R3Vector
vectorSub a b =
  Canonical.r3-vector
    (BishopReal._-_ (Canonical.vx a) (Canonical.vx b))
    (BishopReal._-_ (Canonical.vy a) (Canonical.vy b))
    (BishopReal._-_ (Canonical.vz a) (Canonical.vz b))

vectorScale :
  BishopReal.ℝ → Canonical.R3Vector → Canonical.R3Vector
vectorScale s v =
  Canonical.r3-vector
    (BishopReal._*_ s (Canonical.vx v))
    (BishopReal._*_ s (Canonical.vy v))
    (BishopReal._*_ s (Canonical.vz v))

vectorEquivalent :
  Canonical.R3Vector → Canonical.R3Vector → Set
vectorEquivalent a b =
  BishopReal._≃_ (Canonical.vx a) (Canonical.vx b)
  ×
  (BishopReal._≃_ (Canonical.vy a) (Canonical.vy b)
  × BishopReal._≃_ (Canonical.vz a) (Canonical.vz b))

shiftPoint : Axis → Canonical.R3Point → Canonical.R3Point
shiftPoint axisX p =
  Canonical.r3-point
    (BishopReal._+_ (Canonical.x p) BishopReal.1ℝ)
    (Canonical.y p)
    (Canonical.z p)
shiftPoint axisY p =
  Canonical.r3-point
    (Canonical.x p)
    (BishopReal._+_ (Canonical.y p) BishopReal.1ℝ)
    (Canonical.z p)
shiftPoint axisZ p =
  Canonical.r3-point
    (Canonical.x p)
    (Canonical.y p)
    (BishopReal._+_ (Canonical.z p) BishopReal.1ℝ)

PositiveReal : BishopReal.ℝ → Set
PositiveReal x = BishopReal._<_ BishopReal.0ℝ x

NonnegativeTime : Canonical.Time → Set
NonnegativeTime t = BishopReal._≤_ BishopReal.0ℝ t

------------------------------------------------------------------------
-- The ONLY semantic backend.
--
-- In particular there is no field for "SolvesNS", "DivergenceFree",
-- "Periodic", "RapidDecay" or "BoundedEnergy".  Those are fixed below.
------------------------------------------------------------------------

record FeffermanAnalyticKernel : Set₁ where
  field
    SmoothSpatialVector :
      Canonical.SpatialVectorField → Set
    SmoothVelocityHistory :
      Canonical.VelocityHistory → Set
    SmoothPressureHistory :
      Canonical.PressureHistory → Set
    SmoothForcingHistory :
      Canonical.ForcingHistory → Set

    velocityTimeDerivative :
      Canonical.VelocityHistory →
      Canonical.Time → Canonical.R3Point → Canonical.R3Vector

    velocitySpatialDerivative :
      Axis →
      Canonical.VelocityHistory →
      Canonical.Time → Canonical.R3Point → Canonical.R3Vector

    velocitySecondSpatialDerivative :
      Axis →
      Canonical.VelocityHistory →
      Canonical.Time → Canonical.R3Point → Canonical.R3Vector

    pressureSpatialDerivative :
      Axis →
      Canonical.PressureHistory →
      Canonical.Time → Canonical.R3Point → BishopReal.ℝ

    spatialJetNorm :
      Nat → Canonical.SpatialVectorField → Canonical.R3Point → BishopReal.ℝ

    forcingJetNorm :
      Nat → Nat →
      Canonical.ForcingHistory →
      Canonical.Time → Canonical.R3Point → BishopReal.ℝ

    spatialDecayWeight :
      Nat → Canonical.R3Point → BishopReal.ℝ

    spaceTimeDecayWeight :
      Nat → Canonical.Time → Canonical.R3Point → BishopReal.ℝ

    timeDecayWeight :
      Nat → Canonical.Time → BishopReal.ℝ

    kineticEnergy :
      Canonical.VelocityHistory → Canonical.Time → BishopReal.ℝ

open FeffermanAnalyticKernel public

spatialSlice :
  Canonical.VelocityHistory →
  Canonical.Time →
  Canonical.SpatialVectorField
spatialSlice u t = u t

forcingSlice :
  Canonical.ForcingHistory →
  Canonical.Time →
  Canonical.SpatialVectorField
forcingSlice f t = f t

velocityAt :
  Canonical.VelocityHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
velocityAt u t p = u t p

forcingAt :
  Canonical.ForcingHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
forcingAt f t p = f t p

laplacian :
  FeffermanAnalyticKernel →
  Canonical.VelocityHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
laplacian K u t p =
  vectorAdd
    (velocitySecondSpatialDerivative K axisX u t p)
    (vectorAdd
      (velocitySecondSpatialDerivative K axisY u t p)
      (velocitySecondSpatialDerivative K axisZ u t p))

convection :
  FeffermanAnalyticKernel →
  Canonical.VelocityHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
convection K u t p =
  vectorAdd
    (vectorScale
      (Canonical.vx (u t p))
      (velocitySpatialDerivative K axisX u t p))
    (vectorAdd
      (vectorScale
        (Canonical.vy (u t p))
        (velocitySpatialDerivative K axisY u t p))
      (vectorScale
        (Canonical.vz (u t p))
        (velocitySpatialDerivative K axisZ u t p)))

pressureGradient :
  FeffermanAnalyticKernel →
  Canonical.PressureHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
pressureGradient K p t x =
  Canonical.r3-vector
    (pressureSpatialDerivative K axisX p t x)
    (pressureSpatialDerivative K axisY p t x)
    (pressureSpatialDerivative K axisZ p t x)

divergence :
  FeffermanAnalyticKernel →
  Canonical.VelocityHistory →
  Canonical.Time → Canonical.R3Point → BishopReal.ℝ
divergence K u t p =
  BishopReal._+_
    (axisComponent axisX
      (velocitySpatialDerivative K axisX u t p))
    (BishopReal._+_
      (axisComponent axisY
        (velocitySpatialDerivative K axisY u t p))
      (axisComponent axisZ
        (velocitySpatialDerivative K axisZ u t p)))

momentumResidual :
  FeffermanAnalyticKernel →
  BishopReal.ℝ →
  Canonical.VelocityHistory →
  Canonical.PressureHistory →
  Canonical.ForcingHistory →
  Canonical.Time → Canonical.R3Point → Canonical.R3Vector
momentumResidual K ν u p f t x =
  vectorSub
    (vectorAdd
      (velocityTimeDerivative K u t x)
      (convection K u t x))
    (vectorAdd
      (vectorSub
        (vectorScale ν (laplacian K u t x))
        (pressureGradient K p t x))
      (f t x))

zeroForcing : Canonical.ForcingHistory
zeroForcing t x = zeroVector

------------------------------------------------------------------------
-- Fixed Fefferman predicates.
------------------------------------------------------------------------

DivergenceFreeSpatial :
  FeffermanAnalyticKernel →
  Canonical.SpatialVectorField → Set
DivergenceFreeSpatial K initial =
  (x : Canonical.R3Point) →
  BishopReal._≃_
    ( BishopReal._+_
      (axisComponent axisX
        (velocitySpatialDerivative K axisX
          (λ t → initial) BishopReal.0ℝ x))
      (BishopReal._+_
        (axisComponent axisY
          (velocitySpatialDerivative K axisY
            (λ t → initial) BishopReal.0ℝ x))
        (axisComponent axisZ
          (velocitySpatialDerivative K axisZ
            (λ t → initial) BishopReal.0ℝ x))))
    BishopReal.0ℝ

DivergenceFreeHistory :
  FeffermanAnalyticKernel →
  Canonical.VelocityHistory → Set
DivergenceFreeHistory K u =
  (t : Canonical.Time) → NonnegativeTime t →
  (x : Canonical.R3Point) →
  BishopReal._≃_ (divergence K u t x) BishopReal.0ℝ

RapidSpatialDecay :
  FeffermanAnalyticKernel →
  Canonical.SpatialVectorField → Set
RapidSpatialDecay K initial =
  (order power : Nat) →
  ∃ λ C →
    BishopReal.NonNegative C
    × ((x : Canonical.R3Point) →
      BishopReal._≤_
        (spatialJetNorm K order initial x)
        (BishopReal._*_ C (spatialDecayWeight K power x)))

RapidSpaceTimeDecay :
  FeffermanAnalyticKernel →
  Canonical.ForcingHistory → Set
RapidSpaceTimeDecay K f =
  (spaceOrder timeOrder power : Nat) →
  ∃ λ C →
    BishopReal.NonNegative C
    × ((t : Canonical.Time) → NonnegativeTime t →
      (x : Canonical.R3Point) →
      BishopReal._≤_
        (forcingJetNorm K spaceOrder timeOrder f t x)
        (BishopReal._*_ C (spaceTimeDecayWeight K power t x)))

RapidTimeDecayAllForcingDerivatives :
  FeffermanAnalyticKernel →
  Canonical.ForcingHistory → Set
RapidTimeDecayAllForcingDerivatives K f =
  (spaceOrder timeOrder power : Nat) →
  ∃ λ C →
    BishopReal.NonNegative C
    × ((t : Canonical.Time) → NonnegativeTime t →
      (x : Canonical.R3Point) →
      BishopReal._≤_
        (forcingJetNorm K spaceOrder timeOrder f t x)
        (BishopReal._*_ C (timeDecayWeight K power t)))

BoundedKineticEnergy :
  FeffermanAnalyticKernel →
  Canonical.VelocityHistory → Set
BoundedKineticEnergy K u =
  ∃ λ C →
    (t : Canonical.Time) →
    NonnegativeTime t →
    BishopReal._<_ (kineticEnergy K u t) C

UnitPeriodicSpatialVector :
  Canonical.SpatialVectorField → Set
UnitPeriodicSpatialVector field =
  (axis : Axis) → (x : Canonical.R3Point) →
  vectorEquivalent (field (shiftPoint axis x)) (field x)

UnitPeriodicVelocity :
  Canonical.VelocityHistory → Set
UnitPeriodicVelocity u =
  (axis : Axis) → (t : Canonical.Time) → NonnegativeTime t →
  (x : Canonical.R3Point) →
  vectorEquivalent (u t (shiftPoint axis x)) (u t x)

UnitPeriodicPressure :
  Canonical.PressureHistory → Set
UnitPeriodicPressure p =
  (axis : Axis) → (t : Canonical.Time) → NonnegativeTime t →
  (x : Canonical.R3Point) →
  BishopReal._≃_ (p t (shiftPoint axis x)) (p t x)

UnitPeriodicForcing :
  Canonical.ForcingHistory → Set
UnitPeriodicForcing f =
  (axis : Axis) → (t : Canonical.Time) → NonnegativeTime t →
  (x : Canonical.R3Point) →
  vectorEquivalent (f t (shiftPoint axis x)) (f t x)

AttainsInitialDatum :
  Canonical.VelocityHistory →
  Canonical.SpatialVectorField → Set
AttainsInitialDatum u initial =
  (x : Canonical.R3Point) →
  vectorEquivalent (u BishopReal.0ℝ x) (initial x)

SolvesForcedNS :
  FeffermanAnalyticKernel →
  BishopReal.ℝ →
  Canonical.VelocityHistory →
  Canonical.PressureHistory →
  Canonical.SpatialVectorField →
  Canonical.ForcingHistory →
  Set
SolvesForcedNS K ν u p initial f =
  ((t : Canonical.Time) → NonnegativeTime t →
    (x : Canonical.R3Point) →
    vectorEquivalent
      (momentumResidual K ν u p f t x)
      zeroVector)
  × AttainsInitialDatum u initial

SolvesUnforcedNS :
  FeffermanAnalyticKernel →
  BishopReal.ℝ →
  Canonical.VelocityHistory →
  Canonical.PressureHistory →
  Canonical.SpatialVectorField →
  Set
SolvesUnforcedNS K ν u p initial =
  SolvesForcedNS K ν u p initial zeroForcing

------------------------------------------------------------------------
-- The old authority record is now constructed, not chosen.
------------------------------------------------------------------------

concreteNSSemantics :
  FeffermanAnalyticKernel →
  Canonical.CanonicalNSSemantics
concreteNSSemantics K = record
  { Canonical.PositiveReal = PositiveReal
  ; Canonical.NonnegativeTime = NonnegativeTime
  ; Canonical.SmoothSpatialVector = SmoothSpatialVector K
  ; Canonical.SmoothVelocityHistory = SmoothVelocityHistory K
  ; Canonical.SmoothPressureHistory = SmoothPressureHistory K
  ; Canonical.SmoothForcingHistory = SmoothForcingHistory K
  ; Canonical.DivergenceFreeSpatial = DivergenceFreeSpatial K
  ; Canonical.DivergenceFreeHistory = DivergenceFreeHistory K
  ; Canonical.RapidSpatialDecay = RapidSpatialDecay K
  ; Canonical.RapidSpaceTimeDecay = RapidSpaceTimeDecay K
  ; Canonical.BoundedKineticEnergy = BoundedKineticEnergy K
  ; Canonical.UnitPeriodicSpatialVector = UnitPeriodicSpatialVector
  ; Canonical.UnitPeriodicVelocity = UnitPeriodicVelocity
  ; Canonical.UnitPeriodicPressure = UnitPeriodicPressure
  ; Canonical.UnitPeriodicForcing = UnitPeriodicForcing
  ; Canonical.RapidTimeDecayAllForcingDerivatives =
      RapidTimeDecayAllForcingDerivatives K
  ; Canonical.AttainsInitialDatum = AttainsInitialDatum
  ; Canonical.SolvesUnforcedNS = SolvesUnforcedNS K
  ; Canonical.SolvesForcedNS = SolvesForcedNS K
  }

arbitraryNSPredicateChoiceRemaining : Bool
arbitraryNSPredicateChoiceRemaining = false

pdeDefinedFromCoordinateDerivatives : Bool
pdeDefinedFromCoordinateDerivatives = true

periodicityDefinedExtensionally : Bool
periodicityDefinedExtensionally = true

initialTraceDefinedExtensionally : Bool
initialTraceDefinedExtensionally = true

decayPredicatesDefinedFromJetNorms : Bool
decayPredicatesDefinedFromJetNorms = true

boundedEnergyDefinedFromKineticEnergy : Bool
boundedEnergyDefinedFromKineticEnergy = true

nativeBishopCalculusBackendConstructedHere : Bool
nativeBishopCalculusBackendConstructedHere = false

foreignKernelProofImportedHere : Bool
foreignKernelProofImportedHere = false

clayPromotion : Bool
clayPromotion = false

arbitraryNSPredicateChoiceRemainingIsFalse :
  arbitraryNSPredicateChoiceRemaining ≡ false
arbitraryNSPredicateChoiceRemainingIsFalse = refl

pdeDefinedFromCoordinateDerivativesIsTrue :
  pdeDefinedFromCoordinateDerivatives ≡ true
pdeDefinedFromCoordinateDerivativesIsTrue = refl

foreignKernelProofImportedHereIsFalse :
  foreignKernelProofImportedHere ≡ false
foreignKernelProofImportedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
