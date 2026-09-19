module DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact where

------------------------------------------------------------------------
-- CANONICAL SEMANTIC CARRIERS FOR LITERAL A/C/D
--
-- NSClayLiteralABCDExact intentionally states the Clay propositions over
-- abstract carriers.  That is useful for theorem interfaces but unsafe as a
-- terminal proof boundary: one must not "prove" C or D by choosing convenient
-- meanings for velocity, pressure, forcing, or the PDE.
--
-- This owner fixes the underlying mathematical TYPES:
--
--   spatial point  = constructive R^3,
--   time           = constructive R,
--   vector field   = R^3 -> R^3 (or time x R^3 -> R^3),
--   scalar field   = R^3 -> R,
--
-- and leaves only the genuine analysis predicates/equation semantics to an
-- explicit authority record.  From that one authority we construct the
-- literal A, C and D carriers used by the capstone.
--
-- Thus released C/D proofs can enter only after they are mapped to these exact
-- field/forcing types and equation predicates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSClayLiteralABCDExact as Clay

record R3Point : Set where
  constructor r3-point
  field
    x y z : BishopReal.ℝ
open R3Point public

record R3Vector : Set where
  constructor r3-vector
  field
    vx vy vz : BishopReal.ℝ
open R3Vector public

Time : Set
Time = BishopReal.ℝ

SpatialVectorField : Set
SpatialVectorField = R3Point → R3Vector

SpatialScalarField : Set
SpatialScalarField = R3Point → BishopReal.ℝ

VelocityHistory : Set
VelocityHistory = Time → SpatialVectorField

PressureHistory : Set
PressureHistory = Time → SpatialScalarField

ForcingHistory : Set
ForcingHistory = Time → SpatialVectorField

record CanonicalNSSemantics : Set₁ where
  field
    PositiveReal : BishopReal.ℝ → Set
    NonnegativeTime : Time → Set

    SmoothSpatialVector : SpatialVectorField → Set
    SmoothVelocityHistory : VelocityHistory → Set
    SmoothPressureHistory : PressureHistory → Set
    SmoothForcingHistory : ForcingHistory → Set

    DivergenceFreeSpatial : SpatialVectorField → Set
    DivergenceFreeHistory : VelocityHistory → Set

    RapidSpatialDecay : SpatialVectorField → Set
    RapidSpaceTimeDecay : ForcingHistory → Set
    BoundedKineticEnergy : VelocityHistory → Set

    UnitPeriodicSpatialVector : SpatialVectorField → Set
    UnitPeriodicVelocity : VelocityHistory → Set
    UnitPeriodicPressure : PressureHistory → Set
    UnitPeriodicForcing : ForcingHistory → Set
    RapidTimeDecayAllForcingDerivatives : ForcingHistory → Set

    AttainsInitialDatum :
      VelocityHistory → SpatialVectorField → Set

    SolvesUnforcedNS :
      BishopReal.ℝ →
      VelocityHistory →
      PressureHistory →
      SpatialVectorField →
      Set

    SolvesForcedNS :
      BishopReal.ℝ →
      VelocityHistory →
      PressureHistory →
      SpatialVectorField →
      ForcingHistory →
      Set

open CanonicalNSSemantics public

canonicalEuclideanA :
  CanonicalNSSemantics →
  Clay.FeffermanEuclideanClayCarrier
canonicalEuclideanA S = record
  { Clay.Viscosity = BishopReal.ℝ
  ; Clay.PositiveViscosity = PositiveReal S
  ; Clay.SmoothEuclideanDatum = SpatialVectorField
  ; Clay.DatumSmoothOnR3 = SmoothSpatialVector S
  ; Clay.DatumDivergenceFree = DivergenceFreeSpatial S
  ; Clay.DatumRapidSpatialDecay = RapidSpatialDecay S
  ; Clay.GlobalVelocity = VelocityHistory
  ; Clay.GlobalPressure = PressureHistory
  ; Clay.VelocitySmoothOnR3TimesNonnegativeTime = SmoothVelocityHistory S
  ; Clay.PressureSmoothOnR3TimesNonnegativeTime = SmoothPressureHistory S
  ; Clay.SolvesThreeDimensionalMomentumEquationWithZeroForce =
      SolvesUnforcedNS S
  ; Clay.IncompressibleAtEveryNonnegativeTime = DivergenceFreeHistory S
  ; Clay.AttainsInitialDatumAtTimeZero = AttainsInitialDatum S
  ; Clay.BoundedKineticEnergyAtEveryNonnegativeTime = BoundedKineticEnergy S
  }

canonicalEuclideanC :
  CanonicalNSSemantics →
  Clay.FeffermanEuclideanForcedBreakdownCarrier
canonicalEuclideanC S = record
  { Clay.ViscosityC = BishopReal.ℝ
  ; Clay.PositiveViscosityC = PositiveReal S
  ; Clay.InitialDatumC = SpatialVectorField
  ; Clay.DatumSmoothC = SmoothSpatialVector S
  ; Clay.DatumDivergenceFreeC = DivergenceFreeSpatial S
  ; Clay.DatumRapidSpatialDecayC = RapidSpatialDecay S
  ; Clay.ForcingC = ForcingHistory
  ; Clay.ForcingSmoothC = SmoothForcingHistory S
  ; Clay.ForcingRapidSpaceTimeDecayC = RapidSpaceTimeDecay S
  ; Clay.GlobalVelocityC = VelocityHistory
  ; Clay.GlobalPressureC = PressureHistory
  ; Clay.VelocitySmoothPredicateC = SmoothVelocityHistory S
  ; Clay.PressureSmoothPredicateC = SmoothPressureHistory S
  ; Clay.SolvesForcedNavierStokesC = SolvesForcedNS S
  ; Clay.IncompressiblePredicateC = DivergenceFreeHistory S
  ; Clay.AttainsInitialDatumPredicateC = AttainsInitialDatum S
  ; Clay.BoundedEnergyPredicateC = BoundedKineticEnergy S
  }

canonicalPeriodicD :
  CanonicalNSSemantics →
  Clay.FeffermanPeriodicForcedBreakdownCarrier
canonicalPeriodicD S = record
  { Clay.ViscosityD = BishopReal.ℝ
  ; Clay.PositiveViscosityD = PositiveReal S
  ; Clay.InitialDatumD = SpatialVectorField
  ; Clay.DatumSmoothD = SmoothSpatialVector S
  ; Clay.DatumDivergenceFreeD = DivergenceFreeSpatial S
  ; Clay.DatumUnitPeriodicD = UnitPeriodicSpatialVector S
  ; Clay.ForcingD = ForcingHistory
  ; Clay.ForcingSmoothD = SmoothForcingHistory S
  ; Clay.ForcingUnitPeriodicD = UnitPeriodicForcing S
  ; Clay.ForcingRapidTimeDecayOfAllDerivativesD =
      RapidTimeDecayAllForcingDerivatives S
  ; Clay.GlobalVelocityD = VelocityHistory
  ; Clay.GlobalPressureD = PressureHistory
  ; Clay.VelocitySmoothPredicateD = SmoothVelocityHistory S
  ; Clay.PressureSmoothPredicateD = SmoothPressureHistory S
  ; Clay.VelocityUnitPeriodicPredicateD = UnitPeriodicVelocity S
  ; Clay.PressureUnitPeriodicPredicateD = UnitPeriodicPressure S
  ; Clay.SolvesForcedNavierStokesD = SolvesForcedNS S
  ; Clay.IncompressiblePredicateD = DivergenceFreeHistory S
  ; Clay.AttainsInitialDatumPredicateD = AttainsInitialDatum S
  }

canonicalFieldTypesFixed : Bool
canonicalFieldTypesFixed = true

canonicalAUsesConstructiveR3 : Bool
canonicalAUsesConstructiveR3 = true

canonicalCUsesConstructiveR3 : Bool
canonicalCUsesConstructiveR3 = true

canonicalDUsesPeriodicPredicatesOnSameR3FieldType : Bool
canonicalDUsesPeriodicPredicatesOnSameR3FieldType = true

arbitraryCarrierChoiceCountsAsCanonicalProof : Bool
arbitraryCarrierChoiceCountsAsCanonicalProof = false

releasedProofSameObjectMappingClosedHere : Bool
releasedProofSameObjectMappingClosedHere = false

clayPromotion : Bool
clayPromotion = false

canonicalFieldTypesFixedIsTrue : canonicalFieldTypesFixed ≡ true
canonicalFieldTypesFixedIsTrue = refl

arbitraryCarrierChoiceCountsAsCanonicalProofIsFalse :
  arbitraryCarrierChoiceCountsAsCanonicalProof ≡ false
arbitraryCarrierChoiceCountsAsCanonicalProofIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
