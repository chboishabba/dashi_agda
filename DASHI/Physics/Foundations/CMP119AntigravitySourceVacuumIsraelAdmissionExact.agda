{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySourceVacuumIsraelAdmissionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravityLocalizedVacuumReadoutExact as Readout
import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Israel

------------------------------------------------------------------------
-- ACTUAL SOURCE VACUA -> PARAMETERIZED ISRAEL/KOTTLER GEOMETRY
--
-- The historical 21/64 and 19/48 amplitudes are convenient exact fixtures.
-- They are not a fundamental source requirement.  For the concrete CMP119
-- LocalizedAction realization, select TWO ACTUAL source scales, read their
-- vacuum amplitudes with the already-existing plaquette projector, and solve
-- the rational-square Israel geometry against those amplitudes.
--
-- This turns "CMP119 must hit two magic fractions" into the honest equations
--
--   lambda_in(R,x)    = source vacuum at k_in
--   lambda_out(M,R,y) = source vacuum at k_out
--
-- plus positive-domain / outward-acceleration conditions.
------------------------------------------------------------------------

module _
  {Density Background Fluctuation : Set}
  (source : Source.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  record SourceVacuumPair : Set where
    constructor source-vacuum-pair
    field
      interiorScale : Nat
      exteriorScale : Nat

  open SourceVacuumPair public

  sourceInteriorLambda : SourceVacuumPair → ℚ
  sourceInteriorLambda pair =
    Readout.localizedVacuumValue source (interiorScale pair)

  sourceExteriorLambda : SourceVacuumPair → ℚ
  sourceExteriorLambda pair =
    Readout.localizedVacuumValue source (exteriorScale pair)

  record SourceVacuumIsraelAdmission (pair : SourceVacuumPair) : Set where
    constructor source-vacuum-israel-admission
    field
      mass radius x y : ℚ

      interiorLambdaMatchesSource :
        Israel.lambdaInFromSquareLapse radius x
        ≡ sourceInteriorLambda pair

      exteriorLambdaMatchesSource :
        Israel.lambdaOutFromSquareLapse mass radius y
        ≡ sourceExteriorLambda pair

      radiusPositive : 0ℚ < radius
      interiorLapseRootPositive : 0ℚ < x
      exteriorLapseRootPositive : 0ℚ < y
      interiorRootExceedsExteriorRoot : y < x

      outwardAccelerationPositive :
        0ℚ < Israel.outwardAccelerationScaled mass radius y

      positiveSurfaceEnergy :
        0ℚ < Israel.surfaceSigma8 radius x y

  open SourceVacuumIsraelAdmission public

record SourceVacuumIsraelAdmissionBoundary : Set where
  constructor source-vacuum-israel-admission-boundary
  field
    actualSourceVacuaFeedGeometry : Bool
    fixedTwentyOneSixtyFourAndNineteenFortyEightRequired : Bool
    geometryCanBeReoptimizedToSourceValues : Bool
    sourceToGeometryEqualitiesStillRequired : Bool
    orderAndPhysicalDomainWitnessesStillRequired : Bool
    noNewVacuumReadoutRequired : Bool

canonicalSourceVacuumIsraelAdmissionBoundary :
  SourceVacuumIsraelAdmissionBoundary
canonicalSourceVacuumIsraelAdmissionBoundary =
  source-vacuum-israel-admission-boundary
    true false true true true true
