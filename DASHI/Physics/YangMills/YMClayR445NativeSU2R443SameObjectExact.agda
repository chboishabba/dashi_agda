{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR445NativeSU2R443SameObjectExact where

------------------------------------------------------------------------
-- R443 -> R445 EXACT ORIGINAL NATIVE SU2 CONFIGURATION/OBSERVABLE WELD.
--
-- Prior critical universe bug in RationalSU2BondData has been repaired
-- in its original owner. No surrogate bond-field config or duplicated
-- physical measure is needed. The R443 source Gibbs-Wilson C3 consumer
-- and R445/P2 bounded literal Wilson cylinder input are the SAME
-- RationalSU2BondData 3, with the same selected quaternion group/path.
--
-- Mathematical source: Wilson, Balaban, and existing DASHI native
-- expectation/R278/P2 limits; this new code composes those theorem owners.
-- It does NOT supply R445 bounded-observable tail convergence or actual
-- physical continuum measures: the explicit NativePreferred inputs
-- remain genuine theorem-bearing hypotheses.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Native
import DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact as Wilson
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativeThermodynamicProducerExact as Operations
import DASHI.Physics.YangMills.BalabanLiteralWilsonNativePhysicalMeasureExact as Measure
import DASHI.Physics.YangMills.YMClayLiteralWilsonP2NativeMeasureExact as P2
import DASHI.Physics.YangMills.YMClayNativeRationalSU2Side4C3CarrierWeldExact as Weld
import DASHI.Physics.YangMills.YMClayR443NativeSixPlaneHaarNumeratorExact as R443
import DASHI.Physics.YangMills.YMClayNativeRationalSU2SixPlaneSameSourceExact as Six

-- This equality did NOT typecheck while the original source record
-- was unnecessarily declared Set1. Both are literally the same type.
r443R445NativeConfigurationSameObject :
  R443.NativeConfiguration ≡ Native.RationalSU2BondData Weld.three
r443R445NativeConfigurationSameObject = refl

-- Original R443 source six-plaquette trace really is an observable in the
-- R445 native Wilson function algebra, not an analogous jCoarse surrogate.
r443SixPlaneActionIsNativeWilsonObservable :
  ∀ dataSet →
  R443.nativeSixTrace dataSet
  ≡ Six.sixPlanePhysicalTraceAction dataSet
r443SixPlaneActionIsNativeWilsonObservable dataSet = refl

nativeR443SixPlaneR445Observable : Wilson.RationalWilsonObservable Weld.three
nativeR443SixPlaneR445Observable = R443.nativeSixTrace

-- The physical Wilson *deficit*, not just its raw trace, is also a
-- function on the exact same R445 native observable carrier.
-- Boundedness of each elementary Wilson loop is independently proved
-- already; one must still compile the SIX-SITE-SUM bounded majorant to
-- identify this particular total action with R445's BoundedObservable.
nativeR443SixDeficitR445Observable : Wilson.RationalWilsonObservable Weld.three
nativeR443SixDeficitR445Observable = R443.nativeSixWilsonDeficit

r443SixDeficitIsNativeObservableSameObject :
  ∀ dataSet →
  nativeR443SixDeficitR445Observable dataSet
  ≡ R443.nativeSixWilsonDeficit dataSet
r443SixDeficitIsNativeObservableSameObject dataSet = refl

-- Existing R445/P2 literal quaternion Wilson-cylinder theorem now accepts
-- exactly the same physical configuration type as native R443, no cast.
-- The selected physical measure and its actual tails stay SOURCE inputs.
nativeR443R445FiniteCylinderLimits :
  ∀ {M : Set}
    {operationsInputs :
      Operations.NativeWilsonOSOperationsInputs M Weld.three}
    (measureInputs :
      Measure.NativeWilsonPreferredPhysicalMeasureInputs
        M Weld.three operationsInputs)
    (translateLoop :
      Wilson.RationalWilsonPath Weld.three → Nat →
      Wilson.RationalWilsonPath Weld.three)
    (left right : List (Wilson.RationalWilsonPath Weld.three))
    (time : Nat) →
  P2.NativeWilsonP2Limits measureInputs translateLoop left right time
nativeR443R445FiniteCylinderLimits =
  P2.nativeWilsonP2Limits
