module DASHI.Moonshine.JInvariantLambdaPunctured27SignMaxCutExact where

-- Original-source parity cross-cut (pi/Klein-j PR #1529).
-- Reuses JInvariantLambdaCyclotomicParityExact's exact C3/S3 source,
-- native P3^3 punctured 26 <-> 13 x Bool, and its spatial four-cycle
-- no-edge-compatible-section proof.
--
-- This is NOT a same-object identification between the rational
-- projective lambda plane and the 13-axis spatial hyperfabric.
-- It exhibits TWO independently proved signed obstructions to blindly
-- quotienting by an order-two orientation while consuming a scalar j.
-- Source written; Agda kernel check pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; -_)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Cyclo
import DASHI.Moonshine.JInvariantLambdaCyclotomicParityExact as Lambda
import DASHI.Unified.HyperfabricPunctured27Projective13OrientationExact as Native

-- On the actual original rational cyclotomic carrier, the selected
-- order-three rotation is even on Vandermonde V while reflection is odd.
originalLambdaRotationEven :
  (x : Cyclo.Cyclotomic3) →
  Lambda.vandermonde (Lambda.rotate x)
    ≡ Lambda.vandermonde x
originalLambdaRotationEven = Lambda.rotateEven

originalLambdaReflectionOdd :
  (x : Cyclo.Cyclotomic3) →
  Lambda.vandermonde (Lambda.reflect x)
    ≡ - Lambda.vandermonde x
originalLambdaReflectionOdd = Lambda.reflectOdd

originalLambdaNormReflectionInvariant :
  (x : Cyclo.Cyclotomic3) →
  Cyclo.norm (Lambda.reflect x) ≡ Cyclo.norm x
originalLambdaNormReflectionInvariant = Lambda.reflectNorm

-- On a DIFFERENT actual source carrier, antipodal orientation is
-- retained and recoverable, not reconstructed from a projective label.
nativeThirteenOrientationRoundTrip :
  (axis : Native.Axis13) (bit : Bool) →
  Native.encode (Native.decode (axis , bit))
    ≡ just (axis , bit)
nativeThirteenOrientationRoundTrip = Native.decodeEncode

-- The source's native spatial sign cocycle is nontrivial. Even a
-- scalar-j/Norm-invariant observation on the separate lambda carrier
-- cannot manufacture a global edge-compatible section of this cube.
nativeSpatialOrientationObstructed :
  (x pp y pm : Bool) →
  Native._xor_ x pp ≡ false →
  Native._xor_ pp y ≡ false →
  Native._xor_ y pm ≡ true →
  Native._xor_ pm x ≡ false → ⊥
nativeSpatialOrientationObstructed =
  Native.noEdgeCompatibleOrientation

-- Genuine same-carrier / same-action intertwiners from lambda(tau)
-- to native punctured27 or original theta/Hecke data remain OPEN.
