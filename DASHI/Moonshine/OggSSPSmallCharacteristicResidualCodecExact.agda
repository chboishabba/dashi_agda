module DASHI.Moonshine.OggSSPSmallCharacteristicResidualCodecExact where

------------------------------------------------------------------------
-- SMALL-CHARACTERISTIC RESIDUAL CODECS
--
-- Cross-pollination from DASHI's dependent recoverable-projection machinery.
--
-- p=3:
--   three constant ternary states
--     ~= Sigma {zeroOrbit, nonzeroOrbit} residual
--   with unit residual over zero and binary orientation over nonzero.
--
-- p=2:
--   (strict side, NineOrbit)
--     ~= Sigma NineOrbit StrictSignedSide.
--
-- Thus the 5-vs-10 distinction is an exact reconstruction statement:
-- quotienting away strict side discards the residual required to reopen the
-- ten-object carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Small

------------------------------------------------------------------------
-- 1. p=3 dependent residual.
------------------------------------------------------------------------

data NonzeroOrientation : Set where
  negativeOrientation : NonzeroOrientation
  positiveOrientation : NonzeroOrientation

P3OrbitResidual : Small.ConstantTernaryOrbit → Set
P3OrbitResidual Small.zeroConstantOrbit = ⊤
P3OrbitResidual Small.nonzeroConstantOrbit = NonzeroOrientation

p3Project :
  Small.ConstantTernaryState → Small.ConstantTernaryOrbit
p3Project = Small.constantOrbitOf

p3Residual :
  (state : Small.ConstantTernaryState) →
  P3OrbitResidual (p3Project state)
p3Residual Triadic.zeroTrit = tt
p3Residual Triadic.negativeTrit = negativeOrientation
p3Residual Triadic.positiveTrit = positiveOrientation

p3Reopen :
  (orbit : Small.ConstantTernaryOrbit) →
  P3OrbitResidual orbit →
  Small.ConstantTernaryState
p3Reopen Small.zeroConstantOrbit tt = Triadic.zeroTrit
p3Reopen Small.nonzeroConstantOrbit negativeOrientation =
  Triadic.negativeTrit
p3Reopen Small.nonzeroConstantOrbit positiveOrientation =
  Triadic.positiveTrit

p3ReopenExact :
  (state : Small.ConstantTernaryState) →
  p3Reopen (p3Project state) (p3Residual state) ≡ state
p3ReopenExact Triadic.zeroTrit = refl
p3ReopenExact Triadic.negativeTrit = refl
p3ReopenExact Triadic.positiveTrit = refl

p3RecoverableProjection :
  Recoverable.DependentExactRecoverableProjection
    Small.ConstantTernaryState
    Small.ConstantTernaryOrbit
p3RecoverableProjection =
  Recoverable.dependentExactRecoverableProjection
    P3OrbitResidual
    p3Project
    p3Residual
    p3Reopen
    p3ReopenExact

p3CodeSeparating :
  Recoverable.DependentCodeSeparating p3RecoverableProjection
p3CodeSeparating =
  Recoverable.dependentCodeSeparating p3RecoverableProjection

p3ZeroResidualIsUnit :
  P3OrbitResidual Small.zeroConstantOrbit ≡ ⊤
p3ZeroResidualIsUnit = refl

p3NonzeroResidualIsBinary :
  P3OrbitResidual Small.nonzeroConstantOrbit ≡ NonzeroOrientation
p3NonzeroResidualIsBinary = refl

negativePositiveSameP3Coarse :
  p3Project Triadic.negativeTrit ≡ p3Project Triadic.positiveTrit
negativePositiveSameP3Coarse = refl

negativeNotPositive :
  Triadic.negativeTrit ≡ Triadic.positiveTrit → ⊥
negativeNotPositive ()

p3CoarseProjectionHasNoLeftInverse :
  (recover : Small.ConstantTernaryOrbit → Small.ConstantTernaryState) →
  ((state : Small.ConstantTernaryState) →
    recover (p3Project state) ≡ state) →
  ⊥
p3CoarseProjectionHasNoLeftInverse recover leftInverse =
  negativeNotPositive
    (trans
      (sym (leftInverse Triadic.negativeTrit))
      (trans
        (cong recover negativePositiveSameP3Coarse)
        (leftInverse Triadic.positiveTrit)))

------------------------------------------------------------------------
-- 2. p=2 retained orientation is exactly a coarse+residual codec.
------------------------------------------------------------------------

P2OrbitResidual : Triadic.NineOrbit → Set
P2OrbitResidual orbit = Compression.StrictSignedSide

p2Project :
  Small.P2ResidualObject → Triadic.NineOrbit
p2Project = proj₂

p2Residual :
  (state : Small.P2ResidualObject) →
  P2OrbitResidual (p2Project state)
p2Residual = proj₁

p2Reopen :
  (orbit : Triadic.NineOrbit) →
  P2OrbitResidual orbit →
  Small.P2ResidualObject
p2Reopen orbit side = side , orbit

p2ReopenExact :
  (state : Small.P2ResidualObject) →
  p2Reopen (p2Project state) (p2Residual state) ≡ state
p2ReopenExact (side , orbit) = refl

p2RecoverableProjection :
  Recoverable.DependentExactRecoverableProjection
    Small.P2ResidualObject
    Triadic.NineOrbit
p2RecoverableProjection =
  Recoverable.dependentExactRecoverableProjection
    P2OrbitResidual
    p2Project
    p2Residual
    p2Reopen
    p2ReopenExact

p2CodeSeparating :
  Recoverable.DependentCodeSeparating p2RecoverableProjection
p2CodeSeparating =
  Recoverable.dependentCodeSeparating p2RecoverableProjection

p2Encode :
  Small.P2ResidualObject →
  Recoverable.DependentCode p2RecoverableProjection
p2Encode = Recoverable.encode p2RecoverableProjection

p2Decode :
  Recoverable.DependentCode p2RecoverableProjection →
  Small.P2ResidualObject
p2Decode = Recoverable.decode p2RecoverableProjection

p2DecodeEncodeExact :
  (state : Small.P2ResidualObject) →
  p2Decode (p2Encode state) ≡ state
p2DecodeEncodeExact =
  Recoverable.decodeEncodeExact p2RecoverableProjection

------------------------------------------------------------------------
-- 3. Forgetting orientation is precisely forgetting the reopening residual.
------------------------------------------------------------------------

p2CoarseOnly :
  Recoverable.DependentCode p2RecoverableProjection →
  Triadic.NineOrbit
p2CoarseOnly = proj₁

p2CoarseOnlyAfterEncode :
  (state : Small.P2ResidualObject) →
  p2CoarseOnly (p2Encode state) ≡ p2Project state
p2CoarseOnlyAfterEncode (side , orbit) = refl

lowerUpperSameCoarse :
  (orbit : Triadic.NineOrbit) →
  p2Project (Compression.lowerSide , orbit)
  ≡ p2Project (Compression.upperSide , orbit)
lowerUpperSameCoarse orbit = refl

lowerNotUpper :
  (orbit : Triadic.NineOrbit) →
  (Compression.lowerSide , orbit)
  ≡ (Compression.upperSide , orbit) →
  ⊥
lowerNotUpper orbit ()

p2CoarseProjectionHasNoLeftInverse :
  (recover : Triadic.NineOrbit → Small.P2ResidualObject) →
  ((state : Small.P2ResidualObject) →
    recover (p2Project state) ≡ state) →
  (orbit : Triadic.NineOrbit) →
  ⊥
p2CoarseProjectionHasNoLeftInverse recover leftInverse orbit =
  lowerNotUpper orbit
    (trans
      (sym (leftInverse (Compression.lowerSide , orbit)))
      (trans
        (cong recover (lowerUpperSameCoarse orbit))
        (leftInverse (Compression.upperSide , orbit))))

data CoarseP2CodeRecoversStrictSide : Set where

coarseP2CodeDoesNotRecoverStrictSide :
  CoarseP2CodeRecoversStrictSide → ⊥
coarseP2CodeDoesNotRecoverStrictSide ()

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record SmallCharacteristicResidualCodecBoundary : Set where
  constructor small-characteristic-residual-codec-boundary
  field
    p3DependentResidualCodecConstructed : Bool
    p3ZeroOrbitHasUnitResidual : Bool
    p3NonzeroOrbitHasBinaryResidual : Bool
    p3CodecReopensExactly : Bool
    p3CoarseOrbitAloneCannotReopen : Bool

    p2CoarseNineOrbitResidualIsStrictSide : Bool
    p2TenObjectCarrierReopensExactly : Bool
    p2DependentCodeSeparating : Bool
    p2FiveObjectQuotientDiscardsResidual : Bool
    p2CoarseOrbitAloneCannotReopen : Bool
    p2OrientationIsExplicitReopeningData : Bool

canonicalSmallCharacteristicResidualCodecBoundary :
  SmallCharacteristicResidualCodecBoundary
canonicalSmallCharacteristicResidualCodecBoundary =
  small-characteristic-residual-codec-boundary
    true true true true true
    true true true true true true
