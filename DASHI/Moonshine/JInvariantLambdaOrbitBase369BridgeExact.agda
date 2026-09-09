module DASHI.Moonshine.JInvariantLambdaOrbitBase369BridgeExact where

------------------------------------------------------------------------
-- J-INVARIANT / MODULAR-LAMBDA / BASE369 FINITE ORBIT BRIDGE
--
-- The source atlas records an inspected secondary reference listing six
-- lambda replacements that preserve j.  This module does NOT implement the
-- analytic lambda function and does NOT prove j-invariance.  It proves only
-- the exact finite indexing geometry of those six source-listed labels:
--
--   six labels = three complement pairs x two orientations.
--
-- That finite 6 = 3 x 2 geometry matches the already-owned Base369
-- HexTruth -> TriTruth + orientation-polarity carrier.  Promotion beyond this
-- label-level correspondence requires a same-function analytic intertwiner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; tri-low
  ; tri-mid
  ; tri-high
  )

import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Moonshine.JInvariantSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. The six source-listed lambda replacement labels.
------------------------------------------------------------------------

data LambdaOrbitTag : Set where
  lambdaIdentity : LambdaOrbitTag
  lambdaOneOverOneMinus : LambdaOrbitTag
  lambdaMinusOneOverLambda : LambdaOrbitTag
  lambdaReciprocal : LambdaOrbitTag
  lambdaOverLambdaMinusOne : LambdaOrbitTag
  lambdaOneMinus : LambdaOrbitTag

-- Tag-level complement mu |-> 1-mu.  On the six listed rational functions
-- this pairs:
--   lambda <-> 1-lambda
--   1/(1-lambda) <-> lambda/(lambda-1)
--   (lambda-1)/lambda <-> 1/lambda.
-- The rational-function identities themselves are source/transcription debt;
-- only this finite label involution is proved here.
lambdaComplement : LambdaOrbitTag → LambdaOrbitTag
lambdaComplement lambdaIdentity = lambdaOneMinus
lambdaComplement lambdaOneOverOneMinus = lambdaOverLambdaMinusOne
lambdaComplement lambdaMinusOneOverLambda = lambdaReciprocal
lambdaComplement lambdaReciprocal = lambdaMinusOneOverLambda
lambdaComplement lambdaOverLambdaMinusOne = lambdaOneOverOneMinus
lambdaComplement lambdaOneMinus = lambdaIdentity

lambdaComplementInvolutive :
  (x : LambdaOrbitTag) → lambdaComplement (lambdaComplement x) ≡ x
lambdaComplementInvolutive lambdaIdentity = refl
lambdaComplementInvolutive lambdaOneOverOneMinus = refl
lambdaComplementInvolutive lambdaMinusOneOverLambda = refl
lambdaComplementInvolutive lambdaReciprocal = refl
lambdaComplementInvolutive lambdaOverLambdaMinusOne = refl
lambdaComplementInvolutive lambdaOneMinus = refl

------------------------------------------------------------------------
-- 2. Three pair identities and two local orientations.
------------------------------------------------------------------------

lambdaPairPhase : LambdaOrbitTag → TriTruth
lambdaPairPhase lambdaIdentity = tri-low
lambdaPairPhase lambdaOneMinus = tri-low
lambdaPairPhase lambdaOneOverOneMinus = tri-mid
lambdaPairPhase lambdaOverLambdaMinusOne = tri-mid
lambdaPairPhase lambdaMinusOneOverLambda = tri-high
lambdaPairPhase lambdaReciprocal = tri-high

lambdaOrientation : LambdaOrbitTag → Mobius.OrientationPolarity
lambdaOrientation lambdaIdentity = Mobius.positive
lambdaOrientation lambdaOneOverOneMinus = Mobius.positive
lambdaOrientation lambdaMinusOneOverLambda = Mobius.positive
lambdaOrientation lambdaReciprocal = Mobius.negative
lambdaOrientation lambdaOverLambdaMinusOne = Mobius.negative
lambdaOrientation lambdaOneMinus = Mobius.negative

lambdaComplementPreservesPairPhase :
  (x : LambdaOrbitTag) → lambdaPairPhase (lambdaComplement x) ≡ lambdaPairPhase x
lambdaComplementPreservesPairPhase lambdaIdentity = refl
lambdaComplementPreservesPairPhase lambdaOneOverOneMinus = refl
lambdaComplementPreservesPairPhase lambdaMinusOneOverLambda = refl
lambdaComplementPreservesPairPhase lambdaReciprocal = refl
lambdaComplementPreservesPairPhase lambdaOverLambdaMinusOne = refl
lambdaComplementPreservesPairPhase lambdaOneMinus = refl

lambdaComplementFlipsOrientation :
  (x : LambdaOrbitTag) →
  lambdaOrientation (lambdaComplement x) ≡
  Mobius.flipOrientationPolarity (lambdaOrientation x)
lambdaComplementFlipsOrientation lambdaIdentity = refl
lambdaComplementFlipsOrientation lambdaOneOverOneMinus = refl
lambdaComplementFlipsOrientation lambdaMinusOneOverLambda = refl
lambdaComplementFlipsOrientation lambdaReciprocal = refl
lambdaComplementFlipsOrientation lambdaOverLambdaMinusOne = refl
lambdaComplementFlipsOrientation lambdaOneMinus = refl

------------------------------------------------------------------------
-- 3. Exact finite equivalence with the existing Base369 HexTruth carrier.
--
-- The enumeration is chosen so Base369's +3 involution is exactly the above
-- complement-pair involution and its mod-3 observer is exactly pair identity.
------------------------------------------------------------------------

hexToLambdaOrbit : HexTruth → LambdaOrbitTag
hexToLambdaOrbit hex-0 = lambdaIdentity
hexToLambdaOrbit hex-1 = lambdaOneOverOneMinus
hexToLambdaOrbit hex-2 = lambdaMinusOneOverLambda
hexToLambdaOrbit hex-3 = lambdaOneMinus
hexToLambdaOrbit hex-4 = lambdaOverLambdaMinusOne
hexToLambdaOrbit hex-5 = lambdaReciprocal

lambdaOrbitToHex : LambdaOrbitTag → HexTruth
lambdaOrbitToHex lambdaIdentity = hex-0
lambdaOrbitToHex lambdaOneOverOneMinus = hex-1
lambdaOrbitToHex lambdaMinusOneOverLambda = hex-2
lambdaOrbitToHex lambdaReciprocal = hex-5
lambdaOrbitToHex lambdaOverLambdaMinusOne = hex-4
lambdaOrbitToHex lambdaOneMinus = hex-3

hexLambdaRoundTrip : (h : HexTruth) → lambdaOrbitToHex (hexToLambdaOrbit h) ≡ h
hexLambdaRoundTrip hex-0 = refl
hexLambdaRoundTrip hex-1 = refl
hexLambdaRoundTrip hex-2 = refl
hexLambdaRoundTrip hex-3 = refl
hexLambdaRoundTrip hex-4 = refl
hexLambdaRoundTrip hex-5 = refl

lambdaHexRoundTrip : (l : LambdaOrbitTag) → hexToLambdaOrbit (lambdaOrbitToHex l) ≡ l
lambdaHexRoundTrip lambdaIdentity = refl
lambdaHexRoundTrip lambdaOneOverOneMinus = refl
lambdaHexRoundTrip lambdaMinusOneOverLambda = refl
lambdaHexRoundTrip lambdaReciprocal = refl
lambdaHexRoundTrip lambdaOverLambdaMinusOne = refl
lambdaHexRoundTrip lambdaOneMinus = refl

base369MobiusIntertwinesLambdaComplement :
  (h : HexTruth) →
  hexToLambdaOrbit (Mobius.mobiusTransport h) ≡
  lambdaComplement (hexToLambdaOrbit h)
base369MobiusIntertwinesLambdaComplement hex-0 = refl
base369MobiusIntertwinesLambdaComplement hex-1 = refl
base369MobiusIntertwinesLambdaComplement hex-2 = refl
base369MobiusIntertwinesLambdaComplement hex-3 = refl
base369MobiusIntertwinesLambdaComplement hex-4 = refl
base369MobiusIntertwinesLambdaComplement hex-5 = refl

base369TriadicPhaseMatchesLambdaPairPhase :
  (h : HexTruth) →
  lambdaPairPhase (hexToLambdaOrbit h) ≡ Mobius.hexTriadicPhase h
base369TriadicPhaseMatchesLambdaPairPhase hex-0 = refl
base369TriadicPhaseMatchesLambdaPairPhase hex-1 = refl
base369TriadicPhaseMatchesLambdaPairPhase hex-2 = refl
base369TriadicPhaseMatchesLambdaPairPhase hex-3 = refl
base369TriadicPhaseMatchesLambdaPairPhase hex-4 = refl
base369TriadicPhaseMatchesLambdaPairPhase hex-5 = refl

base369OrientationMatchesLambdaOrientation :
  (h : HexTruth) →
  lambdaOrientation (hexToLambdaOrbit h) ≡ Mobius.hexOrientationPolarity h
base369OrientationMatchesLambdaOrientation hex-0 = refl
base369OrientationMatchesLambdaOrientation hex-1 = refl
base369OrientationMatchesLambdaOrientation hex-2 = refl
base369OrientationMatchesLambdaOrientation hex-3 = refl
base369OrientationMatchesLambdaOrientation hex-4 = refl
base369OrientationMatchesLambdaOrientation hex-5 = refl

------------------------------------------------------------------------
-- 4. Introspective / attribution boundary.
------------------------------------------------------------------------

record JLambdaBase369Boundary : Set where
  constructor j-lambda-base369-boundary
  field
    sourceListsSixLambdaReplacements : Bool
    sixLabelsHaveExactThreePairTwoOrientationIndexing : Bool
    base369HexTransportMatchesPairComplement : Bool
    base369TriadicObserverMatchesPairIdentity : Bool
    analyticLambdaFunctionsImplementedHere : Bool
    jInvarianceKernelProvedHere : Bool
    visualThreeFanIsThetaTheorem : Bool
    sourceReferenceAutomaticallyProvesMonsterPromotion : Bool
    rhReceiptAutomaticallyProvesThisBridge : Bool

canonicalJLambdaBase369Boundary : JLambdaBase369Boundary
canonicalJLambdaBase369Boundary =
  j-lambda-base369-boundary true true true true false false false false false

-- Keep the source atlas live in the dependency graph and pin that the exact
-- inspected source claim used by this bridge remains secondary-reference only.
lambdaSourceIsSecondaryReference :
  Sources.JReferenceClaim.secondaryReferenceOnly Sources.jLambdaSixOrbitClaim ≡ true
lambdaSourceIsSecondaryReference = refl
