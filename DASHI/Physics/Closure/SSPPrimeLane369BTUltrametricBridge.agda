module DASHI.Physics.Closure.SSPPrimeLane369BTUltrametricBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_∸_)
open import Data.Vec using ([]; _∷_)

import DASHI.Geometry.SSP369Ultrametric as Geo
import DASHI.Physics.Closure.SSPPrimeLane369BTBridge as BT
import DASHI.TrackedPrimes as TP

three : Nat
three = suc (suc (suc zero))

rootAddress : Geo.Address zero
rootAddress = []

depthThreeAddress : Geo.Address three
depthThreeAddress =
  Geo.digit3 ∷ Geo.digit6 ∷ Geo.digit9 ∷ []

record SSPPrimeLane369BTUltrametricBridge : Set where
  constructor mkSSPPrimeLane369BTUltrametricBridge
  field
    btProfile : BT.SSPPrimeLane369BTProfile
    primeLane : TP.SSP
    primeLaneMatches : BT.primeLane btProfile ≡ primeLane
    addressDepth : Nat
    sourceAddress : Geo.Address addressDepth
    targetAddress : Geo.Address addressDepth
    prefixDepth : Nat
    prefixWitness : Geo.PrefixMatch prefixDepth sourceAddress targetAddress
    agreementDepthMatches :
      Geo.agreementDepth sourceAddress targetAddress ≡ prefixDepth
    distanceMatches :
      Geo.distance sourceAddress targetAddress ≡ addressDepth ∸ prefixDepth

open SSPPrimeLane369BTUltrametricBridge public

canonicalRootBTUltrametricBridge :
  SSPPrimeLane369BTUltrametricBridge
canonicalRootBTUltrametricBridge =
  mkSSPPrimeLane369BTUltrametricBridge
    (BT.primeLane369BTProfile TP.p3)
    TP.p3
    refl
    zero
    rootAddress
    rootAddress
    zero
    Geo.prefix-zero
    refl
    refl

canonicalDepthThreeBTUltrametricBridge :
  SSPPrimeLane369BTUltrametricBridge
canonicalDepthThreeBTUltrametricBridge =
  mkSSPPrimeLane369BTUltrametricBridge
    (BT.primeLane369BTProfile TP.p7)
    TP.p7
    refl
    three
    depthThreeAddress
    depthThreeAddress
    three
    (Geo.prefix-cons Geo.digit3
      (Geo.prefix-cons Geo.digit6
        (Geo.prefix-cons Geo.digit9 Geo.prefix-zero)))
    refl
    refl

p3BTValencyIs4 : BT.btValency (BT.primeLane369BTProfile TP.p3) ≡ 4
p3BTValencyIs4 = refl

p7BTValencyIs8 : BT.btValency (BT.primeLane369BTProfile TP.p7) ≡ 8
p7BTValencyIs8 = refl

rootAgreementDepthIsZero :
  Geo.agreementDepth rootAddress rootAddress ≡ zero
rootAgreementDepthIsZero = refl

rootPrefixWitness :
  Geo.PrefixMatch zero rootAddress rootAddress
rootPrefixWitness = Geo.prefix-zero

rootDistanceIsZero :
  Geo.distance rootAddress rootAddress ≡ zero
rootDistanceIsZero = refl

depthThreeAgreementDepthIsThree :
  Geo.agreementDepth depthThreeAddress depthThreeAddress ≡ three
depthThreeAgreementDepthIsThree = refl

depthThreePrefixWitness :
  Geo.PrefixMatch three depthThreeAddress depthThreeAddress
depthThreePrefixWitness =
  Geo.prefix-cons Geo.digit3
    (Geo.prefix-cons Geo.digit6
      (Geo.prefix-cons Geo.digit9 Geo.prefix-zero))

depthThreeDistanceIsZero :
  Geo.distance depthThreeAddress depthThreeAddress ≡ zero
depthThreeDistanceIsZero = refl

canonicalRootBTProfilePrimeIsP3 :
  BT.primeLane (btProfile canonicalRootBTUltrametricBridge) ≡ TP.p3
canonicalRootBTProfilePrimeIsP3 = refl

canonicalDepthThreeBTProfilePrimeIsP7 :
  BT.primeLane (btProfile canonicalDepthThreeBTUltrametricBridge) ≡ TP.p7
canonicalDepthThreeBTProfilePrimeIsP7 = refl
