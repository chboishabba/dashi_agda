module DASHI.Physics.Closure.SSPPrimeLane369PAdicUltrametricBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using ([]; _∷_)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Geometry.SSP369Ultrametric as Geo
import DASHI.Physics.Closure.SSPPrimeLane369PAdicBridge as Bridge

three : Nat
three = Ref.three

toGeoDigit : Ref.Lane369Digit → Geo.Digit369
toGeoDigit Ref.digit-3 = Geo.digit3
toGeoDigit Ref.digit-6 = Geo.digit6
toGeoDigit Ref.digit-9 = Geo.digit9

toGeoAddress : ∀ {d : Nat} → Ref.Lane369Address d → Geo.Address d
toGeoAddress Ref.root = []
toGeoAddress (Ref.extend path digit) =
  appendGeoDigit (toGeoAddress path) (toGeoDigit digit)
  where
    appendGeoDigit :
      ∀ {d : Nat} →
      Geo.Address d →
      Geo.Digit369 →
      Geo.Address (suc d)
    appendGeoDigit [] d = d ∷ []
    appendGeoDigit (x ∷ xs) d = x ∷ appendGeoDigit xs d

canonicalRootGeoAddress : Geo.Address zero
canonicalRootGeoAddress = []

canonicalThreeSixNineGeoAddress : Geo.Address three
canonicalThreeSixNineGeoAddress =
  Geo.digit3 ∷ Geo.digit6 ∷ Geo.digit9 ∷ []

record SSPPrimeLane369PAdicUltrametricBridge : Set where
  constructor mkSSPPrimeLane369PAdicUltrametricBridge
  field
    bridge :
      Bridge.SSPPrimeLane369PAdicBridge

    depthRefinement :
      Ref.SSPPrimeLane369Refinement (Bridge.depth bridge)

    depthAddress :
      Ref.Lane369Address (Bridge.depth bridge)

    geometryAddress :
      Geo.Address (Bridge.depth bridge)

    depthRefinementMatchesBridge :
      Bridge.depthRefinement bridge ≡ depthRefinement

    depthAddressMatchesDepthRefinement :
      Ref.address depthRefinement ≡ depthAddress

    geometryAddressMatchesDepthAddress :
      geometryAddress ≡ toGeoAddress depthAddress

    prefixReceipt :
      Geo.PrefixMatch (Bridge.depth bridge) geometryAddress geometryAddress

    agreementReceipt :
      Geo.agreementDepth geometryAddress geometryAddress ≡ Bridge.depth bridge

    distanceReceipt :
      Geo.distance geometryAddress geometryAddress ≡ zero

open SSPPrimeLane369PAdicUltrametricBridge public

bridge→ultrametricBridge :
  (bridge : Bridge.SSPPrimeLane369PAdicBridge) →
  SSPPrimeLane369PAdicUltrametricBridge
bridge→ultrametricBridge bridge =
  record
    { bridge =
        bridge
    ; depthRefinement =
        Bridge.depthRefinement bridge
    ; depthAddress =
        Bridge.depthAddress bridge
    ; geometryAddress =
        toGeoAddress (Bridge.depthAddress bridge)
    ; depthRefinementMatchesBridge =
        refl
    ; depthAddressMatchesDepthRefinement =
        Bridge.depthAddressMatches bridge
    ; geometryAddressMatchesDepthAddress =
        refl
    ; prefixReceipt =
        Geo.prefixMatch-refl (toGeoAddress (Bridge.depthAddress bridge))
    ; agreementReceipt =
        Geo.agreementDepth-self (toGeoAddress (Bridge.depthAddress bridge))
    ; distanceReceipt =
        Geo.distance-self-zero (toGeoAddress (Bridge.depthAddress bridge))
    }

canonicalRootPAdicUltrametricBridge :
  SSPPrimeLane369PAdicUltrametricBridge
canonicalRootPAdicUltrametricBridge =
  bridge→ultrametricBridge Bridge.canonicalRootP3Bridge

canonicalThreeSixNinePAdicUltrametricBridge :
  SSPPrimeLane369PAdicUltrametricBridge
canonicalThreeSixNinePAdicUltrametricBridge =
  bridge→ultrametricBridge Bridge.canonicalThreeSixNineP3Bridge

canonicalRootGeoAddressMatchesDepthAddress :
  geometryAddress canonicalRootPAdicUltrametricBridge ≡ canonicalRootGeoAddress
canonicalRootGeoAddressMatchesDepthAddress = refl

canonicalThreeSixNineGeoAddressMatchesDepthAddress :
  geometryAddress canonicalThreeSixNinePAdicUltrametricBridge
  ≡ canonicalThreeSixNineGeoAddress
canonicalThreeSixNineGeoAddressMatchesDepthAddress = refl

canonicalRootPrefixReceipt :
  Geo.PrefixMatch zero canonicalRootGeoAddress canonicalRootGeoAddress
canonicalRootPrefixReceipt = Geo.prefix-zero

canonicalRootAgreementReceipt :
  Geo.agreementDepth canonicalRootGeoAddress canonicalRootGeoAddress ≡ zero
canonicalRootAgreementReceipt = refl

canonicalRootDistanceReceipt :
  Geo.distance canonicalRootGeoAddress canonicalRootGeoAddress ≡ zero
canonicalRootDistanceReceipt = refl

canonicalThreeSixNinePrefixReceipt :
  Geo.PrefixMatch three canonicalThreeSixNineGeoAddress canonicalThreeSixNineGeoAddress
canonicalThreeSixNinePrefixReceipt =
  Geo.prefix-cons Geo.digit3
    (Geo.prefix-cons Geo.digit6
      (Geo.prefix-cons Geo.digit9 Geo.prefix-zero))

canonicalThreeSixNineAgreementReceipt :
  Geo.agreementDepth canonicalThreeSixNineGeoAddress canonicalThreeSixNineGeoAddress
  ≡ three
canonicalThreeSixNineAgreementReceipt = refl

canonicalThreeSixNineDistanceReceipt :
  Geo.distance canonicalThreeSixNineGeoAddress canonicalThreeSixNineGeoAddress ≡ zero
canonicalThreeSixNineDistanceReceipt = refl

canonicalRootBridgeDepthAddressMatches :
  depthAddress canonicalRootPAdicUltrametricBridge ≡ Ref.root
canonicalRootBridgeDepthAddressMatches = refl

canonicalThreeSixNineBridgeDepthAddressMatches :
  depthAddress canonicalThreeSixNinePAdicUltrametricBridge
  ≡ Ref.canonicalThreeSixNineAddress
canonicalThreeSixNineBridgeDepthAddressMatches = refl
