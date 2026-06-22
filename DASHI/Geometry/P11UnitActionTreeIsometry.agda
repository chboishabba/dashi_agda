module DASHI.Geometry.P11UnitActionTreeIsometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.P11UnitGroupC10Witness using
  ( P11UnitClass
  ; p11UnitGenerator
  ; p11UnitHalfTurnElement
  ; p11UnitIdentity
  ; toStep
  )
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( actOnAddress
  ; actOnRefinement
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement as Ref using
  ( Lane369Address
  ; SSPPrimeLane369Refinement
  ; address
  ; addressDepth
  ; addressDigits
  ; canonicalThreeSixNineAddress
  ; canonicalThreeSixNineLane369Refinement
  ; digit-3
  ; digit-6
  ; digit-9
  ; extend
  ; prefix
  ; root
  )
open import DASHI.Geometry.SSP369SymmetryIsometry as Iso using
  ( actedGeoAddress )
open import DASHI.Geometry.SSP369TreeAutomorphism as Auto using
  ( actionCommutesWithPrefix
  ; actionPreservesAddressDepth
  )
open import DASHI.Geometry.SSP369Ultrametric as Geo using
  ( distance
  ; distance-self-zero
  )
open import DASHI.TrackedPrimes using (p11)

actOnP11Address :
  ∀ {d : Nat} →
  P11UnitClass →
  Lane369Address d →
  Lane369Address d
actOnP11Address q a = actOnAddress p11 (toStep q) a

identityActsOnP11Address :
  ∀ {d : Nat} →
  (a : Lane369Address d) →
  actOnP11Address p11UnitIdentity a ≡ a
identityActsOnP11Address root = refl
identityActsOnP11Address (extend path digit)
  rewrite identityActsOnP11Address path = refl

generatorActsOnCanonicalAddressDigits :
  addressDigits (actOnP11Address p11UnitGenerator canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ digit-3 ∷ []
generatorActsOnCanonicalAddressDigits = refl

halfTurnActsOnCanonicalAddressDigits :
  addressDigits (actOnP11Address p11UnitHalfTurnElement canonicalThreeSixNineAddress)
  ≡ digit-9 ∷ digit-3 ∷ digit-6 ∷ []
halfTurnActsOnCanonicalAddressDigits = refl

generatorCommutesWithPrefixOnCanonicalAddress :
  prefix (actOnP11Address p11UnitGenerator canonicalThreeSixNineAddress)
  ≡ actOnP11Address p11UnitGenerator (prefix canonicalThreeSixNineAddress)
generatorCommutesWithPrefixOnCanonicalAddress =
  actionCommutesWithPrefix p11 (toStep p11UnitGenerator) canonicalThreeSixNineAddress

halfTurnCommutesWithPrefixOnCanonicalAddress :
  prefix (actOnP11Address p11UnitHalfTurnElement canonicalThreeSixNineAddress)
  ≡ actOnP11Address p11UnitHalfTurnElement (prefix canonicalThreeSixNineAddress)
halfTurnCommutesWithPrefixOnCanonicalAddress =
  actionCommutesWithPrefix p11 (toStep p11UnitHalfTurnElement) canonicalThreeSixNineAddress

generatorPreservesCanonicalDepth :
  addressDepth (actOnP11Address p11UnitGenerator canonicalThreeSixNineAddress)
  ≡ suc (suc (suc zero))
generatorPreservesCanonicalDepth =
  actionPreservesAddressDepth p11 (toStep p11UnitGenerator) canonicalThreeSixNineAddress

halfTurnPreservesCanonicalDepth :
  addressDepth (actOnP11Address p11UnitHalfTurnElement canonicalThreeSixNineAddress)
  ≡ suc (suc (suc zero))
halfTurnPreservesCanonicalDepth =
  actionPreservesAddressDepth p11 (toStep p11UnitHalfTurnElement) canonicalThreeSixNineAddress

generatorCanonicalSelfDistanceIsZero :
  distance
    (Iso.actedGeoAddress p11 (toStep p11UnitGenerator) canonicalThreeSixNineAddress)
    (Iso.actedGeoAddress p11 (toStep p11UnitGenerator) canonicalThreeSixNineAddress)
  ≡ zero
generatorCanonicalSelfDistanceIsZero =
  distance-self-zero
    (Iso.actedGeoAddress p11 (toStep p11UnitGenerator) canonicalThreeSixNineAddress)

halfTurnCanonicalSelfDistanceIsZero :
  distance
    (Iso.actedGeoAddress p11 (toStep p11UnitHalfTurnElement) canonicalThreeSixNineAddress)
    (Iso.actedGeoAddress p11 (toStep p11UnitHalfTurnElement) canonicalThreeSixNineAddress)
  ≡ zero
halfTurnCanonicalSelfDistanceIsZero =
  distance-self-zero
    (Iso.actedGeoAddress p11 (toStep p11UnitHalfTurnElement) canonicalThreeSixNineAddress)
