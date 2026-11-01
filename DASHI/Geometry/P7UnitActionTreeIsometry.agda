module DASHI.Geometry.P7UnitActionTreeIsometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.P7UnitGroupC6Witness using ()
open import DASHI.Foundations.P7HexTruthActionQuotient using ()
open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( actOnAddress
  ; actOnRefinement
  )
open import DASHI.Foundations.SSPPrimeLaneUnitGroup using
  ( P7UnitClass
  ; p7UnitGenerator
  ; p7UnitIdentity
  ; p7UnitMobiusElement
  ; toStep
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
  ; prefixDigits
  ; root
  )
open import DASHI.Geometry.SSP369SymmetryIsometry as Iso using
  ( actedGeoAddress )
open import DASHI.Geometry.SSP369TreeAutomorphism as Auto using
  ( actionCommutesWithPrefix
  ; actionPreservesAddressDepth
  ; actionPreservesRefinementDepth
  )
open import DASHI.Geometry.SSP369Ultrametric as Geo using
  ( agreementDepth
  ; distance
  ; distance-self-zero
  )
open import DASHI.TrackedPrimes using (p7)

actOnP7Address :
  ∀ {d : Nat} →
  P7UnitClass →
  Lane369Address d →
  Lane369Address d
actOnP7Address q a = actOnAddress p7 (toStep q) a

actOnP7Refinement :
  ∀ {d : Nat} →
  P7UnitClass →
  SSPPrimeLane369Refinement d →
  SSPPrimeLane369Refinement d
actOnP7Refinement q r = actOnRefinement p7 (toStep q) r

identityActsOnP7Address :
  ∀ {d : Nat} →
  (a : Lane369Address d) →
  actOnP7Address p7UnitIdentity a ≡ a
identityActsOnP7Address root = refl
identityActsOnP7Address (extend path digit)
  rewrite identityActsOnP7Address path = refl

mobiusActsTriviallyOnP7Address :
  ∀ {d : Nat} →
  (a : Lane369Address d) →
  actOnP7Address p7UnitMobiusElement a ≡ a
mobiusActsTriviallyOnP7Address root = refl
mobiusActsTriviallyOnP7Address (extend path digit)
  rewrite mobiusActsTriviallyOnP7Address path = refl

generatorActsOnCanonicalAddressDigits :
  addressDigits (actOnP7Address p7UnitGenerator canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ digit-3 ∷ []
generatorActsOnCanonicalAddressDigits = refl

mobiusActsOnCanonicalAddressDigits :
  addressDigits (actOnP7Address p7UnitMobiusElement canonicalThreeSixNineAddress)
  ≡ digit-3 ∷ digit-6 ∷ digit-9 ∷ []
mobiusActsOnCanonicalAddressDigits = refl

generatorCommutesWithPrefixOnCanonicalAddress :
  prefix (actOnP7Address p7UnitGenerator canonicalThreeSixNineAddress)
  ≡ actOnP7Address p7UnitGenerator (prefix canonicalThreeSixNineAddress)
generatorCommutesWithPrefixOnCanonicalAddress =
  actionCommutesWithPrefix p7 (toStep p7UnitGenerator) canonicalThreeSixNineAddress

mobiusCommutesWithPrefixOnCanonicalAddress :
  prefix (actOnP7Address p7UnitMobiusElement canonicalThreeSixNineAddress)
  ≡ actOnP7Address p7UnitMobiusElement (prefix canonicalThreeSixNineAddress)
mobiusCommutesWithPrefixOnCanonicalAddress =
  actionCommutesWithPrefix p7 (toStep p7UnitMobiusElement) canonicalThreeSixNineAddress

generatorPreservesCanonicalDepth :
  addressDepth (actOnP7Address p7UnitGenerator canonicalThreeSixNineAddress)
  ≡ suc (suc (suc zero))
generatorPreservesCanonicalDepth =
  actionPreservesAddressDepth p7 (toStep p7UnitGenerator) canonicalThreeSixNineAddress

mobiusPreservesCanonicalDepth :
  addressDepth (actOnP7Address p7UnitMobiusElement canonicalThreeSixNineAddress)
  ≡ suc (suc (suc zero))
mobiusPreservesCanonicalDepth =
  actionPreservesAddressDepth p7 (toStep p7UnitMobiusElement) canonicalThreeSixNineAddress

generatorActsOnCanonicalRefinement :
  address (actOnP7Refinement p7UnitGenerator canonicalThreeSixNineLane369Refinement)
  ≡ actOnP7Address p7UnitGenerator canonicalThreeSixNineAddress
generatorActsOnCanonicalRefinement = refl

mobiusActsOnCanonicalRefinement :
  address (actOnP7Refinement p7UnitMobiusElement canonicalThreeSixNineLane369Refinement)
  ≡ canonicalThreeSixNineAddress
mobiusActsOnCanonicalRefinement = refl

generatorCanonicalSelfDistanceIsZero :
  distance
    (Iso.actedGeoAddress p7 (toStep p7UnitGenerator) canonicalThreeSixNineAddress)
    (Iso.actedGeoAddress p7 (toStep p7UnitGenerator) canonicalThreeSixNineAddress)
  ≡ zero
generatorCanonicalSelfDistanceIsZero =
  distance-self-zero
    (Iso.actedGeoAddress p7 (toStep p7UnitGenerator) canonicalThreeSixNineAddress)

mobiusCanonicalSelfDistanceIsZero :
  distance
    (Iso.actedGeoAddress p7 (toStep p7UnitMobiusElement) canonicalThreeSixNineAddress)
    (Iso.actedGeoAddress p7 (toStep p7UnitMobiusElement) canonicalThreeSixNineAddress)
  ≡ zero
mobiusCanonicalSelfDistanceIsZero =
  distance-self-zero
    (Iso.actedGeoAddress p7 (toStep p7UnitMobiusElement) canonicalThreeSixNineAddress)
