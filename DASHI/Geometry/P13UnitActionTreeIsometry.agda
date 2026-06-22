module DASHI.Geometry.P13UnitActionTreeIsometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( UnitActionStep
  ; actOnAddress
  ; actOnRefinement
  ; canonicalGeneratorStep
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
  ( distance
  ; distance-self-zero
  )
open import DASHI.TrackedPrimes using (p13)

actOnP13Address :
  ∀ {d : Nat} →
  UnitActionStep →
  Lane369Address d →
  Lane369Address d
actOnP13Address step a = actOnAddress p13 step a

actOnP13Refinement :
  ∀ {d : Nat} →
  UnitActionStep →
  SSPPrimeLane369Refinement d →
  SSPPrimeLane369Refinement d
actOnP13Refinement step r = actOnRefinement p13 step r

identityActsOnP13Address :
  ∀ {d : Nat} →
  (a : Lane369Address d) →
  actOnP13Address zero a ≡ a
identityActsOnP13Address root = refl
identityActsOnP13Address (extend path digit)
  rewrite identityActsOnP13Address path = refl

generatorActsOnCanonicalAddressDigits :
  addressDigits (actOnP13Address canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ digit-3 ∷ []
generatorActsOnCanonicalAddressDigits = refl

generatorActsOnCanonicalPrefixDigits :
  prefixDigits (actOnP13Address canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ []
generatorActsOnCanonicalPrefixDigits = refl

generatorCommutesWithPrefixOnCanonicalAddress :
  prefix (actOnP13Address canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ actOnP13Address canonicalGeneratorStep (prefix canonicalThreeSixNineAddress)
generatorCommutesWithPrefixOnCanonicalAddress =
  actionCommutesWithPrefix p13 canonicalGeneratorStep canonicalThreeSixNineAddress

generatorPreservesCanonicalDepth :
  addressDepth (actOnP13Address canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ suc (suc (suc zero))
generatorPreservesCanonicalDepth =
  actionPreservesAddressDepth p13 canonicalGeneratorStep canonicalThreeSixNineAddress

generatorActsOnCanonicalRefinement :
  address (actOnP13Refinement canonicalGeneratorStep canonicalThreeSixNineLane369Refinement)
  ≡ actOnP13Address canonicalGeneratorStep canonicalThreeSixNineAddress
generatorActsOnCanonicalRefinement = refl

generatorPreservesCanonicalRefinementDepth :
  Ref.refinementDepth (actOnP13Refinement canonicalGeneratorStep canonicalThreeSixNineLane369Refinement)
  ≡ suc (suc (suc zero))
generatorPreservesCanonicalRefinementDepth =
  actionPreservesRefinementDepth p13 canonicalGeneratorStep canonicalThreeSixNineLane369Refinement

generatorCanonicalSelfDistanceIsZero :
  distance
    (Iso.actedGeoAddress p13 canonicalGeneratorStep canonicalThreeSixNineAddress)
    (Iso.actedGeoAddress p13 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ zero
generatorCanonicalSelfDistanceIsZero =
  distance-self-zero
    (Iso.actedGeoAddress p13 canonicalGeneratorStep canonicalThreeSixNineAddress)

