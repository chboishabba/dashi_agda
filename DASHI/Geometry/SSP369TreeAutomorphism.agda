module DASHI.Geometry.SSP369TreeAutomorphism where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (_∷_; [])

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
  )
open import DASHI.TrackedPrimes using (SSP; p7; p11)

actionCommutesWithPrefix :
  ∀ {d : Nat} →
  (p : SSP) →
  (step : UnitActionStep) →
  (a : Lane369Address (suc d)) →
  prefix (actOnAddress p step a) ≡ actOnAddress p step (prefix a)
actionCommutesWithPrefix p step (extend path digit) = refl

actionPreservesAddressDepth :
  ∀ {d : Nat} →
  (p : SSP) →
  (step : UnitActionStep) →
  (a : Lane369Address d) →
  addressDepth (actOnAddress p step a) ≡ d
actionPreservesAddressDepth p step a = refl

actionPreservesPrimeLane :
  ∀ {d : Nat} →
  (p : SSP) →
  (step : UnitActionStep) →
  (r : SSPPrimeLane369Refinement d) →
  SSPPrimeLane369Refinement.primeLane (actOnRefinement p step r)
  ≡ SSPPrimeLane369Refinement.primeLane r
actionPreservesPrimeLane p step r = refl

actionPreservesRefinementDepth :
  ∀ {d : Nat} →
  (p : SSP) →
  (step : UnitActionStep) →
  (r : SSPPrimeLane369Refinement d) →
  Ref.refinementDepth (actOnRefinement p step r) ≡ d
actionPreservesRefinementDepth p step r = refl

p7CanonicalThreeSixNineDigitsAfterGenerator :
  addressDigits (actOnAddress p7 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ digit-3 ∷ []
p7CanonicalThreeSixNineDigitsAfterGenerator = refl

p11CanonicalThreeSixNineDigitsAfterGenerator :
  addressDigits (actOnAddress p11 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ digit-3 ∷ []
p11CanonicalThreeSixNineDigitsAfterGenerator = refl

p7CanonicalThreeSixNinePrefixCommutes :
  prefix (actOnAddress p7 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ actOnAddress p7 canonicalGeneratorStep (prefix canonicalThreeSixNineAddress)
p7CanonicalThreeSixNinePrefixCommutes = refl

p11CanonicalThreeSixNinePrefixCommutes :
  prefix (actOnAddress p11 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ actOnAddress p11 canonicalGeneratorStep (prefix canonicalThreeSixNineAddress)
p11CanonicalThreeSixNinePrefixCommutes = refl

p7CanonicalThreeSixNinePrefixDigitsAfterGenerator :
  prefixDigits (actOnAddress p7 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ []
p7CanonicalThreeSixNinePrefixDigitsAfterGenerator = refl

p11CanonicalThreeSixNinePrefixDigitsAfterGenerator :
  prefixDigits (actOnAddress p11 canonicalGeneratorStep canonicalThreeSixNineAddress)
  ≡ digit-6 ∷ digit-9 ∷ []
p11CanonicalThreeSixNinePrefixDigitsAfterGenerator = refl

p7GeneratorOnCanonicalRefinementAddress :
  address (actOnRefinement p7 canonicalGeneratorStep canonicalThreeSixNineLane369Refinement)
  ≡ actOnAddress p7 canonicalGeneratorStep canonicalThreeSixNineAddress
p7GeneratorOnCanonicalRefinementAddress = refl

p11GeneratorOnCanonicalRefinementAddress :
  address (actOnRefinement p11 canonicalGeneratorStep canonicalThreeSixNineLane369Refinement)
  ≡ actOnAddress p11 canonicalGeneratorStep canonicalThreeSixNineAddress
p11GeneratorOnCanonicalRefinementAddress = refl
