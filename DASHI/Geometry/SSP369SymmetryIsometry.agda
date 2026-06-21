module DASHI.Geometry.SSP369SymmetryIsometry where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.SSPPrimeLaneUnitAction as Action using
  ( UnitActionStep
  ; actOnAddress
  ; canonicalGeneratorStep
  )
open import DASHI.Foundations.SSPPrimeLane369Refinement as Ref using
  ( Lane369Address
  ; canonicalThreeSixNineAddress
  )
open import DASHI.Physics.Closure.SSPPrimeLane369PAdicUltrametricBridge using
  ( toGeoAddress )
open import DASHI.Geometry.SSP369Ultrametric as Geo using
  ( Address
  ; PrefixMatch
  ; agreementDepth
  ; agreementDepth-self
  ; distance
  ; distance-self-zero
  ; prefixMatch-refl
  )
open import DASHI.TrackedPrimes using (SSP; p7; p11)

actedGeoAddress :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  Ref.Lane369Address d →
  Geo.Address d
actedGeoAddress p step a = toGeoAddress (actOnAddress p step a)

record SSP369SymmetryIsometryReceipt (d : Nat) : Set where
  constructor mkSSP369SymmetryIsometryReceipt
  field
    primeLane : SSP
    rawStep : UnitActionStep
    sourceAddress : Ref.Lane369Address d
    transportedAddress : Geo.Address d
    transportedAddressMatches :
      transportedAddress ≡ actedGeoAddress primeLane rawStep sourceAddress
    selfPrefixWitness :
      PrefixMatch d transportedAddress transportedAddress
    selfAgreementWitness :
      agreementDepth transportedAddress transportedAddress ≡ d
    selfDistanceWitness :
      distance transportedAddress transportedAddress ≡ zero

open SSP369SymmetryIsometryReceipt public

symmetryIsometryReceipt :
  ∀ {d : Nat} →
  SSP →
  UnitActionStep →
  Ref.Lane369Address d →
  SSP369SymmetryIsometryReceipt d
symmetryIsometryReceipt p step a =
  mkSSP369SymmetryIsometryReceipt
    p
    step
    a
    (actedGeoAddress p step a)
    refl
    (prefixMatch-refl (actedGeoAddress p step a))
    (agreementDepth-self (actedGeoAddress p step a))
    (distance-self-zero (actedGeoAddress p step a))

canonicalP7GeneratorIsometryReceipt :
  SSP369SymmetryIsometryReceipt (suc (suc (suc zero)))
canonicalP7GeneratorIsometryReceipt =
  symmetryIsometryReceipt p7 canonicalGeneratorStep canonicalThreeSixNineAddress

canonicalP11GeneratorIsometryReceipt :
  SSP369SymmetryIsometryReceipt (suc (suc (suc zero)))
canonicalP11GeneratorIsometryReceipt =
  symmetryIsometryReceipt p11 canonicalGeneratorStep canonicalThreeSixNineAddress

canonicalP7GeneratorAgreementIsDepth3 :
  Geo.agreementDepth
    (transportedAddress canonicalP7GeneratorIsometryReceipt)
    (transportedAddress canonicalP7GeneratorIsometryReceipt)
  ≡ suc (suc (suc zero))
canonicalP7GeneratorAgreementIsDepth3 = selfAgreementWitness canonicalP7GeneratorIsometryReceipt

canonicalP11GeneratorAgreementIsDepth3 :
  Geo.agreementDepth
    (transportedAddress canonicalP11GeneratorIsometryReceipt)
    (transportedAddress canonicalP11GeneratorIsometryReceipt)
  ≡ suc (suc (suc zero))
canonicalP11GeneratorAgreementIsDepth3 = selfAgreementWitness canonicalP11GeneratorIsometryReceipt

canonicalP7GeneratorDistanceIsZero :
  Geo.distance
    (transportedAddress canonicalP7GeneratorIsometryReceipt)
    (transportedAddress canonicalP7GeneratorIsometryReceipt)
  ≡ zero
canonicalP7GeneratorDistanceIsZero = selfDistanceWitness canonicalP7GeneratorIsometryReceipt

canonicalP11GeneratorDistanceIsZero :
  Geo.distance
    (transportedAddress canonicalP11GeneratorIsometryReceipt)
    (transportedAddress canonicalP11GeneratorIsometryReceipt)
  ≡ zero
canonicalP11GeneratorDistanceIsZero = selfDistanceWitness canonicalP11GeneratorIsometryReceipt
