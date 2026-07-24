module DASHI.Empirical.PNFMeasurementIdentifiability where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record ObservationFamily (Hidden Observable : Set) : Set₁ where
  field
    observe : Hidden → Observable
    instrumentReceipt errorModelReceipt contextReceipt : String

open ObservationFamily public

record ObservationalEquivalence
    {Hidden Observable : Set}
    (family : ObservationFamily Hidden Observable) : Set₁ where
  field
    left right : Hidden
    sameObservable : observe family left ≡ observe family right
    hiddenDistinctReceipt : String

open ObservationalEquivalence public

record IdentifiabilityAuthority
    {Hidden Observable : Set}
    (family : ObservationFamily Hidden Observable) : Set₁ where
  field
    Recover : Observable → Hidden → Set
    uniqueRecovery : Set
    validationReceipt : String

open IdentifiabilityAuthority public

record MeasurementAuthorityBoundary : Set where
  constructor measurementAuthorityBoundary
  field
    scalarObservableRecoversHiddenStateAutomatically : Bool
    scalarObservableRecoversHiddenStateAutomaticallyIsFalse :
      scalarObservableRecoversHiddenStateAutomatically ≡ false
    formalMeasurementContractIsClinicalAuthority : Bool
    formalMeasurementContractIsClinicalAuthorityIsFalse :
      formalMeasurementContractIsClinicalAuthority ≡ false

canonicalMeasurementAuthorityBoundary : MeasurementAuthorityBoundary
canonicalMeasurementAuthorityBoundary =
  measurementAuthorityBoundary false refl false refl
