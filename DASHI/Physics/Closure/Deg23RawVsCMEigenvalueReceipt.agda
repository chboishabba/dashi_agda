module DASHI.Physics.Closure.Deg23RawVsCMEigenvalueReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23FromT13HeckeReceipt as T13
import DASHI.Physics.Closure.EichlerSelbergAtCMPointReceipt as CM

data Deg23InvariantDistinction : Set where
  rawHeckeDegreeCountsCorrespondencePreimages :
    Deg23InvariantDistinction

  cmEigenvalueActsOnCohomologyClass :
    Deg23InvariantDistinction

  residualNotEigenvalueCorrection :
    Deg23InvariantDistinction

canonicalDeg23InvariantDistinctions :
  List Deg23InvariantDistinction
canonicalDeg23InvariantDistinctions =
  rawHeckeDegreeCountsCorrespondencePreimages
  ∷ cmEigenvalueActsOnCohomologyClass
  ∷ residualNotEigenvalueCorrection
  ∷ []

record Deg23RawVsCMEigenvalueReceipt : Setω where
  field
    t13Receipt :
      T13.Deg23FromT13HeckeReceipt

    rawDegreeFourteen :
      T13.t13Degree t13Receipt ≡ 14

    cmReceipt :
      CM.EichlerSelbergAtCMPointReceipt

    cmEigenvalueZero :
      CM.localCMEigenvalue cmReceipt ≡ 0

    rawDegreeAndCMEigenvalueDifferent :
      Bool

    rawDegreeAndCMEigenvalueDifferentIsTrue :
      rawDegreeAndCMEigenvalueDifferent ≡ true

    deg23ResidualFromCMEigenvalue :
      Bool

    deg23ResidualFromCMEigenvalueIsFalse :
      deg23ResidualFromCMEigenvalue ≡ false

    deg23ResidualSourceIdentified :
      Bool

    deg23ResidualSourceIdentifiedIsFalse :
      deg23ResidualSourceIdentified ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    distinctions :
      List Deg23InvariantDistinction

    distinctionsAreCanonical :
      distinctions ≡ canonicalDeg23InvariantDistinctions

open Deg23RawVsCMEigenvalueReceipt public

canonicalDeg23RawVsCMEigenvalueReceipt :
  Deg23RawVsCMEigenvalueReceipt
canonicalDeg23RawVsCMEigenvalueReceipt =
  record
    { t13Receipt =
        T13.canonicalDeg23FromT13HeckeReceipt
    ; rawDegreeFourteen =
        refl
    ; cmReceipt =
        CM.canonicalEichlerSelbergAtCMPointReceipt
    ; cmEigenvalueZero =
        refl
    ; rawDegreeAndCMEigenvalueDifferent =
        true
    ; rawDegreeAndCMEigenvalueDifferentIsTrue =
        refl
    ; deg23ResidualFromCMEigenvalue =
        false
    ; deg23ResidualFromCMEigenvalueIsFalse =
        refl
    ; deg23ResidualSourceIdentified =
        false
    ; deg23ResidualSourceIdentifiedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; distinctions =
        canonicalDeg23InvariantDistinctions
    ; distinctionsAreCanonical =
        refl
    }

deg23RawVsCMEigenvaluePhysicalCKMFalse :
  physicalCKMPromoted canonicalDeg23RawVsCMEigenvalueReceipt ≡ false
deg23RawVsCMEigenvaluePhysicalCKMFalse =
  refl
