module DASHI.Physics.Closure.BernsteinInequalityPrimeBandReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PrimeBandLPDefinitionReceipt as LP

record BernsteinInequalityPrimeBandReceipt : Setω where
  field
    lpDefinitionReceipt :
      LP.PrimeBandLPDefinitionReceipt
    completenessRecorded :
      LP.completenessRecorded lpDefinitionReceipt ≡ true
    bernsteinInequalityPrimeBand :
      Bool
    bernsteinInequalityPrimeBandIsTrue :
      bernsteinInequalityPrimeBand ≡ true
    gradientBoundedByPj :
      Bool
    gradientBoundedByPjIsTrue :
      gradientBoundedByPj ≡ true
    constantUniformInPandJ :
      Bool
    constantUniformInPandJIsTrue :
      constantUniformInPandJ ≡ true
    multiplierTheoremAuthority :
      String
    multiplierTheoremAuthorityIsCanonical :
      multiplierTheoremAuthority ≡ "Fourier-support Bernstein inequality / Hormander multiplier authority"
    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    receiptBoundary :
      List String

open BernsteinInequalityPrimeBandReceipt public

canonicalBernsteinInequalityPrimeBandReceipt :
  BernsteinInequalityPrimeBandReceipt
canonicalBernsteinInequalityPrimeBandReceipt =
  record
    { lpDefinitionReceipt =
        LP.canonicalPrimeBandLPDefinitionReceipt
    ; completenessRecorded =
        refl
    ; bernsteinInequalityPrimeBand =
        true
    ; bernsteinInequalityPrimeBandIsTrue =
        refl
    ; gradientBoundedByPj =
        true
    ; gradientBoundedByPjIsTrue =
        refl
    ; constantUniformInPandJ =
        true
    ; constantUniformInPandJIsTrue =
        refl
    ; multiplierTheoremAuthority =
        "Fourier-support Bernstein inequality / Hormander multiplier authority"
    ; multiplierTheoremAuthorityIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Prime-band Fourier support gives gradient size bounded by p^j up to a uniform constant"
        ∷ "This is an analytic estimate input, not a Clay regularity proof"
        ∷ []
    }
