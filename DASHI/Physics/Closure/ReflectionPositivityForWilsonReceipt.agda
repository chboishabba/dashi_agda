module DASHI.Physics.Closure.ReflectionPositivityForWilsonReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.WilsonActionOn3PlusOneLatticeReceipt as Wilson

data WilsonReflectionPositivityAuthority : Set where
  osterwalderSeilerLatticeGaugePositivity :
    WilsonReflectionPositivityAuthority

  glimmJaffeConstructiveQFTReference :
    WilsonReflectionPositivityAuthority

  transferMatrixPositiveKernel :
    WilsonReflectionPositivityAuthority

canonicalWilsonReflectionAuthorities :
  List WilsonReflectionPositivityAuthority
canonicalWilsonReflectionAuthorities =
  osterwalderSeilerLatticeGaugePositivity
  ∷ glimmJaffeConstructiveQFTReference
  ∷ transferMatrixPositiveKernel
  ∷ []

reflectionMapLabel : String
reflectionMapLabel =
  "theta maps U_i(d,d+1) to U_i(-d-1,-d)^dagger and reverses positive Euclidean time"

record ReflectionPositivityForWilsonReceipt : Setω where
  field
    wilsonReceipt :
      Wilson.WilsonActionOn3PlusOneLatticeReceipt

    wilsonActionDefined :
      Wilson.wilsonActionDefinedOnCarrierLattice wilsonReceipt ≡ true

    reflectionMap :
      String

    reflectionMapIsCanonical :
      reflectionMap ≡ reflectionMapLabel

    finiteLatticeReflectionPositivityInherited :
      Bool

    finiteLatticeReflectionPositivityInheritedIsTrue :
      finiteLatticeReflectionPositivityInherited ≡ true

    continuumReflectionPositivityProved :
      Bool

    continuumReflectionPositivityProvedIsFalse :
      continuumReflectionPositivityProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    authorities :
      List WilsonReflectionPositivityAuthority

    authoritiesAreCanonical :
      authorities ≡ canonicalWilsonReflectionAuthorities

open ReflectionPositivityForWilsonReceipt public

canonicalReflectionPositivityForWilsonReceipt :
  ReflectionPositivityForWilsonReceipt
canonicalReflectionPositivityForWilsonReceipt =
  record
    { wilsonReceipt =
        Wilson.canonicalWilsonActionOn3PlusOneLatticeReceipt
    ; wilsonActionDefined =
        refl
    ; reflectionMap =
        reflectionMapLabel
    ; reflectionMapIsCanonical =
        refl
    ; finiteLatticeReflectionPositivityInherited =
        true
    ; finiteLatticeReflectionPositivityInheritedIsTrue =
        refl
    ; continuumReflectionPositivityProved =
        false
    ; continuumReflectionPositivityProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; authorities =
        canonicalWilsonReflectionAuthorities
    ; authoritiesAreCanonical =
        refl
    }

reflectionPositivityForWilsonKeepsClayFalse :
  clayYangMillsPromoted canonicalReflectionPositivityForWilsonReceipt ≡ false
reflectionPositivityForWilsonKeepsClayFalse =
  refl

reflectionPositivityForWilsonKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalReflectionPositivityForWilsonReceipt
  ≡
  false
reflectionPositivityForWilsonKeepsTerminalFalse =
  refl
