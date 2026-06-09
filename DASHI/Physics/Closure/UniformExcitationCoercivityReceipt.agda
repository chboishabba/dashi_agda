module DASHI.Physics.Closure.UniformExcitationCoercivityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Uniform excitation coercivity receipt.
--
-- The receipt records a carrier-side coercivity obligation: every
-- non-vacuum excitation in the bounded carrier sector must be separated
-- from the vacuum by the internal carrier energy functional.  This is not
-- a continuum Yang-Mills or Clay mass-gap proof.

data UniformExcitationCoercivityPromotionToken : Set where

uniformExcitationCoercivityPromotionBlockedHere :
  UniformExcitationCoercivityPromotionToken →
  ⊥
uniformExcitationCoercivityPromotionBlockedHere ()

boundedCarrierExcitationSectorLabel : String
boundedCarrierExcitationSectorLabel =
  "bounded-carrier-excitation-sector"

internalCarrierEnergyFunctionalLabel : String
internalCarrierEnergyFunctionalLabel =
  "internal-carrier-energy-functional"

record UniformExcitationCoercivityReceipt : Setω where
  field
    excitationSector :
      String

    excitationSector-v :
      excitationSector ≡ boundedCarrierExcitationSectorLabel

    energyFunctional :
      String

    energyFunctional-v :
      energyFunctional ≡ internalCarrierEnergyFunctionalLabel

    nonVacuumExcitationsDetected :
      Bool

    nonVacuumExcitationsDetected-v :
      nonVacuumExcitationsDetected ≡ true

    uniformCarrierCoercivityRequired :
      Bool

    uniformCarrierCoercivityRequired-v :
      uniformCarrierCoercivityRequired ≡ true

    uniformCarrierCoercivityDischargedHere :
      Bool

    uniformCarrierCoercivityDischargedHere-v :
      uniformCarrierCoercivityDischargedHere ≡ false

    obligationSurface :
      String

    obligationSurface-v :
      obligationSurface ≡
        "prove-uniform-positive-internal-carrier-energy-on-non-vacuum-excitations"

    carrierSideReceiptOnly :
      Bool

    carrierSideReceiptOnly-v :
      carrierSideReceiptOnly ≡ true

    continuumUniformCoercivityProved :
      Bool

    continuumUniformCoercivityProved-v :
      continuumUniformCoercivityProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromoted-v :
      clayYangMillsPromoted ≡ false

    noPromotionWithoutAuthority :
      UniformExcitationCoercivityPromotionToken →
      ⊥

    governanceBoundary :
      List String

open UniformExcitationCoercivityReceipt public

canonicalUniformExcitationCoercivityReceipt :
  UniformExcitationCoercivityReceipt
canonicalUniformExcitationCoercivityReceipt =
  record
    { excitationSector =
        boundedCarrierExcitationSectorLabel
    ; excitationSector-v =
        refl
    ; energyFunctional =
        internalCarrierEnergyFunctionalLabel
    ; energyFunctional-v =
        refl
    ; nonVacuumExcitationsDetected =
        true
    ; nonVacuumExcitationsDetected-v =
        refl
    ; uniformCarrierCoercivityRequired =
        true
    ; uniformCarrierCoercivityRequired-v =
        refl
    ; uniformCarrierCoercivityDischargedHere =
        false
    ; uniformCarrierCoercivityDischargedHere-v =
        refl
    ; obligationSurface =
        "prove-uniform-positive-internal-carrier-energy-on-non-vacuum-excitations"
    ; obligationSurface-v =
        refl
    ; carrierSideReceiptOnly =
        true
    ; carrierSideReceiptOnly-v =
        refl
    ; continuumUniformCoercivityProved =
        false
    ; continuumUniformCoercivityProved-v =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromoted-v =
        refl
    ; noPromotionWithoutAuthority =
        uniformExcitationCoercivityPromotionBlockedHere
    ; governanceBoundary =
        "records uniform excitation coercivity as a carrier-side obligation"
        ∷ "internal carrier energy gap is not identified with a physical mass gap here"
        ∷ "continuum coercivity and Clay Yang-Mills promotion remain false"
        ∷ []
    }

canonicalUniformExcitationCoercivityIsObligation :
  uniformCarrierCoercivityRequired
    canonicalUniformExcitationCoercivityReceipt
  ≡
  true
canonicalUniformExcitationCoercivityIsObligation =
  refl

canonicalUniformExcitationCoercivityNotDischargedHere :
  uniformCarrierCoercivityDischargedHere
    canonicalUniformExcitationCoercivityReceipt
  ≡
  false
canonicalUniformExcitationCoercivityNotDischargedHere =
  refl

canonicalUniformExcitationCoercivityDoesNotPromoteClay :
  clayYangMillsPromoted canonicalUniformExcitationCoercivityReceipt ≡ false
canonicalUniformExcitationCoercivityDoesNotPromoteClay =
  refl
