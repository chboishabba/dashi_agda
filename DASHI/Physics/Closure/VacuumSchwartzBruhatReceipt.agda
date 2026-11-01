module DASHI.Physics.Closure.VacuumSchwartzBruhatReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Vacuum Schwartz-Bruhat triviality receipt.
--
-- This is a carrier-side bookkeeping receipt.  It records that the
-- vacuum carrier has no non-trivial compactly supported locally constant
-- excitation component in the staged Schwartz-Bruhat test sector.  It
-- does not construct a continuum interacting vacuum representation.

data VacuumContinuumPromotionAuthorityToken : Set where

vacuumContinuumPromotionBlockedHere :
  VacuumContinuumPromotionAuthorityToken →
  ⊥
vacuumContinuumPromotionBlockedHere ()

vacuumSectorLabel : String
vacuumSectorLabel =
  "carrier-vacuum-sector"

schwartzBruhatTestSectorLabel : String
schwartzBruhatTestSectorLabel =
  "compactly-supported-locally-constant-Schwartz-Bruhat-test-sector"

record VacuumSchwartzBruhatReceipt : Setω where
  field
    carrierSector :
      String

    carrierSector-v :
      carrierSector ≡ vacuumSectorLabel

    testSector :
      String

    testSector-v :
      testSector ≡ schwartzBruhatTestSectorLabel

    vacuumHasNoNontrivialTestExcitation :
      Bool

    vacuumHasNoNontrivialTestExcitation-v :
      vacuumHasNoNontrivialTestExcitation ≡ true

    vacuumSchwartzBruhatTrivialityRecorded :
      Bool

    vacuumSchwartzBruhatTrivialityRecorded-v :
      vacuumSchwartzBruhatTrivialityRecorded ≡ true

    carrierSideOnly :
      Bool

    carrierSideOnly-v :
      carrierSideOnly ≡ true

    continuumVacuumRepresentationConstructed :
      Bool

    continuumVacuumRepresentationConstructed-v :
      continuumVacuumRepresentationConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromoted-v :
      clayYangMillsPromoted ≡ false

    noContinuumPromotionWithoutAuthority :
      VacuumContinuumPromotionAuthorityToken →
      ⊥

    governanceBoundary :
      List String

open VacuumSchwartzBruhatReceipt public

canonicalVacuumSchwartzBruhatReceipt :
  VacuumSchwartzBruhatReceipt
canonicalVacuumSchwartzBruhatReceipt =
  record
    { carrierSector =
        vacuumSectorLabel
    ; carrierSector-v =
        refl
    ; testSector =
        schwartzBruhatTestSectorLabel
    ; testSector-v =
        refl
    ; vacuumHasNoNontrivialTestExcitation =
        true
    ; vacuumHasNoNontrivialTestExcitation-v =
        refl
    ; vacuumSchwartzBruhatTrivialityRecorded =
        true
    ; vacuumSchwartzBruhatTrivialityRecorded-v =
        refl
    ; carrierSideOnly =
        true
    ; carrierSideOnly-v =
        refl
    ; continuumVacuumRepresentationConstructed =
        false
    ; continuumVacuumRepresentationConstructed-v =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromoted-v =
        refl
    ; noContinuumPromotionWithoutAuthority =
        vacuumContinuumPromotionBlockedHere
    ; governanceBoundary =
        "records vacuum Schwartz-Bruhat test-sector triviality on the carrier side"
        ∷ "does not construct a continuum interacting vacuum representation"
        ∷ "does not promote a Clay Yang-Mills mass-gap claim"
        ∷ []
    }

canonicalVacuumSchwartzBruhatTrivialityIsCarrierOnly :
  carrierSideOnly canonicalVacuumSchwartzBruhatReceipt ≡ true
canonicalVacuumSchwartzBruhatTrivialityIsCarrierOnly =
  refl

canonicalVacuumSchwartzBruhatDoesNotPromoteClay :
  clayYangMillsPromoted canonicalVacuumSchwartzBruhatReceipt ≡ false
canonicalVacuumSchwartzBruhatDoesNotPromoteClay =
  refl
