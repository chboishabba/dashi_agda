module DASHI.Law.SensibLawWoogarooSourceAcceptanceNonPromotion20261109Exact where

-- EPBC 2019/8575 original-document provenance firewall.
-- File hash/revision agreement is a technical consistency property.
-- It does NOT establish which agency-approved original a file represents.
-- This is a mathematical projection counterexample; neither witness
-- asserts that an actual October file has/has not been authenticated.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.AffineProductIdentifiabilityExact as Projection

-- First coordinate: manifest hash and revision consistency.
-- Second coordinate: independently paid regulator acceptance.
-- The intake checker only observes the FIRST coordinate.
intakeProjection : Bool → Bool → Bool
intakeProjection hashesAndRevisionAgree independentlyAccepted =
  hashesAndRevisionAgree

sameReportedIntakeForOppositeAgencyStates :
  intakeProjection true false ≡ intakeProjection true true
sameReportedIntakeForOppositeAgencyStates = refl

falseIsNotTrue : false ≡ true → ⊥
falseIsNotTrue ()

-- No decoder that sees ONLY the checked manifest/bytes projection
-- can correctly report independent agency acceptance in every world.
original20198575HashCannotProveAgencyAcceptance :
  (decode : Bool → Bool) →
  ((hashAgreement agencyAccepted : Bool) →
    decode (intakeProjection hashAgreement agencyAccepted)
      ≡ agencyAccepted) →
  ⊥
original20198575HashCannotProveAgencyAcceptance =
  Projection.noRightDecoderAtCollision
    intakeProjection
    sameReportedIntakeForOppositeAgencyStates
    falseIsNotTrue

-- The same impossibility persists even if the checksum status is
-- re-encoded as a number, string, tuple or any other output type.
original20198575HashEncodingCannotProveAgencyAcceptance :
  {O : Set} (encode : Bool → O) →
  (decode : O → Bool) →
  ((hashAgreement agencyAccepted : Bool) →
    decode (encode (intakeProjection hashAgreement agencyAccepted))
      ≡ agencyAccepted) →
  ⊥
original20198575HashEncodingCannotProveAgencyAcceptance
  encode decode correct =
  Projection.noRightDecoderAtCollision
    (λ hashAgreement accepted →
       encode (intakeProjection hashAgreement accepted))
    refl falseIsNotTrue decode correct

-- An independent receipt requires a same-document authority link,
-- approval action, revision and actual source bytes. No constructor
-- for those receipt fields is fabricated here.
data OriginalAgencyAcceptanceReceipt : Set where

-- No constructor: this declaration is a deliberately UNPAID
-- evidence obligation, not a vacuous, filled receipt or a postulate.
