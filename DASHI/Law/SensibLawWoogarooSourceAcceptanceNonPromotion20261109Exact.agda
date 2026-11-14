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

-- This record is *inhabitable only given external proof terms of two
-- separate types selected by the eventual original-source owner*.
-- An empty, permanently uninhabitable datatype was wrong: it would
-- prevent future real evidence from ever closing the gate.
-- No terms of AgencySignedJoin or ApprovedBytesJoin are supplied here.
record OriginalAgencyAcceptanceReceipt
  (AgencySignedJoin ApprovedBytesJoin : Set) : Set where
  constructor original-agency-acceptance-receipt
  field
    signedApprovalToRevision : AgencySignedJoin
    receivedBytesToApprovedOriginal : ApprovedBytesJoin

open OriginalAgencyAcceptanceReceipt public

-- A paid receipt necessarily supplies BOTH independently specified
-- evidentiary joins. This is projection, not authentication.
originalAcceptanceRequiresSignedJoin :
  {A B : Set} →
  OriginalAgencyAcceptanceReceipt A B → A
originalAcceptanceRequiresSignedJoin = signedApprovalToRevision

originalAcceptanceRequiresBytesJoin :
  {A B : Set} →
  OriginalAgencyAcceptanceReceipt A B → B
originalAcceptanceRequiresBytesJoin = receivedBytesToApprovedOriginal

-- Only an original authority/source-owner can select and validate A/B;
-- replacing these obligations with unchecked claims or trivial types
-- would be unsound as an ecological/legal evidence method.
