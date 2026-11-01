module DASHI.Core.ContactGateCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Generic fail-closed gate for governed contact.
--
-- Contact, replay, comparison, and residual scoring do not themselves
-- promote truth.  Promotion requires the relevant external authority and
-- bridge obligations to be closed explicitly.
------------------------------------------------------------------------

record ContactGateCore : Set where
  constructor contactGateCore
  field
    diagnosticOnly            : Bool
    externalAuthorityRequired : Bool
    authorityGateClosed       : Bool
    bridgeRequirementClosed   : Bool
    promotesTruth             : Bool

open ContactGateCore public

canonicalFailClosedContactGate : ContactGateCore
canonicalFailClosedContactGate =
  contactGateCore true true false false false

canonicalGateIsDiagnosticOnly :
  diagnosticOnly canonicalFailClosedContactGate ≡ true
canonicalGateIsDiagnosticOnly = refl

canonicalGateRequiresExternalAuthority :
  externalAuthorityRequired canonicalFailClosedContactGate ≡ true
canonicalGateRequiresExternalAuthority = refl

canonicalGateDoesNotPromoteTruth :
  promotesTruth canonicalFailClosedContactGate ≡ false
canonicalGateDoesNotPromoteTruth = refl
