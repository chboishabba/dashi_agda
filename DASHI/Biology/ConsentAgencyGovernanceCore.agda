module DASHI.Biology.ConsentAgencyGovernanceCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Promotion.AuthorityBoundaryCore as Authority

record ConsentAgencyGovernance : Set where
  constructor mkConsentAgencyGovernance
  field
    boundaryLabel : String
    clinicalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    consentRequired : Bool
    pacingRequired : Bool
    reviewRequired : Bool
    refusalPreserved : Bool
    withdrawalPreserved : Bool
    forcedDisclosureBlocked : Bool
    forcedNormalisationBlocked : Bool
    vulnerableUserAuthorityBlocked : Bool
    governanceHolds : Bool
    governanceHoldsIsTrue : governanceHolds ≡ true

open ConsentAgencyGovernance public

canonicalConsentAgencyGovernance : ConsentAgencyGovernance
canonicalConsentAgencyGovernance =
  mkConsentAgencyGovernance
    "canonical consent and agency governance"
    Authority.canonicalClinicalAuthorityBoundaryReceipt
    true true true true true true true true true refl
