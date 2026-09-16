module DASHI.Finance.TruthAPISourceRoleTriangulationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Primary
import DASHI.Finance.TruthAPIIndependentCorroborationExact as Independent
import DASHI.Finance.TruthAPILitigationAllegationExact as Litigation
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- TRUTH API SOURCE-ROLE TRIANGULATION
--
-- The same empirical object is now observed through three different source
-- roles:
--
--   1. issuer / SEC-filed disclosure: launch, product description, customer
--      count and revenue status;
--   2. independent reporting: corroboration of launch/customer-count/revenue;
--   3. federal-court complaint: primary evidence of plaintiffs' allegations and
--      requested relief, but not of their truth.
--
-- Triangulation improves the evidence graph without flattening source roles.
------------------------------------------------------------------------

data EvidenceRole : Set where
  issuerPrimaryRole : EvidenceRole
  independentCorroborationRole : EvidenceRole
  partyPleadingRole : EvidenceRole

record RoleBoundClaim : Set₁ where
  constructor role-bound-claim
  field
    role : EvidenceRole
    claim : Atlas.TradeEvidenceClaim
    roleReference : String

open RoleBoundClaim public

issuerLaunchClaim : RoleBoundClaim
issuerLaunchClaim =
  role-bound-claim
    issuerPrimaryRole
    Primary.truthAPIRealisedLaunchAndCustomers
    "SEC-filed issuer results: actual launch, >10 agreements, revenue"

independentLaunchClaim : RoleBoundClaim
independentLaunchClaim =
  role-bound-claim
    independentCorroborationRole
    Independent.truthAPIReutersCorroboration
    "Reuters independent synthesis corroborating launch/customer-count/revenue"

litigationClaim : RoleBoundClaim
litigationClaim =
  role-bound-claim
    partyPleadingRole
    Litigation.truthAPIConstitutionalChallengeFiled
    "S.D.N.Y. complaint: primary record of plaintiffs' allegations and requested relief"

record TruthAPITriangulatedEvidence : Set₁ where
  constructor truth-api-triangulated-evidence
  field
    issuer : RoleBoundClaim
    independent : RoleBoundClaim
    pleading : RoleBoundClaim

    issuerRoleExact : role issuer ≡ issuerPrimaryRole
    independentRoleExact : role independent ≡ independentCorroborationRole
    pleadingRoleExact : role pleading ≡ partyPleadingRole

    issuerPrimaryPaid : Atlas.primarySourcePaid (claim issuer) ≡ true
    independentCorroborationPaid :
      Atlas.independentCorroborationPaid (claim independent) ≡ true
    pleadingPrimaryForAllegation : Atlas.primarySourcePaid (claim pleading) ≡ true

open TruthAPITriangulatedEvidence public

canonicalTruthAPITriangulation : TruthAPITriangulatedEvidence
canonicalTruthAPITriangulation =
  truth-api-triangulated-evidence
    issuerLaunchClaim
    independentLaunchClaim
    litigationClaim
    refl refl refl
    refl refl refl

------------------------------------------------------------------------
-- Triangulation is not majority voting over heterogeneous propositions.
------------------------------------------------------------------------

data ThreeSourcesAutomaticallyProveLegalConclusion : Set where
data PrimaryPleadingPlusReportingAutomaticallyProvesAllegation : Set where
data IssuerAndReporterAgreementAutomaticallyPaysCustomerIdentity : Set where
\data DifferentSourceRolesMayBeCollapsedPermission : Set where

threeSourcesDoNotProveLegalConclusion :
  ThreeSourcesAutomaticallyProveLegalConclusion → ⊥
threeSourcesDoNotProveLegalConclusion ()

pleadingAndReportingDoNotProveAllegation :
  PrimaryPleadingPlusReportingAutomaticallyProvesAllegation → ⊥
pleadingAndReportingDoNotProveAllegation ()

agreementDoesNotPayCustomerIdentity :
  IssuerAndReporterAgreementAutomaticallyPaysCustomerIdentity → ⊥
agreementDoesNotPayCustomerIdentity ()

sourceRolesCannotBeSilentlyCollapsed :
  DifferentSourceRolesMayBeCollapsedPermission → ⊥
sourceRolesCannotBeSilentlyCollapsed ()

record TruthAPISourceRoleTriangulationBoundary : Set where
  constructor truth-api-source-role-triangulation-boundary
  field
    issuerPrimaryRoleRetained : Bool
    independentCorroborationRoleRetained : Bool
    partyPleadingRoleRetained : Bool
    independentCorroborationNowPaidForNarrowLaunchClaim : Bool
    legalMeritsRemainUnpaid : Bool
    customerIdentityRemainsUnpaid : Bool
    sourceCountIsNotTruthVote : Bool

canonicalTruthAPISourceRoleTriangulationBoundary :
  TruthAPISourceRoleTriangulationBoundary
canonicalTruthAPISourceRoleTriangulationBoundary =
  truth-api-source-role-triangulation-boundary
    true true true true true true true
