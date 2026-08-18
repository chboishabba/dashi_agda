module DASHI.Governance.ClosedAuthorityInverseJusticeExact where

------------------------------------------------------------------------
-- CLOSED AUTHORITY + REPEATED INVERSE JUSTICE
--
-- AmalekAuthorityProjectionBoundary owns a canonical closed authority-risk
-- loop whose independent correction channel is false.  The situated justice
-- core independently owns a proof-carrying two-step inverse-justice run.  This
-- module composes those exact witnesses without asserting that either structure
-- is instantiated by a named live institution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.AmalekAuthorityProjectionBoundary as AuthorityLoop
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice

record ClosedAuthorityInverseJusticeStabilisation : Set₁ where
  constructor closedAuthorityInverseJusticeStabilisation
  field
    loop : AuthorityLoop.ClosedAuthorityLoop
    independentCorrectionClosed :
      AuthorityLoop.correctionChannelIndependent loop ≡ false
    repeatedInverseJustice : Justice.InverseJusticeRun

open ClosedAuthorityInverseJusticeStabilisation public

canonicalClosedAuthorityInverseJusticeStabilisation :
  ClosedAuthorityInverseJusticeStabilisation
canonicalClosedAuthorityInverseJusticeStabilisation =
  closedAuthorityInverseJusticeStabilisation
    AuthorityLoop.canonicalClosedAuthorityRisk
    AuthorityLoop.canonicalClosedAuthorityRiskHasNoIndependentCorrection
    Justice.canonicalTwoStepInverseJusticeRun

closedAuthorityCanStabiliseInverseJustice :
  ClosedAuthorityInverseJusticeStabilisation
closedAuthorityCanStabiliseInverseJustice =
  canonicalClosedAuthorityInverseJusticeStabilisation

record ClosedAuthorityRepairRequirement : Set₁ where
  constructor closedAuthorityRepairRequirement
  field
    sourceLoop : AuthorityLoop.ClosedAuthorityLoop
    independentCorrectionRequired :
      AuthorityLoop.correctionChannelIndependent sourceLoop ≡ true

open ClosedAuthorityRepairRequirement public

canonicalClosedLoopCannotAlreadySatisfyIndependentRepairRequirement :
  ClosedAuthorityRepairRequirement →
  sourceLoop
    ≡ AuthorityLoop.canonicalClosedAuthorityRisk →
  ⊥
canonicalClosedLoopCannotAlreadySatisfyIndependentRepairRequirement
  requirement refl with
  trans
    (sym AuthorityLoop.canonicalClosedAuthorityRiskHasNoIndependentCorrection)
    (independentCorrectionRequired requirement)
... | ()

record ClosedAuthorityInverseJusticeBoundary : Set where
  constructor closedAuthorityInverseJusticeBoundary
  field
    closedCorrectionAloneProvesInverseJustice : Bool
    inverseJusticeAloneProvesClosedAuthority : Bool
    exactCompositionRequiresBothWitnesses : Bool
    repeatedNegativeRunAvailableInFiniteModel : Bool
    liveInstitutionalApplicationRequiresExternalEvidence : Bool

canonicalClosedAuthorityInverseJusticeBoundary :
  ClosedAuthorityInverseJusticeBoundary
canonicalClosedAuthorityInverseJusticeBoundary =
  closedAuthorityInverseJusticeBoundary false false true true true
