module DASHI.Cognition.PNF.ContextualFractranFibreRestrictionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Provenance
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Exact generic-core instance for one requested prime observation.
--
-- Projecting a complete signed valuation to one SSP trit is intentionally
-- lossy.  Evidence may restrict the compatible valuation fibre; it does not
-- reconstruct the hidden valuation or promote semantic truth.
------------------------------------------------------------------------

projectRequestedPrime :
  Signed.SSPPrime → Context.ContextualValuation → Trit.SSPTrit
projectRequestedPrime prime valuation =
  Context.coarseSSPTrit (valuation prime)

contextualPrimeRestrictionCore :
  Signed.SSPPrime → Fibre.FibreRestrictionCore
contextualPrimeRestrictionCore prime = record
  { Carrier = Context.ContextualValuation
  ; Surface = Trit.SSPTrit
  ; Evidence = Context.ContextualValuation
  ; project = projectRequestedPrime prime
  ; Fibre = λ _ → Context.ContextualValuation
  ; restrictsFibre = λ evidence coarse →
      projectRequestedPrime prime evidence ≡ coarse
  ; doesNotRecoverCarrier = true
  ; promotesTruth = false
  }

-- A maximally lossless reference receipt: retaining the original fine
-- valuation trivially reopens it.  This establishes the type-level distinction
-- between projection and reopening without claiming that every application
-- should retain this much state.
fullValuationReopening :
  (prime : Signed.SSPPrime) →
  Provenance.ProvenanceBearingQuotient (contextualPrimeRestrictionCore prime)
fullValuationReopening prime =
  Provenance.provenanceBearingQuotient
    Context.ContextualValuation
    (λ valuation → valuation)
    (λ coarse valuation → valuation)
    (λ valuation → refl)

record ContextualFibreRestrictionBoundary : Set where
  constructor contextualFibreRestrictionBoundary
  field
    oneRequestedTritRecoversWholeValuation : Bool
    evidenceMayRestrictCompatibleFibre : Bool
    projectionPromotesSemanticTruth : Bool
    retainedResidualCanEnableExactReopening : Bool

canonicalContextualFibreRestrictionBoundary :
  ContextualFibreRestrictionBoundary
canonicalContextualFibreRestrictionBoundary =
  contextualFibreRestrictionBoundary false true false true
