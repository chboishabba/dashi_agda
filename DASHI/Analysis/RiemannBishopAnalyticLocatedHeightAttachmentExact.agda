module DASHI.Analysis.RiemannBishopAnalyticLocatedHeightAttachmentExact where

------------------------------------------------------------------------
-- WHOLE BISHOP COMPLEX CARRIER IDENTITY -> MINIMAL LOCATED-HEIGHT ATTACHMENT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; cong)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BishopComplex
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as BishopHeight
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located

toBishopLocatedHeightAttachment :
  ∀ {analytic functions} →
  BishopComplex.CanonicalBishopComplexCarrierRealization analytic functions →
  Located.AnalyticLocatedHeightCarrierAttachment
    analytic
    BishopHeight.bishopLocatedHeightCarrier
toBishopLocatedHeightAttachment realization = record
  { Located.realCarrierIdentity =
      cong
        Analytic.ComplexAnalyticCarrier.Real
        (BishopComplex.carrierIdentity realization)
  }

record BishopAnalyticLocatedHeightAttachmentBoundary : Set where
  constructor bishop-analytic-located-height-attachment-boundary
  field
    independentRealCarrierEqualityRequiredAfterWholeCarrierIdentity : Bool
    minimalLocatedHeightAttachmentCompiles : Bool
    selectedWholeCarrierIdentityStillRequired : Bool
    rhDerivedHere : Bool

open BishopAnalyticLocatedHeightAttachmentBoundary public

canonicalBishopAnalyticLocatedHeightAttachmentBoundary :
  BishopAnalyticLocatedHeightAttachmentBoundary
canonicalBishopAnalyticLocatedHeightAttachmentBoundary =
  bishop-analytic-located-height-attachment-boundary
    false true true false
