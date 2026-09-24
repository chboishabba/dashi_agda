module DASHI.Analysis.RiemannLocatedLowTransportExact where

------------------------------------------------------------------------
-- SAME-SUBSTRATE LOCATED LOW CRITICALITY -> CANONICAL LOW TRANSPORT
------------------------------------------------------------------------

open import Data.Unit using (⊤; tt)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannLocatedHeightCarrierExact as Height
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as Located
import DASHI.Analysis.RiemannAnalyticLocatedLowCriticalityCompilerExact as LowCritical
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low

compileLocatedLowTransport :
  ∀ {analytic heightCarrier}
    {attachment :
      Located.AnalyticLocatedHeightCarrierAttachment analytic heightCarrier} →
  LowCritical.PublishedLocatedLowCriticality attachment →
  Low.PlattTrudgianVerifiedRegionTransport analytic
compileLocatedLowTransport {attachment = attachment} published = record
  { Low.WithinPublishedVerifiedHeight =
      Located.LocatedVerifiedRegion attachment
  ; Low.publishedVerifiedHeightCritical =
      LowCritical.verifiedLocatedZeroCritical published
  ; Low.exactPublishedHeightIs3000175332800 = ⊤
  ; Low.exactPublishedHeightIs3000175332800Receipt = tt
  ; Low.sourceReference =
      LowCritical.sourceReference published
  ; Low.transportReference =
      LowCritical.sameSubstrateReference published
  }
