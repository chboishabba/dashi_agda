module DASHI.Reasoning.TrialecticHigherPromotionSupersessionExact where

------------------------------------------------------------------------
-- HISTORICAL HIGHER-PROMOTION FIREWALL SUPERSESSION
--
-- TrialecticThreeCellHyperformSynthesisExact introduced an intentionally empty
-- local token `CertifiedHypersheafOrHigherStack` at a time when that module had
-- not constructed higher categorical descent.  Later owners now construct a
-- different, stronger full-site groupoid stack and finite triadic hypersheaf.
--
-- The old empty token remains empty; later certificates do not inhabit it and
-- therefore do not contradict the historical theorem.  What is superseded is
-- only the old token's usefulness as a CURRENT GLOBAL STATUS indicator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Old
import DASHI.Reasoning.TrialecticWavePhaseHigherStackExact as Higher
import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as Hyper

oldLocalTokenStillEmpty :
  Old.CertifiedHypersheafOrHigherStack → ⊥
oldLocalTokenStillEmpty = Old.noCertifiedHypersheafPromotion

higherBoundary : Higher.TrialecticWavePhaseHigherStackBoundary
higherBoundary = Higher.canonicalTrialecticWavePhaseHigherStackBoundary

hyperBoundary : Hyper.TrialecticFiniteTriadicHypersheafBoundary
hyperBoundary = Hyper.canonicalTrialecticFiniteTriadicHypersheafBoundary

record TrialecticHigherPromotionSupersessionBoundary : Set where
  constructor trialectic-higher-promotion-supersession-boundary
  field
    oldLocalThreeCellPromotionTokenInhabited : Bool
    laterIndependentHigherStackCertificatePaid : Bool
    laterIndependentFiniteHypersheafCertificatePaid : Bool
    oldTokenWasGlobalForeverNoGo : Bool
    laterCertificateClaimsOldTokenInhabited : Bool
    oldFirewallSupersededAsCurrentStatusOwner : Bool

open TrialecticHigherPromotionSupersessionBoundary public

canonicalTrialecticHigherPromotionSupersessionBoundary :
  TrialecticHigherPromotionSupersessionBoundary
canonicalTrialecticHigherPromotionSupersessionBoundary =
  trialectic-higher-promotion-supersession-boundary
    false true true false false true
