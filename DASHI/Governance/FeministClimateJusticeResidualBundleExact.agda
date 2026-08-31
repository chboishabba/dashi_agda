module DASHI.Governance.FeministClimateJusticeResidualBundleExact where

open import DASHI.Core.Prelude
import DASHI.Core.MultiaxialResidualBundleExact as Multi
import DASHI.Governance.SafeJustEpistemicResidualLedgerExact as SafeJust

------------------------------------------------------------------------
-- FEMINIST CLIMATE-JUSTICE RESIDUAL VECTOR
--
-- Five independent questions remain visible alongside a technically valid
-- inference chain:
--   phenomenon      -- what unmet need / harm remains in the represented world?
--   epistemic       -- what evidence / knowledge remains incomplete?
--   political       -- what contestation / participation remains unresolved?
--   responsibility  -- what contribution / burden asymmetry remains?
--   category        -- what category-genesis / observer assumptions remain open?
--
-- Qualification is consumer-indexed carriage, not forced zeroing of every axis.
------------------------------------------------------------------------

data PoliticalResidual : Set where contestabilityStillOpen : PoliticalResidual
data ResponsibilityResidual : Set where responsibilityBurdenAsymmetry : ResponsibilityResidual
data CategoryResidual : Set where categoryGenesisStillOpen : CategoryResidual

ClimateJusticeResidualBundle : Set
ClimateJusticeResidualBundle =
  Multi.ResidualBundle
    SafeJust.PhenomenonResidual
    SafeJust.EpistemicResidual
    PoliticalResidual
    ResponsibilityResidual
    CategoryResidual

canonicalClimateJusticeResiduals : ClimateJusticeResidualBundle
canonicalClimateJusticeResiduals =
  Multi.residualBundle
    SafeJust.ecologicalOvershootResidual
    SafeJust.missingNationalBlueWaterSeries
    contestabilityStillOpen
    responsibilityBurdenAsymmetry
    categoryGenesisStillOpen

------------------------------------------------------------------------
-- Example synthesis contract: the consumer explicitly agrees to carry these
-- open coordinates.  This demonstrates that qualified use != semantic closure.
------------------------------------------------------------------------

data AcceptPhenomenon : SafeJust.PhenomenonResidual → Set where
  carryEcologicalOvershoot : AcceptPhenomenon SafeJust.ecologicalOvershootResidual

data AcceptEpistemic : SafeJust.EpistemicResidual → Set where
  carryBlueWaterGap : AcceptEpistemic SafeJust.missingNationalBlueWaterSeries

data AcceptPolitical : PoliticalResidual → Set where
  carryContestabilityGap : AcceptPolitical contestabilityStillOpen

data AcceptResponsibility : ResponsibilityResidual → Set where
  carryResponsibilityAsymmetry : AcceptResponsibility responsibilityBurdenAsymmetry

data AcceptCategory : CategoryResidual → Set where
  carryCategoryGenesisGap : AcceptCategory categoryGenesisStillOpen

researchSynthesisResidualContract :
  Multi.ConsumerResidualContract
    SafeJust.PhenomenonResidual
    SafeJust.EpistemicResidual
    PoliticalResidual
    ResponsibilityResidual
    CategoryResidual
researchSynthesisResidualContract =
  Multi.consumerResidualContract
    AcceptPhenomenon
    AcceptEpistemic
    AcceptPolitical
    AcceptResponsibility
    AcceptCategory

canonicalResidualCarriage :
  Multi.ResidualCarriageReceipt
    researchSynthesisResidualContract
    canonicalClimateJusticeResiduals
canonicalResidualCarriage =
  Multi.residualCarriageReceipt
    carryEcologicalOvershoot
    carryBlueWaterGap
    carryContestabilityGap
    carryResponsibilityAsymmetry
    carryCategoryGenesisGap

record FeministClimateResidualBoundary : Set where
  constructor feministClimateResidualBoundary
  field
    closingDataResidualClosesPoliticalResidual : Bool
    closingDataResidualClosesPoliticalResidualIsFalse :
      closingDataResidualClosesPoliticalResidual ≡ false
    closingDataResidualClosesResponsibilityResidual : Bool
    closingDataResidualClosesResponsibilityResidualIsFalse :
      closingDataResidualClosesResponsibilityResidual ≡ false
    closingDataResidualClosesCategoryResidual : Bool
    closingDataResidualClosesCategoryResidualIsFalse :
      closingDataResidualClosesCategoryResidual ≡ false
    qualifiedSynthesisMeansResidualVectorIsZero : Bool
    qualifiedSynthesisMeansResidualVectorIsZeroIsFalse :
      qualifiedSynthesisMeansResidualVectorIsZero ≡ false
    residualAcceptanceMeansResidualResolved : Bool
    residualAcceptanceMeansResidualResolvedIsFalse :
      residualAcceptanceMeansResidualResolved ≡ false

canonicalFeministClimateResidualBoundary : FeministClimateResidualBoundary
canonicalFeministClimateResidualBoundary =
  feministClimateResidualBoundary false refl false refl false refl false refl false refl
