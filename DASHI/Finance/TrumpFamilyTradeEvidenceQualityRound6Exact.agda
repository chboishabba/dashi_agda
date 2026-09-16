module DASHI.Finance.TrumpFamilyTradeEvidenceQualityRound6Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeClaimIdentityPromotionExact as Identity
import DASHI.Finance.TrumpFamilyTradeSourceGenealogyExact as Genealogy
import DASHI.Finance.TrumpFamilyTradeEvidenceHealthExact as Health
import DASHI.Finance.TrumpSpaceXPrimaryAcquisitionExact as SpaceX
import DASHI.Finance.TrumpSpaceXPropositionGenealogyExact as SpaceXGenealogy
import DASHI.Finance.TrumpFamilyTradePNFChronologyExact as Chronology
import DASHI.Finance.TrumpFamilyTradeStrategicIdentificationExact as Identification

------------------------------------------------------------------------
-- ROUND-6 EVIDENCE-QUALITY AGGREGATE
--
-- The current SpaceX state deliberately remains below primary same-object
-- promotion: Reuters is paid secondary synthesis; the exact primary OGE row is
-- unpaid. Point-in-time/publication chronology can still be retained without
-- pretending that it identifies decision-time information or hidden motive.
------------------------------------------------------------------------

spaceXCurrentHealth : Health.TradeEvidenceHealth
spaceXCurrentHealth =
  Health.trade-evidence-health
    false  -- exact primary/secondary same-object identity not paid
    false  -- exact primary transaction row not paid
    true   -- Reuters transaction/report chronology is explicitly dated
    false  -- derivative secondary + underlying filing is not yet an independent pair
    false  -- no contradiction is asserted in this local proposition
    true   -- genealogy debt is explicitly retained

spaceXNotPrimaryPromotionEligible :
  Health.PromotionEligibleHealth spaceXCurrentHealth → ⊥
spaceXNotPrimaryPromotionEligible eligible with Health.primaryPaid eligible
... | ()

------------------------------------------------------------------------
-- Two-source visibility does not establish independent corroboration when the
-- two surfaces share one upstream transaction filing.
------------------------------------------------------------------------

visiblePairStillGenealogicallyDependent :
  Genealogy.IndependentVisiblePair
    Genealogy.primaryArtifact
    Genealogy.secondaryReport → ⊥
visiblePairStillGenealogicallyDependent =
  Genealogy.primaryPlusDerivativeReportNotIndependent

------------------------------------------------------------------------
-- The same Reuters article also demonstrates why genealogy must be proposition
-- indexed: its transaction statement routes upstream to a financial disclosure,
-- while its portfolio-management representation routes to an attributed White
-- House statement. Same carrier != same evidentiary ancestry for every claim.
------------------------------------------------------------------------

spaceXPropositionGenealogyBoundary :
  SpaceXGenealogy.SpaceXPropositionGenealogyBoundary
spaceXPropositionGenealogyBoundary =
  SpaceXGenealogy.canonicalSpaceXPropositionGenealogyBoundary

------------------------------------------------------------------------
-- Strategic-identification and chronology owners remain authoritative for two
-- distinct questions:
--   exact observed transaction != hidden information state;
--   event time != later disclosure/public-knowledge time.
------------------------------------------------------------------------

identificationBoundary : Identification.TrumpFamilyTradeStrategicIdentificationBoundary
identificationBoundary = Identification.canonicalTrumpFamilyTradeStrategicIdentificationBoundary

chronologyBoundary : Chronology.TrumpFamilyTradePNFChronologyBoundary
chronologyBoundary = Chronology.canonicalTrumpFamilyTradePNFChronologyBoundary

identityBoundary : Identity.TradeClaimIdentityPromotionBoundary
identityBoundary = Identity.canonicalTradeClaimIdentityPromotionBoundary

spaceXAcquisitionBoundary : SpaceX.SpaceXPrimaryAcquisitionBoundary
spaceXAcquisitionBoundary = SpaceX.canonicalSpaceXPrimaryAcquisitionBoundary

record TrumpFamilyTradeEvidenceQualityRound6Boundary : Set where
  constructor trump-family-trade-evidence-quality-round6-boundary
  field
    sourceCountNotCorroboration : Bool
    sameObjectPromotionNeedsExactTransactionCoordinates : Bool
    SpaceXPrimaryRowStillUnpaid : Bool
    sameCarrierCanHaveDifferentPropositionGenealogy : Bool
    laterDisclosureDoesNotIdentifyEarlierInformationState : Bool
    observedTransactionDoesNotIdentifyLatentInformationState : Bool
    evidentiaryHealthDoesNotCreateCausationIllegalityOrMotive : Bool

canonicalTrumpFamilyTradeEvidenceQualityRound6Boundary :
  TrumpFamilyTradeEvidenceQualityRound6Boundary
canonicalTrumpFamilyTradeEvidenceQualityRound6Boundary =
  trump-family-trade-evidence-quality-round6-boundary true true true true true true true
