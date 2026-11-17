module DASHI.Cognition.AustraliaMandelsonMiningTaxPoliticalEconomyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MANDELSON / EPSTEIN / AUSTRALIAN MINING-TAX POLITICAL-ECONOMY BRIDGE
--
-- Released Epstein correspondence documents Mandelson sharing/endorsing
-- mining-industry political strategy around the Rudd government's proposed
-- resource super-profits tax.  This pays a transnational political-advice edge,
-- not Epstein direction of the campaign or proof that the correspondence caused
-- Rudd's removal or the tax's later weakening.
------------------------------------------------------------------------

data MiningTaxEdgeKind : Set where
  xstrataStrategyShared : MiningTaxEdgeKind
  mandelsonCoalitionAdvice : MiningTaxEdgeKind
  epsteinReceivesPoliticalStrategy : MiningTaxEdgeKind
  ruddGovernmentPolicyTarget : MiningTaxEdgeKind
  laterPoliticalOutcome : MiningTaxEdgeKind

record MiningTaxReceipt : Set where
  constructor mining-tax-receipt
  field
    edgeKind : MiningTaxEdgeKind
    sourceIdentity : String
    boundedFinding : String
    relationPaid : Bool
    causalOutcomePaid : Bool
    wrongdoingPaid : Bool
open MiningTaxReceipt public

xstrataReceipt : MiningTaxReceipt
xstrataReceipt = mining-tax-receipt
  xstrataStrategyShared
  "2026 reporting on DOJ-released Epstein files"
  "Peter Mandelson forwarded to Epstein a private analysis from Xstrata CEO Mick Davis concerning opposition to the Rudd government's proposed mining super-profits tax."
  true false false

coalitionAdviceReceipt : MiningTaxReceipt
coalitionAdviceReceipt = mining-tax-receipt
  mandelsonCoalitionAdvice
  "released Epstein correspondence / Guardian Australia 2026-02-03"
  "Mandelson advised building a broad coalition against the tax and warned against framing the dispute as corporate power versus democracy."
  true false false

epsteinReceipt : MiningTaxReceipt
epsteinReceipt = mining-tax-receipt
  epsteinReceivesPoliticalStrategy
  "released Epstein correspondence"
  "Epstein was a recipient of sensitive political/economic strategy concerning an Australian domestic resource-tax dispute."
  true false false

ruddReceipt : MiningTaxReceipt
ruddReceipt = mining-tax-receipt
  ruddGovernmentPolicyTarget
  "2010 policy chronology / released correspondence"
  "The strategy concerned pressure against the Rudd government's proposed 40% resource super-profits tax."
  true false false

outcomeBoundaryReceipt : MiningTaxReceipt
outcomeBoundaryReceipt = mining-tax-receipt
  laterPoliticalOutcome
  "Australian political chronology"
  "Rudd was later replaced by Julia Gillard and a weaker mining-tax regime followed, but the sources used here do not establish that Mandelson/Epstein correspondence caused those outcomes."
  true false false

record MiningTaxPoliticalEconomyBoundary : Set where
  constructor mining-tax-political-economy-boundary
  field
    transnationalPoliticalAdvicePaid : Bool
    epsteinRecipientOfStrategyPaid : Bool
    australianResourcePolicyBridgePaid : Bool
    epsteinDirectedMiningCampaignPaid : Bool
    correspondenceCausedRuddRemovalPaid : Bool
    correspondenceCausedTaxWeakeningPaid : Bool
open MiningTaxPoliticalEconomyBoundary public

canonicalMiningTaxPoliticalEconomyBoundary : MiningTaxPoliticalEconomyBoundary
canonicalMiningTaxPoliticalEconomyBoundary =
  mining-tax-political-economy-boundary true true true false false false

data AdviceImpliesCampaignControl : Set where
data CorrespondenceImpliesPoliticalOutcome : Set where
data RecipientImpliesOperationalDirection : Set where

adviceDoesNotCreateCampaignControl : AdviceImpliesCampaignControl → ⊥
adviceDoesNotCreateCampaignControl ()

correspondenceDoesNotCreatePoliticalOutcome : CorrespondenceImpliesPoliticalOutcome → ⊥
correspondenceDoesNotCreatePoliticalOutcome ()

recipientDoesNotCreateOperationalDirection : RecipientImpliesOperationalDirection → ⊥
recipientDoesNotCreateOperationalDirection ()
