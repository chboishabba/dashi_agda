module DASHI.Policy.BerkmanDataCentreObscurationAnalogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Michael Berkman data-centre speech as an analogy for foregrounded dispute
-- versus underlying shared policy commitment.
--
-- Source identity: Queensland Parliament / Michael Berkman, Adjournment - Data
-- Centres, 27 August 2026; the user-supplied Instagram reel appears to reuse or
-- bundle this chamber material.  Exact multi-withdrawal edit provenance remains
-- a separate source-location residual.
------------------------------------------------------------------------

data BerkmanClaim : Set where
  manufacturedFightHypothesis : BerkmanClaim
  sharedDataCentreBoomCommitment : BerkmanClaim
  thirteenPercentPowerPriceClaim : BerkmanClaim
  nextDCMaroochydoreLoadClaim : BerkmanClaim
  foregroundRenewablesDisputeObscuresDataCentreQuestion : BerkmanClaim
  multipleWithdrawalBundleClaim : BerkmanClaim

data ClaimStatus : Set where
  speakerAttributed : ClaimStatus
  independentlyVerifiable : ClaimStatus
  speakerHypothesis : ClaimStatus
  sourceResidual : ClaimStatus

record BerkmanReceipt : Set where
  constructor berkmanReceipt
  field
    claim : BerkmanClaim
    status : ClaimStatus
    sourceReference : String
    boundedStatement : String

open BerkmanReceipt public

manufacturedFightReceipt : BerkmanReceipt
manufacturedFightReceipt = berkmanReceipt manufacturedFightHypothesis speakerHypothesis
  "Michael Berkman, Queensland Parliament adjournment speech, 27 Aug 2026"
  "Berkman explicitly calls it his 'conspiracy theory, for what it's worth' that the visible political fight is manufactured to shift focus away from whether Queenslanders want the data-centre boom at all."

sharedCommitmentReceipt : BerkmanReceipt
sharedCommitmentReceipt = berkmanReceipt sharedDataCentreBoomCommitment speakerAttributed
  "same speech"
  "Berkman's argument treats the visible Labor/LNP energy-source dispute as potentially secondary to a shared commitment to data-centre expansion."

priceClaimReceipt : BerkmanReceipt
priceClaimReceipt = berkmanReceipt thirteenPercentPowerPriceClaim independentlyVerifiable
  "same speech; underlying modelling/source remains a separate producer"
  "Berkman states that the data-centre boom could increase Queensland power prices by 13% over the next ten years. The speech attribution is closed; exact modelling authority remains independently verifiable."

maroochydoreReceipt : BerkmanReceipt
maroochydoreReceipt = berkmanReceipt nextDCMaroochydoreLoadClaim independentlyVerifiable
  "same speech; NEXTDC Maroochydore proposal is the underlying empirical producer"
  "Berkman uses NEXTDC Maroochydore as an example, claiming its proposed annual energy use would exceed that of the suburb's homes combined. Attribution is closed; exact load/household comparison remains an empirical verification coordinate."

obscurationAnalogyReceipt : BerkmanReceipt
obscurationAnalogyReceipt = berkmanReceipt foregroundRenewablesDisputeObscuresDataCentreQuestion speakerHypothesis
  "same speech"
  "The analytic shape is foregrounded partisan disagreement -> possible attention displacement from a shared underlying policy commitment. This is a hypothesis pattern, not proof of orchestration."

withdrawalBundleResidual : BerkmanReceipt
withdrawalBundleResidual = berkmanReceipt multipleWithdrawalBundleClaim sourceResidual
  "user-supplied Instagram reel D c-EIZIPM2U; chamber source identified as 27-Aug-2026 data-centre speech for the quoted segment"
  "The user's memory that the reel bundles several occasions on which Berkman was required to withdraw/take back statements remains plausible but unclosed. The identified data-centre transcript itself does not yet establish the count or prove that all bundled interventions belong to one speech."

------------------------------------------------------------------------
-- Cross-domain analogy boundary.
------------------------------------------------------------------------

data ObscurationPattern : Set where
  foregroundedConflict : ObscurationPattern
  sharedUnderlyingCommitment : ObscurationPattern
  omittedCostCoordinate : ObscurationPattern
  attentionDisplacementHypothesis : ObscurationPattern

record AnalogyBoundary : Set where
  constructor analogyBoundary
  field
    samePatternMeansSameCause : Bool
    samePatternMeansSameCauseIsFalse : samePatternMeansSameCause ≡ false
    foregroundConflictProvesManufacture : Bool
    foregroundConflictProvesManufactureIsFalse : foregroundConflictProvesManufacture ≡ false
    sharedCommitmentMayMotivateSalienceAudit : Bool
    sharedCommitmentMayMotivateSalienceAuditIsTrue : sharedCommitmentMayMotivateSalienceAudit ≡ true
    omittedCostMayMotivateDecisionFunctionSearch : Bool
    omittedCostMayMotivateDecisionFunctionSearchIsTrue : omittedCostMayMotivateDecisionFunctionSearch ≡ true

canonicalAnalogyBoundary : AnalogyBoundary
canonicalAnalogyBoundary = analogyBoundary false refl false refl true refl true refl
