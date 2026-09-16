module DASHI.Finance.TrumpFamilyTradeAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradeSourceAtlasRound2Exact as Round2

------------------------------------------------------------------------
-- CLAIM-LEVEL SOURCE-DEBT PARETO FRONTIER
--
-- This is deliberately not another generic scheduler.  It specializes the
-- repo-native admissible/Pareto machinery to the concrete evidence debt left by
-- the Trump-family trade atlas.
--
-- Primary transaction documents and independent corroboration are different
-- debts.  A secondary article cannot pay a missing primary-document debt, and
-- another issuer-controlled source cannot pay an independence debt.
------------------------------------------------------------------------

data AcquisitionAction : Set where
  independentPrimaryRecord : AcquisitionAction
  independentReporting : AcquisitionAction
  moreIssuerMaterial : AcquisitionAction

data AcquisitionDebt : Set where
  primaryDocumentDebt : AcquisitionDebt
  independentCorroborationDebt : AcquisitionDebt
  exactTimingDebt : AcquisitionDebt
  causalAttributionDebt : AcquisitionDebt

data PaysPrimaryDebt : AcquisitionAction → Set where
  primaryPaysPrimary : PaysPrimaryDebt independentPrimaryRecord

data PaysIndependentDebt : AcquisitionAction → Set where
  primaryPaysIndependent : PaysIndependentDebt independentPrimaryRecord
  reportingPaysIndependent : PaysIndependentDebt independentReporting

data SourceAdmissible : AcquisitionAction → Set where
  independentPrimaryAdmissible : SourceAdmissible independentPrimaryRecord
  independentReportingAdmissible : SourceAdmissible independentReporting
  issuerMaterialAdmissible : SourceAdmissible moreIssuerMaterial

secondaryOnlyCannotPayPrimaryDebt : PaysPrimaryDebt independentReporting → ⊥
secondaryOnlyCannotPayPrimaryDebt ()

issuerMaterialCannotPayIndependentDebt : PaysIndependentDebt moreIssuerMaterial → ⊥
issuerMaterialCannotPayIndependentDebt ()

------------------------------------------------------------------------
-- Current concrete debt: the exact Eric-Trump ABTC cash purchase now has a
-- primary SEC filing but still lacks independently sourced transaction-specific
-- corroboration in the atlas.  We therefore rank only acquisitions that can pay
-- the independence debt; more issuer material is consumer-inadequate.
------------------------------------------------------------------------

currentTargetClaim : Atlas.TradeEvidenceClaim
currentTargetClaim = Round2.ericAmericanBitcoinCashPurchase

currentTargetPrimaryPaid : Atlas.primarySourcePaid currentTargetClaim ≡ true
currentTargetPrimaryPaid = refl

currentTargetIndependentStillUnpaid :
  Atlas.independentCorroborationPaid currentTargetClaim ≡ false
currentTargetIndependentStillUnpaid = refl

acquisitionProblem : MDL.ConsumerMDLProblem
acquisitionProblem = MDL.consumerMDLProblem
  AcquisitionAction
  SourceAdmissible
  PaysIndependentDebt
  acquisitionBurden
  (λ _ _ → ⊤)
  actionReference
  "claim-level source-acquisition cost chart"
  "independent corroboration of a primary-paid transaction claim"
  where
    acquisitionBurden : AcquisitionAction → Nat
    acquisitionBurden independentPrimaryRecord = 3
    acquisitionBurden independentReporting = 1
    acquisitionBurden moreIssuerMaterial = 1

    actionReference : AcquisitionAction → String
    actionReference independentPrimaryRecord =
      "independent primary record: court/regulatory/issuer-independent transaction document"
    actionReference independentReporting =
      "independent reporting: transaction-specific corroboration with named primary basis"
    actionReference moreIssuerMaterial =
      "additional issuer-controlled material; cannot pay independence debt"

data SourceDebtAxis : Set where
  acquisitionBurdenAxis : SourceDebtAxis
  unpaidPrimaryProvenanceAxis : SourceDebtAxis
  remainingIndependenceGapAxis : SourceDebtAxis
  inferentialPromotionRiskAxis : SourceDebtAxis

sourceDebtCosts : MDL.CostHyperfabric acquisitionProblem
sourceDebtCosts = MDL.costHyperfabric SourceDebtAxis cost axisReference
  where
    cost : SourceDebtAxis → AcquisitionAction → Nat
    cost acquisitionBurdenAxis independentPrimaryRecord = 3
    cost acquisitionBurdenAxis independentReporting = 1
    cost acquisitionBurdenAxis moreIssuerMaterial = 1

    cost unpaidPrimaryProvenanceAxis independentPrimaryRecord = 0
    cost unpaidPrimaryProvenanceAxis independentReporting = 1
    cost unpaidPrimaryProvenanceAxis moreIssuerMaterial = 0

    cost remainingIndependenceGapAxis independentPrimaryRecord = 0
    cost remainingIndependenceGapAxis independentReporting = 0
    cost remainingIndependenceGapAxis moreIssuerMaterial = 1

    cost inferentialPromotionRiskAxis independentPrimaryRecord = 0
    cost inferentialPromotionRiskAxis independentReporting = 0
    cost inferentialPromotionRiskAxis moreIssuerMaterial = 1

    axisReference : SourceDebtAxis → String
    axisReference acquisitionBurdenAxis = "declared acquisition burden"
    axisReference unpaidPrimaryProvenanceAxis = "remaining primary-provenance deficit"
    axisReference remainingIndependenceGapAxis = "remaining independent-corroboration gap"
    axisReference inferentialPromotionRiskAxis = "risk of over-promoting source scope"

weakSelf : (a : AcquisitionAction) → MDL.WeaklyDominates sourceDebtCosts a a
weakSelf independentPrimaryRecord acquisitionBurdenAxis = ≤-refl
weakSelf independentPrimaryRecord unpaidPrimaryProvenanceAxis = ≤-refl
weakSelf independentPrimaryRecord remainingIndependenceGapAxis = ≤-refl
weakSelf independentPrimaryRecord inferentialPromotionRiskAxis = ≤-refl
weakSelf independentReporting acquisitionBurdenAxis = ≤-refl
weakSelf independentReporting unpaidPrimaryProvenanceAxis = ≤-refl
weakSelf independentReporting remainingIndependenceGapAxis = ≤-refl
weakSelf independentReporting inferentialPromotionRiskAxis = ≤-refl
weakSelf moreIssuerMaterial acquisitionBurdenAxis = ≤-refl
weakSelf moreIssuerMaterial unpaidPrimaryProvenanceAxis = ≤-refl
weakSelf moreIssuerMaterial remainingIndependenceGapAxis = ≤-refl
weakSelf moreIssuerMaterial inferentialPromotionRiskAxis = ≤-refl

primaryPareto : MDL.ParetoAdmissible sourceDebtCosts independentPrimaryRecord
primaryPareto = MDL.paretoAdmissible
  (independentPrimaryAdmissible , primaryPaysIndependent)
  noStrictlyCheaper
  "independent primary acquisition trades higher burden for zero primary-provenance deficit"
  where
    noStrictlyCheaper :
      (candidate : AcquisitionAction) →
      MDL.Eligible acquisitionProblem candidate →
      MDL.WeaklyDominates sourceDebtCosts candidate independentPrimaryRecord →
      MDL.WeaklyDominates sourceDebtCosts independentPrimaryRecord candidate
    noStrictlyCheaper independentPrimaryRecord _ _ = weakSelf independentPrimaryRecord
    noStrictlyCheaper independentReporting _ dominates with dominates unpaidPrimaryProvenanceAxis
    ... | ()
    noStrictlyCheaper moreIssuerMaterial (_ , ()) _

reportingPareto : MDL.ParetoAdmissible sourceDebtCosts independentReporting
reportingPareto = MDL.paretoAdmissible
  (independentReportingAdmissible , reportingPaysIndependent)
  noStrictlyCheaper
  "independent reporting trades lower acquisition burden for residual primary-provenance deficit"
  where
    noStrictlyCheaper :
      (candidate : AcquisitionAction) →
      MDL.Eligible acquisitionProblem candidate →
      MDL.WeaklyDominates sourceDebtCosts candidate independentReporting →
      MDL.WeaklyDominates sourceDebtCosts independentReporting candidate
    noStrictlyCheaper independentPrimaryRecord _ dominates with dominates acquisitionBurdenAxis
    ... | ()
    noStrictlyCheaper independentReporting _ _ = weakSelf independentReporting
    noStrictlyCheaper moreIssuerMaterial (_ , ()) _

record TrumpFamilyTradeAcquisitionFrontier : Set₁ where
  constructor trump-family-trade-acquisition-frontier
  field
    targetClaim : Atlas.TradeEvidenceClaim
    primaryDocumentOption : MDL.ParetoAdmissible sourceDebtCosts independentPrimaryRecord
    independentReportingOption : MDL.ParetoAdmissible sourceDebtCosts independentReporting
    targetPrimaryAlreadyPaid : Atlas.primarySourcePaid targetClaim ≡ true
    targetIndependentStillUnpaid : Atlas.independentCorroborationPaid targetClaim ≡ false
    frontierReference : String

open TrumpFamilyTradeAcquisitionFrontier public

canonicalTrumpFamilyTradeAcquisitionFrontier : TrumpFamilyTradeAcquisitionFrontier
canonicalTrumpFamilyTradeAcquisitionFrontier =
  trump-family-trade-acquisition-frontier
    currentTargetClaim
    primaryPareto
    reportingPareto
    currentTargetPrimaryPaid
    currentTargetIndependentStillUnpaid
    "Current frontier: independently corroborate the exact ABTC cash-purchase edge without conflating independent synthesis with primary transaction authority."

record AcquisitionParetoBoundary : Set where
  constructor acquisition-pareto-boundary
  field
    primaryAndIndependentDebtAreSeparate : Bool
    secondaryOnlyPaysMissingPrimaryDocument : Bool
    moreIssuerMaterialPaysIndependenceDebt : Bool
    cheaperSourceAutomaticallyWins : Bool
    timingEvidenceAutomaticallyProvesCausation : Bool
    completedAcquisitionCreatesTradeAuthority : Bool

canonicalAcquisitionParetoBoundary : AcquisitionParetoBoundary
canonicalAcquisitionParetoBoundary =
  acquisition-pareto-boundary true false false false false false
