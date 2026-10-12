module DASHI.Philosophy.NonginRoadmapClosureExact where

------------------------------------------------------------------------
-- NONGIN ROADMAP CLOSURE
--
-- This is the terminal status theorem for the Nongin lineage itself.
--
-- The raw/later source genealogy now has one canonical provenance entry for
-- every declared OriginPhase.  The semantic programme required to reconstruct
-- the raw Nongin invariants is also paid by existing owners:
--
--   * coarse/fine collision and consumer-relative non-descent;
--   * exact richer-observer recovery;
--   * least-sufficient consumer observer / information-order theorem;
--   * recursive observer depth, truncation, residual reopening;
--   * generic recursive-fibre/inverse-limit bridge;
--   * mature trialectic/Grothendieck descendant integration;
--   * explicit finite-geometry and Set-descent boundaries;
--   * exact C3 local-context obstruction and residual repair;
--   * explicit next-depth expansion policy plus proof of underdetermination.
--
-- The later transport-enriched groupoid / 2-sheaf / higher-stack / hypersheaf
-- programme is valuable generalisation, but it is NOT a prerequisite for
-- closing the historical Nongin reconstruction.  Nor are exceptional-group or
-- physical-law realizations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.DialecticOriginSourceAtlasExact as Atlas
import DASHI.Philosophy.NonginCurrentMaxCutExact as Current
import DASHI.Reasoning.NonginConsumerRelativeFrameAdvantageExact as Advantage

atlasBoundary : Atlas.DialecticOriginSourceAtlasBoundary
atlasBoundary = Atlas.canonicalDialecticOriginSourceAtlasBoundary

currentBoundary : Current.NonginCurrentMaxCutBoundary
currentBoundary = Current.canonicalNonginCurrentMaxCutBoundary

leastBoundary : Advantage.NonginLeastSufficientObserverBoundary
leastBoundary = Advantage.canonicalNonginLeastSufficientObserverBoundary

------------------------------------------------------------------------
-- 1. Genealogy is total over the declared phase type.
------------------------------------------------------------------------

genealogyPhaseTotalityReceipt :
  Atlas.everyDeclaredOriginPhaseHasCanonicalEntry atlasBoundary ≡ true
genealogyPhaseTotalityReceipt = refl

canonicalEntryReturnsDeclaredPhase :
  (declared : Atlas.OriginPhase) →
  Atlas.phase (Atlas.entryForPhase declared) ≡ declared
canonicalEntryReturnsDeclaredPhase = Atlas.entryForPhaseIsExact

------------------------------------------------------------------------
-- 2. Exact Nongin-required obligations.
------------------------------------------------------------------------

data NonginRequiredObligation : Set where
  phaseTotalGenealogy : NonginRequiredObligation
  structuralOriginFormalisation : NonginRequiredObligation
  consumerRelativeNonDescent : NonginRequiredObligation
  exactConsumerRecovery : NonginRequiredObligation
  leastSufficientConsumerObserver : NonginRequiredObligation
  recursiveObserverReopening : NonginRequiredObligation
  recursiveObserverFibreTower : NonginRequiredObligation
  observerStreamInverseLimit : NonginRequiredObligation
  matureTrialecticDescendantIntegration : NonginRequiredObligation
  setLevelDescentIntegration : NonginRequiredObligation
  c3ContextObstructionAndRepair : NonginRequiredObligation
  nextDepthExpansionUnderdetermination : NonginRequiredObligation

requiredObligationPaid : NonginRequiredObligation → Bool
requiredObligationPaid phaseTotalGenealogy =
  Atlas.everyDeclaredOriginPhaseHasCanonicalEntry atlasBoundary
requiredObligationPaid structuralOriginFormalisation =
  Current.historicalOriginFormalized currentBoundary
requiredObligationPaid consumerRelativeNonDescent =
  Current.consumerRelativeCorePaid currentBoundary
requiredObligationPaid exactConsumerRecovery =
  Current.exactConsumerRecoveryPaid currentBoundary
requiredObligationPaid leastSufficientConsumerObserver =
  Current.leastSufficientHiddenOtherObserverPaid currentBoundary
requiredObligationPaid recursiveObserverReopening =
  Current.recursiveObserverReopeningPaid currentBoundary
requiredObligationPaid recursiveObserverFibreTower =
  Current.recursiveObserverFibreTowerPaid currentBoundary
requiredObligationPaid observerStreamInverseLimit =
  Current.observerStreamInverseLimitPaid currentBoundary
requiredObligationPaid matureTrialecticDescendantIntegration =
  Current.matureTrialecticGrothendieckDescendantsPaid currentBoundary
requiredObligationPaid setLevelDescentIntegration =
  Current.setLevelEffectiveDescentPaid currentBoundary
requiredObligationPaid c3ContextObstructionAndRepair =
  Current.c3ResidualRepairPaid currentBoundary
requiredObligationPaid nextDepthExpansionUnderdetermination =
  Current.carryExpansionPolicyPaid currentBoundary

allNonginRequiredObligationsPaid :
  (obligation : NonginRequiredObligation) →
  requiredObligationPaid obligation ≡ true
allNonginRequiredObligationsPaid phaseTotalGenealogy = refl
allNonginRequiredObligationsPaid structuralOriginFormalisation = refl
allNonginRequiredObligationsPaid consumerRelativeNonDescent = refl
allNonginRequiredObligationsPaid exactConsumerRecovery = refl
allNonginRequiredObligationsPaid leastSufficientConsumerObserver = refl
allNonginRequiredObligationsPaid recursiveObserverReopening = refl
allNonginRequiredObligationsPaid recursiveObserverFibreTower = refl
allNonginRequiredObligationsPaid observerStreamInverseLimit = refl
allNonginRequiredObligationsPaid matureTrialecticDescendantIntegration = refl
allNonginRequiredObligationsPaid setLevelDescentIntegration = refl
allNonginRequiredObligationsPaid c3ContextObstructionAndRepair = refl
allNonginRequiredObligationsPaid nextDepthExpansionUnderdetermination = refl

------------------------------------------------------------------------
-- 3. Strong receipts retained from the capstone.
------------------------------------------------------------------------

leastSufficientInformationOrderReceipt :
  Advantage.hiddenOtherConsumerIsLeastSufficient leastBoundary ≡ true
leastSufficientInformationOrderReceipt = refl

everyAdequateObserverMustRefineConsumerPaid :
  Advantage.everyAdequateObserverRefinesHiddenOther leastBoundary ≡ true
everyAdequateObserverMustRefineConsumerPaid = refl

c3WholeOldEdgeRetentionNotRequired :
  Current.c3OldFullT9RetentionRequired currentBoundary ≡ false
c3WholeOldEdgeRetentionNotRequired = refl

carrySeedDoesNotDetermineUniqueNextState :
  Current.carrySeedUniqueNextStructuredState currentBoundary ≡ false
carrySeedDoesNotDetermineUniqueNextState = refl

carryAllDepthCoherenceIsNotAutomatic :
  Current.carryAllDepthCoherenceAutomatic currentBoundary ≡ false
carryAllDepthCoherenceIsNotAutomatic = refl

------------------------------------------------------------------------
-- 4. Downstream generalisations are explicitly outside Nongin closure.
------------------------------------------------------------------------

data OptionalDescendantProgramme : Set where
  transportEnrichedGroupoidPresheafProgramme : OptionalDescendantProgramme
  effectiveHigherStackProgramme : OptionalDescendantProgramme
  certifiedHypersheafProgramme : OptionalDescendantProgramme
  exceptionalGroupRealisationProgramme : OptionalDescendantProgramme
  physicalLawPromotionProgramme : OptionalDescendantProgramme

requiredForNonginClosure : OptionalDescendantProgramme → Bool
requiredForNonginClosure transportEnrichedGroupoidPresheafProgramme = false
requiredForNonginClosure effectiveHigherStackProgramme = false
requiredForNonginClosure certifiedHypersheafProgramme = false
requiredForNonginClosure exceptionalGroupRealisationProgramme = false
requiredForNonginClosure physicalLawPromotionProgramme = false

noOptionalDescendantIsRequired :
  (programme : OptionalDescendantProgramme) →
  requiredForNonginClosure programme ≡ false
noOptionalDescendantIsRequired transportEnrichedGroupoidPresheafProgramme = refl
noOptionalDescendantIsRequired effectiveHigherStackProgramme = refl
noOptionalDescendantIsRequired certifiedHypersheafProgramme = refl
noOptionalDescendantIsRequired exceptionalGroupRealisationProgramme = refl
noOptionalDescendantIsRequired physicalLawPromotionProgramme = refl

transportEnrichmentStillOpenButNonBlocking :
  Current.transportEnrichedGroupoidPresheafPaid currentBoundary ≡ false
transportEnrichmentStillOpenButNonBlocking = refl

higherStackStillOpenButNonBlocking :
  Current.certifiedHigherStackPaid currentBoundary ≡ false
higherStackStillOpenButNonBlocking = refl

hypersheafStillOpenButNonBlocking :
  Current.certifiedHypersheafPaid currentBoundary ≡ false
hypersheafStillOpenButNonBlocking = refl

------------------------------------------------------------------------
-- 5. Terminal closure receipt.
------------------------------------------------------------------------

record NonginRoadmapClosureReceipt : Set where
  constructor nongin-roadmap-closure-receipt
  field
    genealogyTotal :
      Atlas.everyDeclaredOriginPhaseHasCanonicalEntry atlasBoundary ≡ true
    allRequiredPaid :
      (obligation : NonginRequiredObligation) →
      requiredObligationPaid obligation ≡ true
    empiricalTenPercentNotPromoted :
      Current.empiricalTenPercentLawPromoted currentBoundary ≡ false
    universalRepresentationAdvantageNotPromoted :
      Current.universalRicherRepresentationAdvantagePromoted currentBoundary ≡ false
    higherStackNotRequired :
      requiredForNonginClosure effectiveHigherStackProgramme ≡ false
    hypersheafNotRequired :
      requiredForNonginClosure certifiedHypersheafProgramme ≡ false
    exceptionalGroupNotRequired :
      Current.exceptionalGroupRealizationRequiredForNongin currentBoundary ≡ false
    physicalLawNotPromoted :
      Current.physicalLawPromotionPaid currentBoundary ≡ false

open NonginRoadmapClosureReceipt public

canonicalNonginRoadmapClosureReceipt : NonginRoadmapClosureReceipt
canonicalNonginRoadmapClosureReceipt =
  nongin-roadmap-closure-receipt
    refl
    allNonginRequiredObligationsPaid
    refl
    refl
    refl
    refl
    refl
    refl

record NonginRoadmapClosureBoundary : Set where
  constructor nongin-roadmap-closure-boundary
  field
    genealogyPhaseTotalityPaid : Bool
    semanticRoadmapRequiredObligationsPaid : Bool
    leastSufficientInformationOrderPaid : Bool
    recursiveObserverInverseLimitPaid : Bool
    trialecticDescendantIntegrationPaid : Bool
    c3ResidualRepairPaid : Bool
    carryExpansionUnderdeterminationPaid : Bool
    nonginRoadmapClosed : Bool
    higherStackRequiredForNonginClosure : Bool
    hypersheafRequiredForNonginClosure : Bool
    physicalLawPromotionRequiredForNonginClosure : Bool

open NonginRoadmapClosureBoundary public

canonicalNonginRoadmapClosureBoundary : NonginRoadmapClosureBoundary
canonicalNonginRoadmapClosureBoundary =
  nongin-roadmap-closure-boundary
    true true true true true true true true
    false false false
