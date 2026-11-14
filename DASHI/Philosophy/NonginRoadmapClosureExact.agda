module DASHI.Philosophy.NonginRoadmapClosureExact where

------------------------------------------------------------------------
-- NONGIN CORE ROADMAP CLOSURE
--
-- The historical/semantic Nongin core is closed.  Attached descendant research
-- continues in NonginExtendedRoadmapExact; several categorical descendants now
-- advance beyond the conservative status that existed when this core closure
-- owner was first written.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.DialecticOriginSourceAtlasExact as Atlas
import DASHI.Philosophy.NonginCurrentMaxCutExact as Current
import DASHI.Philosophy.NonginGenealogyOwnerWeldExact as Weld
import DASHI.Reasoning.NonginConsumerRelativeFrameAdvantageExact as Advantage

atlasBoundary : Atlas.DialecticOriginSourceAtlasBoundary
atlasBoundary = Atlas.canonicalDialecticOriginSourceAtlasBoundary

currentBoundary : Current.NonginCurrentMaxCutBoundary
currentBoundary = Current.canonicalNonginCurrentMaxCutBoundary

leastBoundary : Advantage.NonginLeastSufficientObserverBoundary
leastBoundary = Advantage.canonicalNonginLeastSufficientObserverBoundary

weldBoundary : Weld.NonginGenealogyOwnerWeldBoundary
weldBoundary = Weld.canonicalNonginGenealogyOwnerWeldBoundary

genealogyPhaseTotalityReceipt :
  Atlas.everyDeclaredOriginPhaseHasCanonicalEntry atlasBoundary ≡ true
genealogyPhaseTotalityReceipt = refl

canonicalEntryReturnsDeclaredPhase :
  (declared : Atlas.OriginPhase) →
  Atlas.phase (Atlas.entryForPhase declared) ≡ declared
canonicalEntryReturnsDeclaredPhase = Atlas.entryForPhaseIsExact

typedGenealogyOwnerWeldReceipt :
  Weld.allTypedDescendantOwnersLinked weldBoundary ≡ true
typedGenealogyOwnerWeldReceipt = refl

data NonginRequiredObligation : Set where
  phaseTotalGenealogy : NonginRequiredObligation
  typedGenealogyOwnerWeld : NonginRequiredObligation
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
requiredObligationPaid typedGenealogyOwnerWeld =
  Weld.allTypedDescendantOwnersLinked weldBoundary
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
allNonginRequiredObligationsPaid typedGenealogyOwnerWeld = refl
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
-- Core closure does not require descendant completion.  This is a dependency
-- statement, not a detachment statement; NonginExtendedRoadmapExact keeps all
-- descendant programmes attached to the same research lineage.
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

transportEnrichmentAdvancedAfterCoreClosure :
  Current.transportEnrichedGroupoidPresheafPaid currentBoundary ≡ true
transportEnrichmentAdvancedAfterCoreClosure = refl

higherStackAdvancedAfterCoreClosure :
  Current.certifiedHigherStackPaid currentBoundary ≡ true
higherStackAdvancedAfterCoreClosure = refl

finiteTriadicHypersheafAdvancedAfterCoreClosure :
  Current.certifiedFiniteTriadicHypersheafPaid currentBoundary ≡ true
finiteTriadicHypersheafAdvancedAfterCoreClosure = refl

arbitraryInfinityHypersheafStillSeparate :
  Current.certifiedArbitraryInfinityHypersheafPaid currentBoundary ≡ false
arbitraryInfinityHypersheafStillSeparate = refl

record NonginRoadmapClosureReceipt : Set where
  constructor nongin-roadmap-closure-receipt
  field
    genealogyTotal :
      Atlas.everyDeclaredOriginPhaseHasCanonicalEntry atlasBoundary ≡ true
    typedOwnersLinked :
      Weld.allTypedDescendantOwnersLinked weldBoundary ≡ true
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
    typedGenealogyOwnersLinked : Bool
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
    true true true true true true true true true
    false false false
