module DASHI.Governance.SecondOrderJusticeGrammarExact where

------------------------------------------------------------------------
-- SECOND-ORDER JUSTICE GRAMMAR
--
-- PowerAndGrammar already defines second-order power as control over the
-- grammar, quotient, evidence-legibility and promotion policy through which
-- first-order claims become institutionally legible.  Here that generic carrier
-- is instantiated against an exact justice-relevant quotient collision.
--
-- No named actor is classified as unjust by this module.  The Palestine/Amalek
-- carrier is used only because the repository already contains a finite,
-- explicit non-injective quotient witness with strict promotion boundaries.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Governance.JusticeCrossPollinationBridgeExact as Cross
import DASHI.Philosophy.PowerAndGrammar as Power
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Enemy

------------------------------------------------------------------------
-- The grammar declares exactly those fine actors quotiented together whose
-- existing rhetorical-compression observations coincide.
------------------------------------------------------------------------

enemyCompressionGrammar : Power.ClaimGrammar Enemy.ConcreteActor
enemyCompressionGrammar = record
  { Power.expressible = λ claim → ⊤
  ; Power.admissible = λ claim → ⊤
  ; Power.quotientedTogether = λ left right →
      Enemy.rhetoricalCompression left ≡ Enemy.rhetoricalCompression right
  }

enemyCompressionPromotionPolicy : Power.PromotionPolicy Enemy.ConcreteActor
enemyCompressionPromotionPolicy = record
  { Power.evidenceLegible = λ claim → ⊤
  ; Power.promotable = λ claim → ⊤
  ; Power.residualIgnored = λ claim → ⊤
  }

data GrammarCode : Set where grammarCode : GrammarCode
data PolicyCode : Set where policyCode : PolicyCode

canonicalSecondOrderCompressionPower :
  Power.SecondOrderPower Enemy.ConcreteActor GrammarCode PolicyCode
canonicalSecondOrderCompressionPower = record
  { Power.grammar = enemyCompressionGrammar
  ; Power.promotion = enemyCompressionPromotionPolicy
  ; Power.transformGrammarCode = λ code → code
  ; Power.transformPolicyCode = λ code → code
  ; Power.controlsWhichDistinctionsCount = ⊤
  ; Power.controlsWhichEvidenceIsLegible = ⊤
  ; Power.controlsWhichClaimsPromote = ⊤
  ; Power.accountabilityWitness = ⊤
  }

canonicalCompressionPowerControlsDistinctions :
  Power.controlsWhichDistinctionsCount canonicalSecondOrderCompressionPower
canonicalCompressionPowerControlsDistinctions = tt

canonicalGrammarCollapsesActorAndCivilianPopulation :
  Power.quotientedTogether
    (Power.grammar canonicalSecondOrderCompressionPower)
    Enemy.hamasActor
    Enemy.palestinianCivilianPopulation
canonicalGrammarCollapsesActorAndCivilianPopulation =
  Enemy.combatantAndCivilianCollapseUnderCompression

------------------------------------------------------------------------
-- Justice blindness is an exact non-factorability property, not an inferred
-- psychological or political motive.
------------------------------------------------------------------------

record JusticeBlindGrammarWitness : Set₁ where
  constructor justiceBlindGrammarWitness
  field
    secondOrderPower :
      Power.SecondOrderPower Enemy.ConcreteActor GrammarCode PolicyCode
    left right : Enemy.ConcreteActor
    grammarCollapsesPair :
      Power.quotientedTogether
        (Power.grammar secondOrderPower)
        left right
    fineTreatmentsDiffer :
      Cross.fineJusticeAssessment left
      ≡ Cross.fineJusticeAssessment right →
      ⊥

open JusticeBlindGrammarWitness public

canonicalJusticeBlindGrammarWitness : JusticeBlindGrammarWitness
canonicalJusticeBlindGrammarWitness =
  justiceBlindGrammarWitness
    canonicalSecondOrderCompressionPower
    Enemy.hamasActor
    Enemy.palestinianCivilianPopulation
    Enemy.combatantAndCivilianCollapseUnderCompression
    Cross.combatantCivilianAssessmentsDiffer

justiceNonFactorabilityBlocksCoarseGovernanceGrammar :
  NonFactor.FactorsThrough
    Enemy.rhetoricalCompression
    Cross.fineJusticeAssessment →
  ⊥
justiceNonFactorabilityBlocksCoarseGovernanceGrammar =
  Cross.justiceRelevantEnemyCompressionCannotBeJusticeSufficient

secondOrderPowerCanInduceJusticeBlindnessWitness :
  JusticeBlindGrammarWitness
secondOrderPowerCanInduceJusticeBlindnessWitness =
  canonicalJusticeBlindGrammarWitness

record SecondOrderJusticeGrammarBoundary : Set where
  constructor secondOrderJusticeGrammarBoundary
  field
    grammarControlAutomaticallyProvesBadMotive : Bool
    quotientCollisionMayBeJusticeRelevant : Bool
    coarseGrammarCanRecoverMissingFineTreatmentWithoutRefinement : Bool
    evidencePolicyControlEqualsTruth : Bool
    livePoliticalApplicationRequiresExternalEvidence : Bool

canonicalSecondOrderJusticeGrammarBoundary : SecondOrderJusticeGrammarBoundary
canonicalSecondOrderJusticeGrammarBoundary =
  secondOrderJusticeGrammarBoundary false true false false true
