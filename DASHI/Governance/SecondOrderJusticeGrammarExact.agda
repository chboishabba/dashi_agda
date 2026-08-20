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

enemyCompressionGrammar : Power.ClaimGrammar Enemy.ConcreteActor
enemyCompressionGrammar = record
  { expressible = λ claim → ⊤
  ; admissible = λ claim → ⊤
  ; quotientedTogether = λ left right →
      Enemy.rhetoricalCompression left ≡ Enemy.rhetoricalCompression right
  }

enemyCompressionPromotionPolicy : Power.PromotionPolicy Enemy.ConcreteActor
enemyCompressionPromotionPolicy = record
  { evidenceLegible = λ claim → ⊤
  ; promotable = λ claim → ⊤
  ; residualIgnored = λ claim → ⊤
  }

data GrammarCode : Set where grammarCode : GrammarCode
data PolicyCode : Set where policyCode : PolicyCode

canonicalSecondOrderCompressionPower :
  Power.SecondOrderPower Enemy.ConcreteActor GrammarCode PolicyCode
canonicalSecondOrderCompressionPower = record
  { grammar = enemyCompressionGrammar
  ; promotion = enemyCompressionPromotionPolicy
  ; transformGrammarCode = λ code → code
  ; transformPolicyCode = λ code → code
  ; controlsWhichDistinctionsCount = ⊤
  ; controlsWhichEvidenceIsLegible = ⊤
  ; controlsWhichClaimsPromote = ⊤
  ; accountabilityWitness = ⊤
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
