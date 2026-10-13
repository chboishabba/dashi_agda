module DASHI.Core.IntegrationConsumerDescentOrderExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- GENERIC INTEGRATION / OBSERVER CONTRACT
--
-- Equality descent and order preservation are separate obligations.
-- A scalar can be sufficient for one consumer while failing to preserve the
-- ordering required by another consumer.  This owner is intentionally domain
-- neutral: IIT, spectral summaries, latent scores, graph cuts and biological
-- observables all instantiate the same kernel.
------------------------------------------------------------------------

Relation : Set → Set₁
Relation A = A → A → Set

Preserves :
  ∀ {A B : Set} →
  (A → B) → Relation A → Relation B → Set
Preserves observe sourceRelation targetRelation =
  ∀ left right → sourceRelation left right →
    targetRelation (observe left) (observe right)

Reflects :
  ∀ {A B : Set} →
  (A → B) → Relation A → Relation B → Set
Reflects observe sourceRelation targetRelation =
  ∀ left right → targetRelation (observe left) (observe right) →
    sourceRelation left right

record OrderFailureWitness
    {A B : Set}
    (observe : A → B)
    (sourceRelation : Relation A)
    (targetRelation : Relation B) : Set where
  constructor orderFailureWitness
  field
    left right : A
    sourceOrdered : sourceRelation left right
    targetOrderFails : targetRelation (observe left) (observe right) → ⊥

open OrderFailureWitness public

orderFailureBlocksPreservation :
  ∀ {A B : Set}
    {observe : A → B}
    {sourceRelation : Relation A}
    {targetRelation : Relation B} →
  OrderFailureWitness observe sourceRelation targetRelation →
  Preserves observe sourceRelation targetRelation →
  ⊥
orderFailureBlocksPreservation witness preserves =
  targetOrderFails witness
    (preserves
      (left witness)
      (right witness)
      (sourceOrdered witness))

record IntegrationObservation
    (State Surface Score : Set) : Set₁ where
  constructor integrationObservation
  field
    observe : State → Surface
    score : State → Score

open IntegrationObservation public

ScoreDescends :
  ∀ {State Surface Score : Set} →
  IntegrationObservation State Surface Score → Set
ScoreDescends observation =
  Descent.FibreConstantFor
    (observe observation)
    (score observation)

ScoreFactorsThrough :
  ∀ {State Surface Score : Set} →
  IntegrationObservation State Surface Score → Set₁
ScoreFactorsThrough observation =
  Descent.FactorsThrough
    (observe observation)
    (score observation)

factorizationPaysDescent :
  ∀ {State Surface Score : Set}
    (observation : IntegrationObservation State Surface Score) →
  ScoreFactorsThrough observation →
  ScoreDescends observation
factorizationPaysDescent observation =
  Descent.factorsThroughImpliesFibreConstant

record IntegrationNonDescentWitness
    {State Surface Score : Set}
    (observation : IntegrationObservation State Surface Score) : Set where
  constructor integrationNonDescentWitness
  field
    witness :
      Descent.ConsumerNonDescentWitness
        (observe observation)
        (score observation)

open IntegrationNonDescentWitness public

nonDescentBlocksScoreFactorization :
  ∀ {State Surface Score : Set}
    {observation : IntegrationObservation State Surface Score} →
  IntegrationNonDescentWitness observation →
  ScoreFactorsThrough observation →
  ⊥
nonDescentBlocksScoreFactorization nonDescent factorization =
  Descent.nonDescentWitnessBlocksFactorization
    (witness nonDescent)
    factorization

record InterpretationFirewall : Set where
  constructor interpretationFirewall
  field
    integrationScoreIsStructuralObservable : Bool
    structuralObservableImpliesPhenomenalIdentity : Bool
    equalScoreImpliesEqualLatentState : Bool
    higherScoreImpliesHigherConsumerValueWithoutOrderProof : Bool
    observerSufficiencyIsConsumerRelative : Bool

open InterpretationFirewall public

canonicalInterpretationFirewall : InterpretationFirewall
canonicalInterpretationFirewall =
  interpretationFirewall true false false false true

structuralScoreDoesNotSelfPromote :
  structuralObservableImpliesPhenomenalIdentity canonicalInterpretationFirewall ≡ false
structuralScoreDoesNotSelfPromote = refl

orderNeedsSeparateProof :
  higherScoreImpliesHigherConsumerValueWithoutOrderProof canonicalInterpretationFirewall ≡ false
orderNeedsSeparateProof = refl
