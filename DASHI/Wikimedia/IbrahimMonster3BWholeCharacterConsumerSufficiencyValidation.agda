module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterConsumerSufficiencyValidation where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterConsumerSufficiencyExact as P

bidiRegression :
  P.MonsterWholeCharacterConsumerSufficiencyBoundary.consumerIndexedResidualRefinementReused
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ true
  × P.MonsterWholeCharacterConsumerSufficiencyBoundary.wholeCharacterMayBeSufficientForIsotypicConsumer
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ true
  × P.MonsterWholeCharacterConsumerSufficiencyBoundary.failureMustReturnConsumerRelevantResidual
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ true
  × P.MonsterWholeCharacterConsumerSufficiencyBoundary.wholeCharacterSufficiencyCreatesConcreteBasisActionRecognition
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ false
bidiRegression = refl , refl , refl , refl

paymentRegression :
  P.MonsterWholeCharacterConsumerSufficiencyBoundary.wholeCharacterLeanProducerPaid
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ false
  × P.MonsterWholeCharacterConsumerSufficiencyBoundary.literalConstituentFallbackRetained
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ true
  × P.MonsterWholeCharacterConsumerSufficiencyBoundary.oeisCreatesConsumerSufficiency
    P.canonicalMonsterWholeCharacterConsumerSufficiencyBoundary
  ≡ false
paymentRegression = refl , refl , refl
