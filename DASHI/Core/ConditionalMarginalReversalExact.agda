module DASHI.Core.ConditionalMarginalReversalExact where

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- E. H. Simpson,
-- "The Interpretation of Interaction in Contingency Tables",
-- Journal of the Royal Statistical Society: Series B (Methodological),
-- 13(2), 238-241 (1951).
-- DOI: 10.1111/j.2517-6161.1951.tb00088.x.
--
-- Steven A. Julious and Mark A. Mullee,
-- "Confounding and Simpson's paradox", BMJ 309, 1480-1481 (1994).
-- DOI: 10.1136/bmj.309.6967.1480.
--
-- The finite counts below are the kidney-stone example reported by Julious
-- and Mullee.  DASHI uses the example only as an exact context-erasure
-- countermodel: a direction which holds in each retained context can reverse
-- after aggregation.  No causal or clinical recommendation is derived here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥)

record OutcomeCounts : Set where
  constructor outcomeCounts
  field
    successes : Nat
    total : Nat

open OutcomeCounts public

combine : OutcomeCounts → OutcomeCounts → OutcomeCounts
combine (outcomeCounts s₁ n₁) (outcomeCounts s₂ n₂) =
  outcomeCounts (s₁ + s₂) (n₁ + n₂)

cross : OutcomeCounts → OutcomeCounts → Nat
cross left right = successes left * total right

------------------------------------------------------------------------
-- A proof-relevant strict rate advantage without division: winner/loser
-- comparison is cross-multiplied, and the positive gap is carried explicitly.
------------------------------------------------------------------------

record StrictRateAdvantage (winner loser : OutcomeCounts) : Set where
  constructor strictRateAdvantage
  field
    gap : Nat
    predecessor : Nat
    gapIsPositive : gap ≡ suc predecessor
    crossGapExact : cross loser winner + gap ≡ cross winner loser

open StrictRateAdvantage public

data Context : Set where
  smallerStoneContext largerStoneContext : Context

data Method : Set where
  methodA methodB : Method

data AdvantageDirection : Set where
  methodAAdvantage methodBAdvantage : AdvantageDirection

counts : Context → Method → OutcomeCounts
counts smallerStoneContext methodA = outcomeCounts 81 87
counts smallerStoneContext methodB = outcomeCounts 234 270
counts largerStoneContext methodA = outcomeCounts 192 263
counts largerStoneContext methodB = outcomeCounts 55 80

smallContextFavoursA :
  StrictRateAdvantage
    (counts smallerStoneContext methodA)
    (counts smallerStoneContext methodB)
smallContextFavoursA = strictRateAdvantage 1512 1511 refl refl

largeContextFavoursA :
  StrictRateAdvantage
    (counts largerStoneContext methodA)
    (counts largerStoneContext methodB)
largeContextFavoursA = strictRateAdvantage 895 894 refl refl

marginalCounts : Method → OutcomeCounts
marginalCounts method =
  combine
    (counts smallerStoneContext method)
    (counts largerStoneContext method)

marginalACountsExact : marginalCounts methodA ≡ outcomeCounts 273 350
marginalACountsExact = refl

marginalBCountsExact : marginalCounts methodB ≡ outcomeCounts 289 350
marginalBCountsExact = refl

marginalFavoursB :
  StrictRateAdvantage (marginalCounts methodB) (marginalCounts methodA)
marginalFavoursB = strictRateAdvantage 5600 5599 refl refl

conditionalDirection : Context → AdvantageDirection
conditionalDirection smallerStoneContext = methodAAdvantage
conditionalDirection largerStoneContext = methodAAdvantage

marginalDirection : AdvantageDirection
marginalDirection = methodBAdvantage

conditionalSmallDiffersFromMarginal :
  conditionalDirection smallerStoneContext ≡ marginalDirection → ⊥
conditionalSmallDiffersFromMarginal ()

conditionalLargeDiffersFromMarginal :
  conditionalDirection largerStoneContext ≡ marginalDirection → ⊥
conditionalLargeDiffersFromMarginal ()

record ConditionalMarginalReversalWitness : Set where
  constructor conditionalMarginalReversalWitness
  field
    firstContextFavoursA :
      StrictRateAdvantage
        (counts smallerStoneContext methodA)
        (counts smallerStoneContext methodB)
    secondContextFavoursA :
      StrictRateAdvantage
        (counts largerStoneContext methodA)
        (counts largerStoneContext methodB)
    contextForgottenAggregateFavoursB :
      StrictRateAdvantage (marginalCounts methodB) (marginalCounts methodA)

canonicalConditionalMarginalReversalWitness :
  ConditionalMarginalReversalWitness
canonicalConditionalMarginalReversalWitness =
  conditionalMarginalReversalWitness
    smallContextFavoursA
    largeContextFavoursA
    marginalFavoursB

record ConditionalMarginalBoundary : Set where
  field
    marginalDirectionDeterminesEachConditionalDirection : Bool
    contextErasurePreservesAssociationDirectionAutomatically : Bool
    aggregateReversalCreatesCausalConclusion : Bool

canonicalConditionalMarginalBoundary : ConditionalMarginalBoundary
canonicalConditionalMarginalBoundary = record
  { marginalDirectionDeterminesEachConditionalDirection = false
  ; contextErasurePreservesAssociationDirectionAutomatically = false
  ; aggregateReversalCreatesCausalConclusion = false
  }
