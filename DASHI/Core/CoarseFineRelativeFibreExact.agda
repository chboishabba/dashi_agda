module DASHI.Core.CoarseFineRelativeFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction

------------------------------------------------------------------------
-- COARSE / RELATIVE-FINE FIBRE KERNEL
--
-- A fine state need not be understood as merely "a more expensive coarse
-- state".  It may instead decompose into a coarse coordinate plus residual
-- fine information living over that coarse coordinate.  This module abstracts
-- that pattern without importing any JCoarse/JFine-specific semantics.
------------------------------------------------------------------------

record CoarseFineReopening (FineState : Set) : Set₁ where
  constructor coarseFineReopening
  field
    Coarse RelativeFine : Set
    coarse : FineState → Coarse
    relativeFine : FineState → RelativeFine
    reopen : Coarse → RelativeFine → FineState
    reopenExact :
      (state : FineState) →
      reopen (coarse state) (relativeFine state) ≡ state

open CoarseFineReopening public

------------------------------------------------------------------------
-- A coarse projection is sufficient only if both dynamics and the declared
-- consumer factor through it.
------------------------------------------------------------------------

record CoarseDynamicsClosure
    {FineState Action : Set}
    (geometry : CoarseFineReopening FineState)
    (fineStep : Action → FineState → FineState) : Set₁ where
  constructor coarseDynamicsClosure
  field
    coarseStep : Action → Coarse geometry → Coarse geometry
    stepCommutes :
      (action : Action) (state : FineState) →
      coarse geometry (fineStep action state)
      ≡ coarseStep action (coarse geometry state)

open CoarseDynamicsClosure public

record CoarseConsumerFactorisation
    {FineState Observation : Set}
    (geometry : CoarseFineReopening FineState)
    (fineObserve : FineState → Observation) : Set₁ where
  constructor coarseConsumerFactorisation
  field
    coarseObserve : Coarse geometry → Observation
    observationFactors :
      (state : FineState) →
      fineObserve state ≡ coarseObserve (coarse geometry state)

open CoarseConsumerFactorisation public

coarseProjectionAsExactReduction :
  ∀ {FineState Action Observation}
    {fineStep : Action → FineState → FineState}
    {fineObserve : FineState → Observation}
    (geometry : CoarseFineReopening FineState) →
    (dynamics : CoarseDynamicsClosure geometry fineStep) →
    (consumer : CoarseConsumerFactorisation geometry fineObserve) →
  Reduction.ConsumerRelativeReduction FineState Action Observation
coarseProjectionAsExactReduction geometry dynamics consumer =
  Reduction.consumerRelativeReduction
    (Coarse geometry)
    (coarse geometry)
    _
    (coarseStep dynamics)
    _
    (coarseObserve consumer)
    (stepCommutes dynamics)
    (observationFactors consumer)

coarseProjectionRetainsRelativeFineResidual :
  ∀ {FineState Action Observation}
    {fineStep : Action → FineState → FineState}
    {fineObserve : FineState → Observation}
    (geometry : CoarseFineReopening FineState)
    (dynamics : CoarseDynamicsClosure geometry fineStep)
    (consumer : CoarseConsumerFactorisation geometry fineObserve) →
  Reduction.ExactResidualReopening
    (coarseProjectionAsExactReduction geometry dynamics consumer)
coarseProjectionRetainsRelativeFineResidual geometry dynamics consumer =
  Reduction.exactResidualReopening
    (RelativeFine geometry)
    (relativeFine geometry)
    (reopen geometry)
    (reopenExact geometry)

------------------------------------------------------------------------
-- Conversely, a fine-sensitive consumer gives an immediate proof that the
-- coarse projection is insufficient.  No statement that the fine residual is
-- intrinsically more important is needed: the failure is consumer-relative.
------------------------------------------------------------------------

record FineSensitiveConsumer
    {FineState Observation : Set}
    (geometry : CoarseFineReopening FineState)
    (observe : FineState → Observation) : Set where
  constructor fineSensitiveConsumer
  field
    left right : FineState
    sameCoarse : coarse geometry left ≡ coarse geometry right
    consumerSeparates : observe left ≡ observe right → ⊥
    witnessReference : String

open FineSensitiveConsumer public

fineSensitivityRefutesCoarseOnlyReduction :
  ∀ {FineState Action Observation}
    {fineStep : Action → FineState → FineState}
    {observe : FineState → Observation}
    (geometry : CoarseFineReopening FineState) →
  FineSensitiveConsumer geometry observe →
  Reduction.CandidateReductionFailure
    fineStep observe (coarse geometry)
fineSensitivityRefutesCoarseOnlyReduction geometry witness =
  Reduction.candidateReductionFailure
    (left witness)
    (right witness)
    (sameCoarse witness)
    []
    (consumerSeparates witness)

------------------------------------------------------------------------
-- Relative-fine difference and absolute-state difference are deliberately
-- distinct notions.  Fine data may be essential for one consumer and invisible
-- for another.  The geometry therefore supports both exact coarse reduction and
-- fine-sensitive refutation, depending on the declared consumer.
------------------------------------------------------------------------

record CoarseFineRelativeFibreBoundary : Set where
  constructor coarseFineRelativeFibreBoundary
  field
    fineMeansOnlyHigherComputeCost : Bool
    fineMeansOnlyHigherComputeCostIsFalse :
      fineMeansOnlyHigherComputeCost ≡ false

    fineMayBeRelativeResidualOverCoarse : Bool
    fineMayBeRelativeResidualOverCoarseIsTrue :
      fineMayBeRelativeResidualOverCoarse ≡ true

    coarseProjectionMayBeExactForOneConsumer : Bool
    coarseProjectionMayBeExactForOneConsumerIsTrue :
      coarseProjectionMayBeExactForOneConsumer ≡ true

    sameCoarseMayFailForFineSensitiveConsumer : Bool
    sameCoarseMayFailForFineSensitiveConsumerIsTrue :
      sameCoarseMayFailForFineSensitiveConsumer ≡ true

    discardingFineResidualIsRequiredWhenCoarseIsSafe : Bool
    discardingFineResidualIsRequiredWhenCoarseIsSafeIsFalse :
      discardingFineResidualIsRequiredWhenCoarseIsSafe ≡ false

canonicalCoarseFineRelativeFibreBoundary : CoarseFineRelativeFibreBoundary
canonicalCoarseFineRelativeFibreBoundary =
  coarseFineRelativeFibreBoundary
    false refl true refl true refl true refl false refl
