module DASHI.Core.CoarseFineRelativeFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.FibreRestrictionCore as CanonicalFibre
import DASHI.Core.ProvenanceBearingQuotient as Provenance
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized

------------------------------------------------------------------------
-- COARSE / RELATIVE-FINE FIBRE KERNEL
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

fromProvenanceBearingQuotient :
  ∀ {core : CanonicalFibre.FibreRestrictionCore} →
  Provenance.ProvenanceBearingQuotient core →
  CoarseFineReopening (CanonicalFibre.Carrier core)
fromProvenanceBearingQuotient {core} quotient =
  coarseFineReopening
    (CanonicalFibre.Surface core)
    (Provenance.Receipt quotient)
    (CanonicalFibre.project core)
    (Provenance.receipt quotient)
    (Provenance.reopen quotient)
    (Provenance.reopenExact quotient)

coarseAndRelativeFineDetermineState :
  ∀ {FineState}
    (geometry : CoarseFineReopening FineState)
    {left right : FineState} →
  coarse geometry left ≡ coarse geometry right →
  relativeFine geometry left ≡ relativeFine geometry right →
  left ≡ right
coarseAndRelativeFineDetermineState geometry {left} {right}
    sameCoarse sameFine =
  trans
    (sym (reopenExact geometry left))
    (trans
      (cong
        (λ c → reopen geometry c (relativeFine geometry left))
        sameCoarse)
      (trans
        (cong (reopen geometry (coarse geometry right)) sameFine)
        (reopenExact geometry right)))

relativeFineMustChangeInsideNontrivialCoarseFibre :
  ∀ {FineState}
    (geometry : CoarseFineReopening FineState)
    {left right : FineState} →
  coarse geometry left ≡ coarse geometry right →
  (left ≡ right → ⊥) →
  relativeFine geometry left ≡ relativeFine geometry right → ⊥
relativeFineMustChangeInsideNontrivialCoarseFibre geometry sameCoarse different
    sameFine =
  different (coarseAndRelativeFineDetermineState geometry sameCoarse sameFine)

------------------------------------------------------------------------
-- Observer-refinement weld from PR #584's canonical lattice.
--
-- Adding the retained fine coordinate gives a factorized refinement of the
-- coarse observer, and exact reopening makes the pair observer separating.
------------------------------------------------------------------------

coarseFineObserver :
  ∀ {FineState} →
  (geometry : CoarseFineReopening FineState) →
  FineState → Coarse geometry × RelativeFine geometry
coarseFineObserver geometry state =
  coarse geometry state , relativeFine geometry state

coarseFactorsThroughCoarseFineObserver :
  ∀ {FineState}
    (geometry : CoarseFineReopening FineState) →
  Factorized.FactorizedRefinement
    (coarse geometry)
    (coarseFineObserver geometry)
coarseFactorsThroughCoarseFineObserver geometry =
  Factorized.factorizedRefinement proj₁ (λ state → refl)

coarseFineObserverSeparating :
  ∀ {FineState}
    (geometry : CoarseFineReopening FineState)
    (left right : FineState) →
  coarseFineObserver geometry left ≡ coarseFineObserver geometry right →
  left ≡ right
coarseFineObserverSeparating geometry left right same =
  coarseAndRelativeFineDetermineState geometry
    (cong proj₁ same)
    (cong proj₂ same)

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
coarseProjectionAsExactReduction
    {fineStep = fineStep} {fineObserve = fineObserve}
    geometry dynamics consumer =
  Reduction.consumerRelativeReduction
    (Coarse geometry)
    (coarse geometry)
    fineStep
    (coarseStep dynamics)
    fineObserve
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

record CoarseFineRelativeFibreBoundary : Set where
  constructor coarseFineRelativeFibreBoundary
  field
    thisReplacesCanonicalProvenanceQuotient : Bool
    thisReplacesCanonicalProvenanceQuotientIsFalse :
      thisReplacesCanonicalProvenanceQuotient ≡ false
    canonicalProvenanceReceiptCanInstantiateRelativeFine : Bool
    canonicalProvenanceReceiptCanInstantiateRelativeFineIsTrue :
      canonicalProvenanceReceiptCanInstantiateRelativeFine ≡ true
    coarsePlusRelativeFineDeterminesFineState : Bool
    coarsePlusRelativeFineDeterminesFineStateIsTrue :
      coarsePlusRelativeFineDeterminesFineState ≡ true
    coarseFinePairRefinesCoarseObserver : Bool
    coarseFinePairRefinesCoarseObserverIsTrue :
      coarseFinePairRefinesCoarseObserver ≡ true
    coarseFinePairIsSeparatingWithExactReopening : Bool
    coarseFinePairIsSeparatingWithExactReopeningIsTrue :
      coarseFinePairIsSeparatingWithExactReopening ≡ true
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
    false refl true refl true refl true refl true refl
    false refl true refl true refl true refl false refl
