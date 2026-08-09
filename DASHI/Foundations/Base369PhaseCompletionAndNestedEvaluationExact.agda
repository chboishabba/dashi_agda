module DASHI.Foundations.Base369PhaseCompletionAndNestedEvaluationExact where

------------------------------------------------------------------------
-- A completed balanced phase block is not deleted.  It remains as a fine
-- fibre while an observer may map the complete orbit to a coarse state or to
-- an evaluation zero.  This separates phase, instantiation and observation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; sspNegOne
  ; sspZero
  ; sspPosOne
  )

open import DASHI.Foundations.Base369CompletedRelationalDigitExact using
  ( CompletionBit
  ; uninstantiated
  ; instantiated
  ; RelationalZeroWitness
  ; emptyZero
  ; balancedEvaluationZero
  ; invariantNeutralZero
  )

record BalancedPhaseFibre (Sector : Set) : Set where
  constructor balancedPhaseFibre
  field
    negativeSector : Sector
    neutralSector : Sector
    positiveSector : Sector

open BalancedPhaseFibre public

phaseLabel : {Sector : Set} → BalancedPhaseFibre Sector → SSPTrit → Sector
phaseLabel fibre sspNegOne = negativeSector fibre
phaseLabel fibre sspZero = neutralSector fibre
phaseLabel fibre sspPosOne = positiveSector fibre

record PhaseCompletion (Fine Coarse : Set) : Set₁ where
  constructor phaseCompletion
  field
    fineFibre : BalancedPhaseFibre Fine
    completionStatus : CompletionBit
    coarseCompletedState : Coarse

open PhaseCompletion public

record FibreObserver (Fine Observation : Set) : Set₁ where
  constructor fibreObserver
  field
    observeFine : BalancedPhaseFibre Fine → Observation
    zeroWitness : BalancedPhaseFibre Fine → RelationalZeroWitness

open FibreObserver public

record NestedPhaseFibre (Fine Coarse : Set) : Set₁ where
  constructor nestedPhaseFibre
  field
    level : Nat
    completedBlock : PhaseCompletion Fine Coarse
    retainedFineFibre : BalancedPhaseFibre Fine
    coarseState : Coarse

open NestedPhaseFibre public

promoteCompletedBlock :
  {Fine Coarse : Set} →
  Nat → PhaseCompletion Fine Coarse → NestedPhaseFibre Fine Coarse
promoteCompletedBlock level block =
  nestedPhaseFibre
    (suc level)
    block
    (fineFibre block)
    (coarseCompletedState block)

promotionRetainsFineFibre :
  {Fine Coarse : Set} →
  (level : Nat) →
  (block : PhaseCompletion Fine Coarse) →
  retainedFineFibre (promoteCompletedBlock level block)
  ≡ fineFibre block
promotionRetainsFineFibre level block = refl

promotionAdvancesLevel :
  {Fine Coarse : Set} →
  (level : Nat) →
  (block : PhaseCompletion Fine Coarse) →
  NestedPhaseFibre.level (promoteCompletedBlock level block) ≡ suc level
promotionAdvancesLevel level block = refl

emptyPhaseCompletion :
  {Fine Coarse : Set} →
  BalancedPhaseFibre Fine → Coarse → PhaseCompletion Fine Coarse
emptyPhaseCompletion fibre coarse =
  phaseCompletion fibre uninstantiated coarse

instantiatedPhaseCompletion :
  {Fine Coarse : Set} →
  BalancedPhaseFibre Fine → Coarse → PhaseCompletion Fine Coarse
instantiatedPhaseCompletion fibre coarse =
  phaseCompletion fibre instantiated coarse

-- Three zero witnesses remain distinct even when an external numeric observer
-- maps all of them to the same scalar zero.
emptyZeroWitness : RelationalZeroWitness
emptyZeroWitness = emptyZero

cancelledOrbitZeroWitness : RelationalZeroWitness
cancelledOrbitZeroWitness = balancedEvaluationZero

fixedNeutralZeroWitness : RelationalZeroWitness
fixedNeutralZeroWitness = invariantNeutralZero
