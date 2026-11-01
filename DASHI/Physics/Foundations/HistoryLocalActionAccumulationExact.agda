module DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List using (_++_)

------------------------------------------------------------------------
-- Generic finite action generator from local step contributions.
--
-- This owner deliberately says nothing about which local valuation is
-- physically correct.  It only closes the algebraic arrow
--
--   local contribution -> additive finite-history functional.
------------------------------------------------------------------------

record LocalActionSystem : Set₁ where
  field
    State : Set
    localAction : State → State → Nat
    actionReading : String

open LocalActionSystem public

Step : LocalActionSystem → Set
Step surface = State surface × State surface

stepAction :
  (surface : LocalActionSystem) →
  Step surface →
  Nat
stepAction surface (left , right) =
  localAction surface left right

historyAction :
  (surface : LocalActionSystem) →
  List (Step surface) →
  Nat
historyAction surface [] = zero
historyAction surface (step ∷ rest) =
  stepAction surface step + historyAction surface rest

historyActionSingleton :
  (surface : LocalActionSystem) →
  (step : Step surface) →
  historyAction surface (step ∷ []) ≡ stepAction surface step
historyActionSingleton surface step
  rewrite +-identityʳ (stepAction surface step) =
  refl

historyActionAppend :
  (surface : LocalActionSystem) →
  (left right : List (Step surface)) →
  historyAction surface (left ++ right)
  ≡
  historyAction surface left + historyAction surface right
historyActionAppend surface [] right = refl
historyActionAppend surface (step ∷ rest) right
  rewrite historyActionAppend surface rest right
        | +-assoc
            (stepAction surface step)
            (historyAction surface rest)
            (historyAction surface right) =
  refl

------------------------------------------------------------------------
-- Pointwise symmetry/invariance lifts automatically to the accumulated
-- history functional.
------------------------------------------------------------------------

record LocalActionSymmetry (surface : LocalActionSystem) : Set₁ where
  field
    transform : State surface → State surface
    transformInvolutive :
      (state : State surface) →
      transform (transform state) ≡ state

    localActionInvariant :
      (left right : State surface) →
      localAction surface (transform left) (transform right)
      ≡
      localAction surface left right

open LocalActionSymmetry public

transformStep :
  {surface : LocalActionSystem} →
  LocalActionSymmetry surface →
  Step surface →
  Step surface
transformStep symmetry (left , right) =
  transform symmetry left , transform symmetry right

transformTrace :
  {surface : LocalActionSystem} →
  LocalActionSymmetry surface →
  List (Step surface) →
  List (Step surface)
transformTrace symmetry [] = []
transformTrace symmetry (step ∷ rest) =
  transformStep symmetry step ∷ transformTrace symmetry rest

stepActionInvariant :
  {surface : LocalActionSystem} →
  (symmetry : LocalActionSymmetry surface) →
  (step : Step surface) →
  stepAction surface (transformStep symmetry step)
  ≡
  stepAction surface step
stepActionInvariant symmetry (left , right) =
  localActionInvariant symmetry left right

historyActionInvariant :
  {surface : LocalActionSystem} →
  (symmetry : LocalActionSymmetry surface) →
  (trace : List (Step surface)) →
  historyAction surface (transformTrace symmetry trace)
  ≡
  historyAction surface trace
historyActionInvariant symmetry [] = refl
historyActionInvariant symmetry (step ∷ rest)
  rewrite stepActionInvariant symmetry step
        | historyActionInvariant symmetry rest =
  refl

record LocalActionAccumulationBoundary : Set where
  constructor localActionAccumulationBoundary
  field
    additiveFunctionalDeterminesPhysicalUnits : Bool
    additiveFunctionalDeterminesPhysicalUnitsIsFalse :
      additiveFunctionalDeterminesPhysicalUnits ≡ false

    symmetryInvariantFunctionalIsAutomaticallyPhysicalAction : Bool
    symmetryInvariantFunctionalIsAutomaticallyPhysicalActionIsFalse :
      symmetryInvariantFunctionalIsAutomaticallyPhysicalAction ≡ false

    finiteAdditivityProvesContinuumAction : Bool
    finiteAdditivityProvesContinuumActionIsFalse :
      finiteAdditivityProvesContinuumAction ≡ false

canonicalLocalActionAccumulationBoundary : LocalActionAccumulationBoundary
canonicalLocalActionAccumulationBoundary =
  localActionAccumulationBoundary
    false refl
    false refl
    false refl
