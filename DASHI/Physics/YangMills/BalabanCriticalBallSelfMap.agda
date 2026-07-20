module DASHI.Physics.YangMills.BalabanCriticalBallSelfMap where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure as Background

record CriticalBallSelfMapData (Index State Bound : Set) : Set₁ where
  field
    criticalMap : Index → State → State
    zero : State
    subtract : State → State → State
    norm : State → Bound
    radius greenUpper nonlinearUpper rhoG : Bound
    multiply add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set
    transitive : ∀ {left middle right} → LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftPrime right rightPrime} → LessEqual left leftPrime → LessEqual right rightPrime → LessEqual (add left right) (add leftPrime rightPrime)
    reflexive : ∀ value → LessEqual value value
    multiplyMonotoneLeft : ∀ prefix {left right} → LessEqual left right → LessEqual (multiply prefix left) (multiply prefix right)
    triangleFromZero : ∀ index state → LessEqual (norm (criticalMap index state)) (add (norm (criticalMap index zero)) (norm (subtract (criticalMap index state) (criticalMap index zero))))
    contractionFromZero : ∀ index state → LessEqual (norm (subtract (criticalMap index state) (criticalMap index zero))) (multiply rhoG (norm state))
    criticalMapAtZeroBudget : ∀ index → LessEqual (add (norm (criticalMap index zero)) (multiply rhoG radius)) radius
    greenTimesNonlinearBelowRho : LessEqual (multiply greenUpper nonlinearUpper) rhoG
    rhoGStrict : StrictlyBelowOne rhoG

open CriticalBallSelfMapData public

InCriticalBall : ∀ {Index State Bound : Set} → CriticalBallSelfMapData Index State Bound → Index → State → Set
InCriticalBall dataSet index state = LessEqual dataSet (norm dataSet state) (radius dataSet)

criticalMapPreservesBall : ∀ {Index State Bound : Set} → (dataSet : CriticalBallSelfMapData Index State Bound) → ∀ index state → InCriticalBall dataSet index state → InCriticalBall dataSet index (criticalMap dataSet index state)
criticalMapPreservesBall dataSet index state stateInBall =
  transitive dataSet
    (triangleFromZero dataSet index state)
    (transitive dataSet
      (addMonotone dataSet
        (reflexive dataSet (norm dataSet (criticalMap dataSet index (zero dataSet))))
        (contractionFromZero dataSet index state))
      (transitive dataSet
        (addMonotone dataSet
          (reflexive dataSet (norm dataSet (criticalMap dataSet index (zero dataSet))))
          (multiplyMonotoneLeft dataSet (rhoG dataSet) stateInBall))
        (criticalMapAtZeroBudget dataSet index)))

toCriticalBallBudget : ∀ {Index State Bound : Set} → (dataSet : CriticalBallSelfMapData Index State Bound) → Background.CriticalBallBudget Index State Bound
toCriticalBallBudget dataSet = record
  { criticalMap = criticalMap dataSet
  ; InCriticalBall = InCriticalBall dataSet
  ; zero = zero dataSet
  ; norm = norm dataSet
  ; radius = radius dataSet
  ; greenUpper = greenUpper dataSet
  ; nonlinearUpper = nonlinearUpper dataSet
  ; rhoG = rhoG dataSet
  ; multiply = multiply dataSet
  ; add = add dataSet
  ; LessEqual = LessEqual dataSet
  ; StrictlyBelowOne = StrictlyBelowOne dataSet
  ; criticalMapPreservesBall = criticalMapPreservesBall dataSet
  ; criticalMapAtZeroBudget = criticalMapAtZeroBudget dataSet
  ; greenTimesNonlinearBelowRho = greenTimesNonlinearBelowRho dataSet
  ; rhoGStrict = rhoGStrict dataSet
  }

criticalBallSelfMapBridgeLevel : ProofLevel
criticalBallSelfMapBridgeLevel = machineChecked

criticalBallAnalyticInputsLevel : ProofLevel
criticalBallAnalyticInputsLevel = conditional
