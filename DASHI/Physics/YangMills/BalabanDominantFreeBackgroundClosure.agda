module DASHI.Physics.YangMills.BalabanDominantFreeBackgroundClosure where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanBackgroundFieldClosure as Background
import DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity as Coercivity
import DASHI.Physics.YangMills.BalabanReferenceGreenPerturbation as Green
import DASHI.Physics.YangMills.BalabanNonlinearComponentLipschitz as Nonlinear
import DASHI.Physics.YangMills.BalabanCriticalBallSelfMap as Ball

record DominantFreeBackgroundInputs
    (Index Coarse State Bound Gauge : Set)
    (criticalMap₀ : State → State)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    coercivityData : Coercivity.RelativeHessianCoercivityData Index State Bound
    greenData : Green.ReferenceGreenPerturbationData Index State Bound
    nonlinearData : Nonlinear.SevenComponentNonlinearData Index State Bound
    ballData : Ball.CriticalBallSelfMapData Index State Bound
    randomWalk : Background.UniformPatchwiseRandomWalk Index State Bound
    semanticClosure : Background.BackgroundFieldClosure
      Coarse State Gauge criticalMap₀ Critical Minimizer
    criticalMapFromGreenNonlinear : Index → State → State
    inverseIsWeightedGreen : ∀ index source →
      Coercivity.green coercivityData index source ≡
      Green.fullGreen greenData index source
    randomWalkIsWeightedGreen : ∀ index source →
      Background.UniformPatchwiseRandomWalk.green randomWalk index source ≡
      Green.fullGreen greenData index source
    criticalMapDefinition : ∀ index state →
      Ball.criticalMap ballData index state ≡
      criticalMapFromGreenNonlinear index state
    nonlinearOperatorMatches : ∀ index state →
      Nonlinear.nonlinear nonlinearData index state ≡
      Background.UniformNonlinearRemainderEstimate.nonlinear
        (Nonlinear.toUniformNonlinearRemainderEstimate nonlinearData)
        index state
    nonlinearBallToCriticalBall : ∀ index state →
      Nonlinear.InCriticalBall nonlinearData index state →
      Ball.InCriticalBall ballData index state
    criticalBallToNonlinearBall : ∀ index state →
      Ball.InCriticalBall ballData index state →
      Nonlinear.InCriticalBall nonlinearData index state
    greenUpperMatches :
      Ball.greenUpper ballData ≡
      Background.UniformWeightedGreenEstimates.greenUpper
        (Green.toUniformWeightedGreenEstimates greenData)
    nonlinearUpperMatches :
      Ball.nonlinearUpper ballData ≡ Nonlinear.nonlinearUpper nonlinearData

open DominantFreeBackgroundInputs public

record DominantFreeBackgroundCertificate
    (Index Coarse State Bound Gauge : Set)
    (criticalMap₀ : State → State)
    (Critical Minimizer : State → Set) : Set₁ where
  field
    inputs : DominantFreeBackgroundInputs
      Index Coarse State Bound Gauge criticalMap₀ Critical Minimizer
    analyticClosure : Background.BackgroundFieldAnalyticClosure
      Index Coarse State Bound Bound Gauge criticalMap₀ Critical Minimizer
    inverseIsWeightedGreen : ∀ index source →
      Coercivity.green (coercivityData inputs) index source ≡
      Green.fullGreen (greenData inputs) index source
    randomWalkIsWeightedGreen : ∀ index source →
      Background.UniformPatchwiseRandomWalk.green (randomWalk inputs) index source ≡
      Green.fullGreen (greenData inputs) index source
    criticalMapDefinition : ∀ index state →
      Ball.criticalMap (ballData inputs) index state ≡
      criticalMapFromGreenNonlinear inputs index state

open DominantFreeBackgroundCertificate public

assembleDominantFreeBackground :
  ∀ {Index Coarse State Bound Gauge : Set}
    {criticalMap₀ : State → State}
    {Critical Minimizer : State → Set} →
  (inputs : DominantFreeBackgroundInputs
    Index Coarse State Bound Gauge criticalMap₀ Critical Minimizer) →
  DominantFreeBackgroundCertificate
    Index Coarse State Bound Gauge criticalMap₀ Critical Minimizer
assembleDominantFreeBackground inputs = record
  { inputs = inputs
  ; analyticClosure =
      Background.assembleBackgroundFieldAnalyticClosure
        (Coercivity.toUniformConstrainedHessianCoercivity (coercivityData inputs))
        (Green.toUniformWeightedGreenEstimates (greenData inputs))
        (randomWalk inputs)
        (Nonlinear.toUniformNonlinearRemainderEstimate (nonlinearData inputs))
        (Ball.toCriticalBallBudget (ballData inputs))
        (semanticClosure inputs)
  ; inverseIsWeightedGreen =
      DominantFreeBackgroundInputs.inverseIsWeightedGreen inputs
  ; randomWalkIsWeightedGreen =
      DominantFreeBackgroundInputs.randomWalkIsWeightedGreen inputs
  ; criticalMapDefinition =
      DominantFreeBackgroundInputs.criticalMapDefinition inputs
  }

dominantFreeBackgroundAssemblyLevel : ProofLevel
dominantFreeBackgroundAssemblyLevel = machineChecked

dominantFreeBackgroundProducerInputsLevel : ProofLevel
dominantFreeBackgroundProducerInputsLevel = conditional
