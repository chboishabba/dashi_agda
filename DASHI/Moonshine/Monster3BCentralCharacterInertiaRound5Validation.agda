module DASHI.Moonshine.Monster3BCentralCharacterInertiaRound5Validation where

import DASHI.Moonshine.Monster3BOrbifoldLocalModuleRound4Validation
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact as Probe
import DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact as Pipeline
import DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact as Split

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

centralPhaseInversionIsInvolutive :
  (phase : Inertia.CentralPhase3) →
  Inertia.invertPhase (Inertia.invertPhase phase) ≡ phase
centralPhaseInversionIsInvolutive = Inertia.invertPhaseInvolutive

inertiaPreservesChosenPhase :
  ∀ {State Normalizer}
    (action : Inertia.CentralNormalizerAction State Normalizer) →
    Inertia.CentralInertia action →
    Inertia.CentralEigenspace
      (Inertia.phaseAction action) Inertia.phaseZeta →
    Inertia.CentralEigenspace
      (Inertia.phaseAction action) Inertia.phaseZeta
inertiaPreservesChosenPhase = Inertia.inertiaPreservesZetaSector

inverterSwapsChosenPhase :
  ∀ {State Normalizer}
    (action : Inertia.CentralNormalizerAction State Normalizer) →
    Inertia.CentralInverter action →
    Inertia.CentralEigenspace
      (Inertia.phaseAction action) Inertia.phaseZeta →
    Inertia.CentralEigenspace
      (Inertia.phaseAction action) Inertia.phaseZetaSquared
inverterSwapsChosenPhase = Inertia.inverterSendsZetaToZetaSquared

allOggAddressesReconstruct :
  (prime : DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface.MonsterPrimeLane) →
  DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface.monsterPrimeLaneToNat prime
  ≡ Probe.coarseSheets (Probe.nonaryProbe prime) * 9
    + Probe.fineResidue (Probe.nonaryProbe prime)
allOggAddressesReconstruct prime = Probe.addressExact (Probe.nonaryProbe prime)

uniformOrderedPlusThreeIsImpossible :
  Probe.ProposedFractranOrderedPlusThree → ⊥
uniformOrderedPlusThreeIsImpossible =
  Probe.proposedFractranOrderedPlusThreeImpossible

fortyOneReflectionPairIsExact :
  Probe.leftPrimeValue Probe.pair41And41
  + Probe.rightPrimeValue Probe.pair41And41 ≡ 82
fortyOneReflectionPairIsExact =
  Probe.reflectionPairSumsTo82 Probe.pair41And41

pipelineTransportsOwnWeightProjector :
  (pipeline : Pipeline.ActualZetaPromotionPipeline) →
  (state : Pipeline.chosenZetaSector pipeline) →
  DASHI.Moonshine.Monster3BMultiplicityEvaluationExact.actualWeightProjectorCoefficient
    (Pipeline.modelRecognition pipeline)
    (Pipeline.chosenWeightPosition pipeline state)
    state
  ≡ 1
pipelineTransportsOwnWeightProjector =
  Pipeline.chosenOwnWeightProjectorCoefficient

twelvePlusSeventyEightDimensionCompatibility : 90 ≡ 12 + 78
twelvePlusSeventyEightDimensionCompatibility =
  Split.ninetyIsTwelvePlusSeventyEight
