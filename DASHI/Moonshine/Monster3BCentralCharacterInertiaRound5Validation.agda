module DASHI.Moonshine.Monster3BCentralCharacterInertiaRound5Validation where

import DASHI.Moonshine.Monster3BOrbifoldLocalModuleRound4Validation
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.MonsterOggNonaryProbeAuthorityExact as Probe
import DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact as Pipeline
import DASHI.Moonshine.Monster3BMultiplicityTwelveSeventyEightRecognitionExact as Split
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Multiplicity
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_/_)

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

------------------------------------------------------------------------
-- Complete nonary address and residue exclusion.
------------------------------------------------------------------------

allOggAddressesReconstruct :
  (prime : Lane.MonsterPrimeLane) →
  Lane.monsterPrimeLaneToNat prime
  ≡ Probe.coarseSheets (Probe.nonaryProbe prime) * 9
    + Probe.fineResidue (Probe.nonaryProbe prime)
allOggAddressesReconstruct prime = Probe.addressExact (Probe.nonaryProbe prime)

allOggResiduesExcludeZero :
  (prime : Lane.MonsterPrimeLane) →
  Probe.fineResidue (Probe.nonaryProbe prime) ≡ 0 → ⊥
allOggResiduesExcludeZero = Probe.allOggFineResiduesAvoidZero

allOggResiduesExcludeSix :
  (prime : Lane.MonsterPrimeLane) →
  Probe.fineResidue (Probe.nonaryProbe prime) ≡ 6 → ⊥
allOggResiduesExcludeSix = Probe.allOggFineResiduesAvoidSix

unitComplementIsInvolutive :
  ∀ {residue} →
  (unit : Probe.UnitResidue9 residue) →
  Probe.complementUnitResidue (Probe.complementUnitWitness unit) ≡ residue
unitComplementIsInvolutive = Probe.complementUnitResidueInvolutive

unitComplementPreservesMode :
  ∀ {residue} →
  (unit : Probe.UnitResidue9 residue) →
  Probe.unitComplementMode (Probe.complementUnitWitness unit)
  ≡ Probe.unitComplementMode unit
unitComplementPreservesMode = Probe.complementPreservesUnitMode

unitComplementReversesOrientation :
  ∀ {residue} →
  (unit : Probe.UnitResidue9 residue) →
  Probe.unitOrientation (Probe.complementUnitWitness unit)
  ≡ Probe.flipOrientation (Probe.unitOrientation unit)
unitComplementReversesOrientation = Probe.complementFlipsUnitOrientation

------------------------------------------------------------------------
-- Sorted signature versus actual FRACTRAN firing relation.
------------------------------------------------------------------------

uniformOrderedPlusThreeIsImpossible :
  Probe.ProposedFractranOrderedPlusThree → ⊥
uniformOrderedPlusThreeIsImpossible =
  Probe.proposedFractranOrderedPlusThreeImpossible

actualReplacementPlusThreeIsImpossible :
  (replacement : Probe.ActualFractranReplacement) →
  Probe.plusThreeResidue (Probe.replacementSourceResidue replacement)
  ≡ Probe.replacementTargetResidue replacement → ⊥
actualReplacementPlusThreeIsImpossible =
  Probe.actualFractranReplacementIsNotPlusThree

actualEarningChainReaches196883 :
  (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 196883
actualEarningChainReaches196883 = Probe.actualFractranEarningChain

earnedProductAdjoinsOneTo196884 : 47 * 59 * 71 + 1 ≡ 196884
earnedProductAdjoinsOneTo196884 = Probe.earnedPrimeProductPlusOneIs196884

------------------------------------------------------------------------
-- Depth-two reflection and precise 7A normalization.
------------------------------------------------------------------------

fortyOneReflectionPairIsExact :
  Probe.leftPrimeValue Probe.pair41And41
  + Probe.rightPrimeValue Probe.pair41And41 ≡ 82
fortyOneReflectionPairIsExact =
  Probe.reflectionPairSumsTo82 Probe.pair41And41

fortyOneIsPointedMidpoint : 2 * 41 ≡ 81 + 1
fortyOneIsPointedMidpoint = Probe.fortyOneIsPointedMidpointOfEightyOne

seventyOneCompletesWithTen : 71 + 10 ≡ 81
seventyOneCompletesWithTen = Probe.seventyOnePlusTenCompletesEightyOne

rawSevenAConstantIsTen :
  Probe.unnormalizedSevenAEtaQuotientCoefficient Probe.constantDegree ≡ 10
rawSevenAConstantIsTen = Probe.unnormalizedSevenAConstantIsTen

normalizedSevenAConstantVanishes :
  Probe.normalizedSevenAHauptmodulCoefficient Probe.constantDegree ≡ 0
normalizedSevenAConstantVanishes = Probe.normalizedSevenAConstantIsZero

sevenANormalizationOffsetIsTen :
  Probe.normalizedSevenAHauptmodulCoefficient Probe.constantDegree + 10
  ≡ Probe.unnormalizedSevenAEtaQuotientCoefficient Probe.constantDegree
sevenANormalizationOffsetIsTen = Probe.sevenANormalizationRemovesTen

seventyOneDeficitMatchesRawSevenAOffset :
  71 + Probe.unnormalizedSevenAEtaQuotientCoefficient Probe.constantDegree
  ≡ 81
seventyOneDeficitMatchesRawSevenAOffset =
  Probe.seventyOneDeficitMatchesUnnormalizedSevenAConstant

------------------------------------------------------------------------
-- Exact 7+7+1 finite partition and coarse-sheet boundary.
------------------------------------------------------------------------

mirrorAHasSevenLanes : Probe.listCount Probe.canonicalMirrorA7 ≡ 7
mirrorAHasSevenLanes = Probe.mirrorA7CountIsSeven

mirrorBHasSevenLanes : Probe.listCount Probe.canonicalMirrorB7 ≡ 7
mirrorBHasSevenLanes = Probe.mirrorB7CountIsSeven

signBlockHasOneLane : Probe.listCount Probe.canonicalSign1 ≡ 1
signBlockHasOneLane = Probe.sign1CountIsOne

sevenSevenOneReconstructsFifteen :
  Probe.listCount Probe.canonicalMirrorA7
  + Probe.listCount Probe.canonicalMirrorB7
  + Probe.listCount Probe.canonicalSign1 ≡ 15
sevenSevenOneReconstructsFifteen = Probe.semanticSevenSevenOneCountIsFifteen

observerLaneOccupiesCoarseSheetSeven :
  Probe.coarseSheets (Probe.nonaryProbe (Probe.sign1Prime Probe.sign71)) ≡ 7
observerLaneOccupiesCoarseSheetSeven = Probe.sign1CoarseSheetIsSeven

------------------------------------------------------------------------
-- Existing actual-sector pipeline.
------------------------------------------------------------------------

pipelineTransportsOwnWeightProjector :
  (pipeline : Pipeline.ActualZetaPromotionPipeline) →
  (state : Pipeline.chosenZetaSector pipeline) →
  Multiplicity.actualWeightProjectorCoefficient
    (Pipeline.modelRecognition pipeline)
    (Pipeline.chosenWeightPosition pipeline state)
    state
  ≡ 1
pipelineTransportsOwnWeightProjector =
  Pipeline.chosenOwnWeightProjectorCoefficient

twelvePlusSeventyEightDimensionCompatibility : 90 ≡ 12 + 78
twelvePlusSeventyEightDimensionCompatibility =
  Split.ninetyIsTwelvePlusSeventyEight
