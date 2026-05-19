module DASHI.Physics.Closure.ShiftContractCollapseTime where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
  using
    ( PrefixBoundaryShape
    ; ShiftContractGeneratorTaxonomy
    ; canonicalShiftContractGeneratorTaxonomy
    ; prefixFourthStepShape
    ; boundaryUnknown
    ; boundaryExit
    ; boundaryExitToAnchored
    ; boundaryStay
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily as MTF
  using
    ( MixedScaleGeneratorClass
    ; fullSupportCascade
    ; supportCascade
    )
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily as PTF
  using
    ( GeneratorClass
    ; anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    )

------------------------------------------------------------------------
-- Coarse collapse-time observable above the generator taxonomy.
--
-- Keep the codomain intentionally coarse:
-- - immediateExit: exits the current `π-mdl-max` fibre at the next live step
-- - exitToAnchored: exits the current fibre into the anchored branch
-- - staysOneMoreStep: remains in the current fibre for one more live step
-- - unknownCollapse: reserved for future generator classes that have not yet
--   been classified

data CollapseTime : Set where
  immediateExit : CollapseTime
  exitToAnchored : CollapseTime
  staysOneMoreStep : CollapseTime
  unknownCollapse : CollapseTime

collapseTimePrefix : GeneratorClass → CollapseTime
collapseTimePrefix c with
  prefixFourthStepShape canonicalShiftContractGeneratorTaxonomy c
... | boundaryExit = immediateExit
... | boundaryExitToAnchored = exitToAnchored
... | boundaryStay = staysOneMoreStep
... | boundaryUnknown = unknownCollapse

collapseTime-explicitWidth1 :
  collapseTimePrefix explicitWidth1 ≡ staysOneMoreStep
collapseTime-explicitWidth1 = refl

collapseTime-explicitWidth2 :
  collapseTimePrefix explicitWidth2 ≡ immediateExit
collapseTime-explicitWidth2 = refl

collapseTime-explicitWidth3 :
  collapseTimePrefix explicitWidth3 ≡ staysOneMoreStep
collapseTime-explicitWidth3 = refl

collapseTime-balancedCycle :
  collapseTimePrefix balancedCycle ≡ exitToAnchored
collapseTime-balancedCycle = refl

collapseTime-denseComposed :
  collapseTimePrefix denseComposed ≡ staysOneMoreStep
collapseTime-denseComposed = refl

collapseTime-balancedComposed :
  collapseTimePrefix balancedComposed ≡ exitToAnchored
collapseTime-balancedComposed = refl

collapseTime-anchoredTrajectory :
  collapseTimePrefix anchoredTrajectory ≡ immediateExit
collapseTime-anchoredTrajectory = refl

collapseTimeMixedScale : MixedScaleGeneratorClass → CollapseTime
collapseTimeMixedScale supportCascade = staysOneMoreStep
collapseTimeMixedScale fullSupportCascade = immediateExit

collapseTime-supportCascade :
  collapseTimeMixedScale supportCascade ≡ staysOneMoreStep
collapseTime-supportCascade = refl

collapseTime-fullSupportCascade :
  collapseTimeMixedScale fullSupportCascade ≡ immediateExit
collapseTime-fullSupportCascade = refl

data GeneratorCollapseClass : Set where
  prefixClass : GeneratorClass → GeneratorCollapseClass
  mixedScaleClass : MixedScaleGeneratorClass → GeneratorCollapseClass

collapseTime : GeneratorCollapseClass → CollapseTime
collapseTime (prefixClass c) = collapseTimePrefix c
collapseTime (mixedScaleClass c) = collapseTimeMixedScale c
