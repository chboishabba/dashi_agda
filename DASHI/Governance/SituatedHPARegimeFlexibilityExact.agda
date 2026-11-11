module DASHI.Governance.SituatedHPARegimeFlexibilityExact where

-- Original DASHI qualitative regime-capability example.
-- Prior mathematical owner:
-- DASHI.Cognition.ResponseKink.RecruitmentSuppressionProfile
-- Source motivation (not original proof): Yehuda et al., reports of
-- lower cortisol/altered glucocorticoid metabolism in some
-- Holocaust-survivor offspring cohorts. This is NOT a deterministic
-- trauma->high->blunted law or evidence for dorsal-vagal freeze.
open import DASHI.Core.Prelude
import DASHI.Cognition.ResponseKink as Kink
import DASHI.Core.IntersectionalNonFactorability as NF

data HypotheticalLoad : Set where
  lowLoad risingLoad intermediateLoad prolongedLoad : HypotheticalLoad

-- Toy ordinal response map, NOT a cortisol concentration, cohort fit,
-- biological mechanistic bifurcation proof, or trauma score.
responseIndex : HypotheticalLoad → Nat
responseIndex lowLoad = 0
responseIndex risingLoad = 1
responseIndex intermediateLoad = 2
responseIndex prolongedLoad = 1

sampledRegimeProfile :
  Kink.RecruitmentSuppressionProfile HypotheticalLoad
sampledRegimeProfile = record
  { lowInput = lowLoad
  ; prePeakInput = risingLoad
  ; peakInput = intermediateLoad
  ; overloadInput = prolongedLoad
  ; response = responseIndex
  ; low-to-prePeak-rise = n<1+n 0
  ; prePeak-to-peak-rise = n<1+n 1
  ; overload-below-peak = n<1+n 1
  }

regimeShapeInherited :
  (responseIndex lowLoad < responseIndex risingLoad)
  × ((responseIndex risingLoad < responseIndex intermediateLoad)
    × (responseIndex prolongedLoad < responseIndex intermediateLoad))
regimeShapeInherited = Kink.profile-shape sampledRegimeProfile

-- The original stress score is insufficient to infer a selected HPA
-- calibration regime: context and person-time dynamics remain independent.
data ModelCalibration : Set where
  elevatedPattern attenuatedPattern : ModelCalibration

data RegimeModel : Set where
  elevatedWorld attenuatedWorld : RegimeModel

sameNominalExposure : RegimeModel → Nat
sameNominalExposure _ = 5

regime : RegimeModel → ModelCalibration
regime elevatedWorld = elevatedPattern
regime attenuatedWorld = attenuatedPattern

sameExposureDifferentRegime :
  NF.NonFactorabilityWitness sameNominalExposure regime
sameExposureDifferentRegime =
  NF.nonFactorabilityWitness elevatedWorld attenuatedWorld refl (λ ())

exposureCannotDetermineHPARegime :
  NF.FactorsThrough sameNominalExposure regime → ⊥
exposureCannotDetermineHPARegime =
  NF.witnessRulesOutEveryFlatFactorisation
    sameExposureDifferentRegime

-- Do NOT equate 'blunted endocrine pattern' to exhaustion, trauma
-- diagnosis, vagal shutdown or an individual's subjective state.
data ProposedInterpretation : Set where
  attenuatedCortisolPattern livedEpistemicExhaustion : ProposedInterpretation

attenuationNotExhaustionByDefinition :
  attenuatedCortisolPattern ≡ livedEpistemicExhaustion → ⊥
attenuationNotExhaustionByDefinition ()
