module DASHI.Biology.IBSMonashAdaptiveSequencingRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSMonashAdaptiveSequencingExact as Monash

programmeAtlasRegression :
  Monash.canonicalMonashIBSProgrammeAtlas ≡ Monash.canonicalMonashIBSProgrammeAtlas
programmeAtlasRegression = refl

sequencingFrontierRegression :
  Monash.canonicalAdaptiveTreatmentSequencingFrontier ≡ Monash.canonicalAdaptiveTreatmentSequencingFrontier
sequencingFrontierRegression = refl

responseNotMechanismRegression :
  Monash.TreatmentResponseIdentifiesMechanismPermission → ⊥
responseNotMechanismRegression = Monash.treatmentResponseDoesNotIdentifyMechanism

informationNotBenefitRegression :
  Monash.InformationGainEqualsClinicalBenefitPermission → ⊥
informationNotBenefitRegression = Monash.informationGainDoesNotEqualClinicalBenefit

fodmapNotUniversalRegression :
  Monash.LowFODMAPResponseIdentifiesUniversalFODMAPMechanismPermission → ⊥
fodmapNotUniversalRegression = Monash.lowFODMAPResponseDoesNotIdentifyUniversalMechanism
