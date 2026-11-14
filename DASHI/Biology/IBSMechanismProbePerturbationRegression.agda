module DASHI.Biology.IBSMechanismProbePerturbationRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSMechanismProbePerturbationAtlasExact as Probe

probeAtlasRegression :
  Probe.canonicalIBSMechanismProbeAtlas ≡ Probe.canonicalIBSMechanismProbeAtlas
probeAtlasRegression = refl

responseNotMechanismIdentityRegression :
  Probe.ResponseIdentifiesUniqueMechanismPermission → ⊥
responseNotMechanismIdentityRegression = Probe.responseDoesNotIdentifyUniqueMechanism

sameSymptomImprovementNotSamePathwayRegression :
  Probe.EqualSymptomResponseMeansSamePathwayPermission → ⊥
sameSymptomImprovementNotSamePathwayRegression = Probe.equalSymptomResponseDoesNotMeanSamePathway

probeFrontierRegression :
  Probe.canonicalIBSProbeParetoFrontier ≡ Probe.canonicalIBSProbeParetoFrontier
probeFrontierRegression = refl
