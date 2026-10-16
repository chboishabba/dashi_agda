module DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Moonshine.OggSSPClimbingGymDirichletPhaseExact as Target

validationTwentyPrimeChannels : Target.combinedPrimeCount ≡ 20
validationTwentyPrimeChannels = refl

validationDiscoveryWindowSize : Target.discoveryZeroCount ≡ 849
validationDiscoveryWindowSize = refl

validationHeldOutWindowSize : Target.heldOutZeroCount ≡ 849
validationHeldOutWindowSize = refl

validationResidualNotExactFiniteFormula :
  Target.landauMainTermClaimedExactFiniteFormula
    Target.canonicalDirichletPhaseBoundary
  ≡ false
validationResidualNotExactFiniteFormula = refl

validationHeldOutDoesNotPromoteMonster :
  Target.heldOutReplicatedMonsterSpecificAnomaly
    Target.canonicalDirichletPhaseBoundary
  ≡ false
validationHeldOutDoesNotPromoteMonster = refl

validationExplicitFormulaPriorArtAttributed :
  Target.landauGonekPriorArtAttributed
    Target.canonicalDirichletPhaseBoundary
  ≡ true
validationExplicitFormulaPriorArtAttributed = refl
