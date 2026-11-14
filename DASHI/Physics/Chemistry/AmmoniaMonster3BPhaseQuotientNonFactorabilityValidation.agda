module DASHI.Physics.Chemistry.AmmoniaMonster3BPhaseQuotientNonFactorabilityValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaMonster3BPhaseQuotientNonFactorabilityExact as N
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as M

samePhaseDifferentWeight :
  N.modelPhase N.weightState0 ≡ N.modelPhase N.weightState1
samePhaseDifferentWeight = refl

samePhaseDifferentMultiplicity :
  N.modelPhase N.multiplicityState0 ≡ N.modelPhase N.multiplicityState1
samePhaseDifferentMultiplicity = refl

allWitnessesAreZeta :
  N.modelPhase N.weightState0 ≡ M.phaseZeta
allWitnessesAreZeta = refl

phaseDoesNotRecoverFineState :
  N.PhaseRecoversModelBasis → ⊥
phaseDoesNotRecoverFineState = N.phaseCannotRecoverModelBasis

phaseDoesNotRecoverWeight :
  N.PhaseRecoversWeightPosition → ⊥
phaseDoesNotRecoverWeight = N.phaseCannotRecoverWeightPosition

phaseDoesNotRecoverMultiplicity :
  N.PhaseRecoversMultiplicityCoordinate → ⊥
phaseDoesNotRecoverMultiplicity = N.phaseCannotRecoverMultiplicityCoordinate

boundaryPaid :
  N.PhaseQuotientNonFactorabilityBoundary.phaseQuotientFineStateNonfactorabilityPaid
    N.canonicalPhaseQuotientNonFactorabilityBoundary ≡ true
boundaryPaid = refl
