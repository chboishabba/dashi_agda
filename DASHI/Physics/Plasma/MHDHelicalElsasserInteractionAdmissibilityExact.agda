module DASHI.Physics.Plasma.MHDHelicalElsasserInteractionAdmissibilityExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Plasma.MHDHelicalElsasserTriadHypervoxelExact as V

------------------------------------------------------------------------
-- COUNTERPROPAGATING ADMISSIBILITY BEFORE COEFFICIENT EVALUATION
------------------------------------------------------------------------

data Opposite : V.BinarySign → V.BinarySign → Set where
  plusMinus : Opposite V.plus V.minus
  minusPlus : Opposite V.minus V.plus

record ElsasserNonlinearAdmissibility
    (advected advecting : V.BinarySign) : Set where
  constructor elsasser-nonlinear-admissibility
  field
    counterpropagating : Opposite advected advecting

open ElsasserNonlinearAdmissibility public

record AdmittedMHDTriadInteraction
    (voxel : V.MHDHelicalElsasserTriadHypervoxel) : Set₁ where
  constructor admitted-mhd-triad-interaction
  field
    AdvectedOrientation AdvectingOrientation : V.BinarySign
    orientationWeld : Set
    counterpropagatingReceipt :
      ElsasserNonlinearAdmissibility AdvectedOrientation AdvectingOrientation
    coefficientSameObjectReceipt : Set
    amplitudeSameObjectReceipt : Set

open AdmittedMHDTriadInteraction public

record InteractionAdmissionBoundary : Set where
  constructor interaction-admission-boundary
  field
    sameElsasserOrientationAutomaticallyInteractsNonlinearly : Bool
    sameElsasserOrientationAutomaticallyInteractsNonlinearlyIsFalse :
      sameElsasserOrientationAutomaticallyInteractsNonlinearly ≡ false

    helicityOppositionCanSubstituteForElsasserOpposition : Bool
    helicityOppositionCanSubstituteForElsasserOppositionIsFalse :
      helicityOppositionCanSubstituteForElsasserOpposition ≡ false

    coefficientMayBeUsedBeforeAdmission : Bool
    coefficientMayBeUsedBeforeAdmissionIsFalse :
      coefficientMayBeUsedBeforeAdmission ≡ false

canonicalInteractionAdmissionBoundary : InteractionAdmissionBoundary
canonicalInteractionAdmissionBoundary =
  interaction-admission-boundary false refl false refl false refl
