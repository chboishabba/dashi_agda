module DASHI.Cognition.Teleodynamics.AlbertE6WeightRoleRegression where

import DASHI.Cognition.Teleodynamics.AlbertE6WeightRoleCorrectionExact as W

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

finiteFibreIsRepresentationSpaceIsFalse :
  W.finiteRootFibreIsAlbertRepresentationSpace W.canonicalRoleBoundary ≡ false
finiteFibreIsRepresentationSpaceIsFalse = refl

weightOrbitRecognitionIsCorrectTarget :
  W.e8MixedFibreTargetsWeightOrbit W.canonicalRoleBoundary ≡ true
weightOrbitRecognitionIsCorrectTarget = refl

fullF4StillOpen :
  W.fullF4ActionConstructed W.canonicalRoleBoundary ≡ false
fullF4StillOpen = refl

fullE6StillOpen :
  W.fullE6ActionConstructed W.canonicalRoleBoundary ≡ false
fullE6StillOpen = refl
