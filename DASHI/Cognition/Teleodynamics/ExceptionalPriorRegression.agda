module DASHI.Cognition.Teleodynamics.ExceptionalPriorRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior
import DASHI.Cognition.Teleodynamics.ExceptionalPriorFamilyExact as Exceptional

rootCountsAreCanonical :
  (Exceptional.rootCount Exceptional.g2RootPrior ≡ 12)
  × (Exceptional.rootCount Exceptional.f4RootPrior ≡ 48)
  × (Exceptional.rootCount Exceptional.e6RootPrior ≡ 72)
  × (Exceptional.rootCount Exceptional.e7RootPrior ≡ 126)
  × (Exceptional.rootCount Exceptional.e8RootPrior ≡ 240)
rootCountsAreCanonical = refl , refl , refl , refl , refl

ranksAreCanonical :
  (Exceptional.rootRank Exceptional.g2RootPrior ≡ 2)
  × (Exceptional.rootRank Exceptional.f4RootPrior ≡ 4)
  × (Exceptional.rootRank Exceptional.e6RootPrior ≡ 6)
  × (Exceptional.rootRank Exceptional.e7RootPrior ≡ 7)
  × (Exceptional.rootRank Exceptional.e8RootPrior ≡ 8)
ranksAreCanonical = refl , refl , refl , refl , refl

rankAndRepresentationDimensionAreSeparate :
  Exceptional.rootRank Exceptional.e6RootPrior ≡ 6
rankAndRepresentationDimensionAreSeparate = refl

codebookUseDoesNotCreateExceptionalAction :
  Prior.groupEquivarianceEstablished Prior.canonicalGeometricPriorBoundary ≡ false
codebookUseDoesNotCreateExceptionalAction = refl
