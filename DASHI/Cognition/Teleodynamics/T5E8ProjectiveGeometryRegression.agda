module DASHI.Cognition.Teleodynamics.T5E8ProjectiveGeometryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.T5E8ProjectiveGeometryBoundaryExact as B

projectiveCount120 :
  B.projectiveRelativeCount120 B.canonicalT5E8ProjectiveGeometryBoundary ≡ true
projectiveCount120 = refl

circulantForms27 :
  B.symmetricCirculantForms27 B.canonicalT5E8ProjectiveGeometryBoundary ≡ true
circulantForms27 = refl

candidateFound :
  B.e8Valency56CandidateFound B.canonicalT5E8ProjectiveGeometryBoundary ≡ false
candidateFound = refl

fullGeometry :
  B.fullE8GeometryRecognized B.canonicalT5E8ProjectiveGeometryBoundary ≡ false
fullGeometry = refl
