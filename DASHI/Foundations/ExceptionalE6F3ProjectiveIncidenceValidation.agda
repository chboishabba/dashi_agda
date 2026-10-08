module DASHI.Foundations.ExceptionalE6F3ProjectiveIncidenceValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.ExceptionalE6F3ProjectiveIncidenceExact as P

boundary = P.canonicalExceptionalE6F3ProjectiveIncidenceBoundary

primitiveProjectiveCount40 : P.primitiveProjectiveCount40 boundary ≡ true
primitiveProjectiveCount40 = refl

standardProjectiveCount40 : P.standardProjectiveCount40 boundary ≡ true
standardProjectiveCount40 = refl

projectiveTwoSidedRecognitionPaid : P.projectiveTwoSidedRecognitionPaid boundary ≡ true
projectiveTwoSidedRecognitionPaid = refl

incidenceOrthogonalityIntertwiningPaid : P.incidenceOrthogonalityIntertwiningPaid boundary ≡ true
incidenceOrthogonalityIntertwiningPaid = refl

rawT4PointGeometryIdentified : P.rawT4PointGeometryIdentified boundary ≡ false
rawT4PointGeometryIdentified = refl
