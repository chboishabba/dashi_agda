module DASHI.Reasoning.TrialecticFiniteHypercover369CechCrosswalkValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticFiniteHypercover369CechCrosswalkExact as Cross

boundary : Cross.TrialecticFiniteHypercover369CechCrosswalkBoundary
boundary = Cross.canonicalTrialecticFiniteHypercover369CechCrosswalkBoundary

relationalFiniteHypersheafPaid :
  Cross.relationalFiniteOneTruncatedHypersheafPaid boundary ≡ true
relationalFiniteHypersheafPaid = refl

cubeSixFaces : Cross.cubeBoundarySixFacesPaid boundary ≡ true
cubeSixFaces = refl

cubeTwelveEdges : Cross.cubeBoundaryTwelveEdgesPaid boundary ≡ true
cubeTwelveEdges = refl

cubeEightCorners : Cross.cubeBoundaryEightCornersPaid boundary ≡ true
cubeEightCorners = refl

cubeInvertibleTransports : Cross.cubeInvertibleEdgeTransportPaid boundary ≡ true
cubeInvertibleTransports = refl

cubeCornerCocycle : Cross.cubeCornerCocyclePaid boundary ≡ true
cubeCornerCocycle = refl

sameObjectEquivalenceNotInferred :
  Cross.relationalAndCubeNervesIdentified boundary ≡ false
sameObjectEquivalenceNotInferred = refl

rankObstructionRetained : Cross.fullBoundaryRankObstructionRetained boundary ≡ true
rankObstructionRetained = refl
