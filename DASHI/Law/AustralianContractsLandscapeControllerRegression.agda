module DASHI.Law.AustralianContractsLandscapeControllerRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Law.AustralianContractsLegalFollowExact as Contracts
import DASHI.Law.AustralianContractsLandscapeControllerExact as Controller

boundaryExists : Set
boundaryExists =
  Controller.AustralianContractsLandscapeControllerBoundary

boundaryPaid : boundaryExists
boundaryPaid =
  Controller.canonicalAustralianContractsLandscapeControllerBoundary

fourFrontiersRemainSeparated :
  Controller.fourFrontiersAreSeparated
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
fourFrontiersRemainSeparated =
  Controller.fourFrontiersAreSeparatedIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

boundedSeedRemainsBounded :
  Controller.boundedSeedOnly
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ true
boundedSeedRemainsBounded =
  Controller.boundedSeedOnlyIsTrue
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

controllerStillCannotCreateCurrentLaw :
  Controller.controllerCreatesCurrentLawConclusion
    Controller.canonicalAustralianContractsLandscapeControllerBoundary
    ≡ false
controllerStillCannotCreateCurrentLaw =
  Controller.controllerCreatesCurrentLawConclusionIsFalse
    Controller.canonicalAustralianContractsLandscapeControllerBoundary

qldAsAtAxisStillCannotBeFlattened :
  NF.FactorsThrough
    Contracts.coarsePrivityProjection
    Contracts.operativePrivityRoute
  → ⊥
qldAsAtAxisStillCannotBeFlattened =
  Controller.qldTemporalAlternativeMustRemainRepresentable
