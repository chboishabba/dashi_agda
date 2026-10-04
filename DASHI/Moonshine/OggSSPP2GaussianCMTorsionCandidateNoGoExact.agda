module DASHI.Moonshine.OggSSPP2GaussianCMTorsionCandidateNoGoExact where

------------------------------------------------------------------------
-- p=2 GAUSSIAN-CM TWO-TORSION SEED: CANDIDATE ELIMINATION
--
-- SOURCE / ATTRIBUTION
--
-- The concrete two-torsion carrier for E : y^2 = x^3 - x is owned by
-- EllipticCurveTwoTorsionAndBadPrimeExact, sourced to Silverman there.
--
-- DASHI contribution here:
--   compare that exact four-state C2 x C2 seed with the ten-component p=2
--   retained target and prove the finite capacity mismatch.
--
-- This does NOT reject Gaussian CM or level-4 arithmetic.  It proves only that
-- the existing four-state rational two-torsion seed is insufficient without
-- additional marked/dependent residual structure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact finite capacity comparison.
------------------------------------------------------------------------

twoTorsionSeedStateCount : Nat
twoTorsionSeedStateCount = 4

p2RetainedTargetComponentCount : Nat
p2RetainedTargetComponentCount = Target.p2RetainedPi0Count

twoTorsionSeedStateCountIsFour :
  twoTorsionSeedStateCount ≡ 4
twoTorsionSeedStateCountIsFour = refl

p2RetainedTargetComponentCountIsTen :
  p2RetainedTargetComponentCount ≡ 10
p2RetainedTargetComponentCountIsTen = refl

twoTorsionFourDoesNotEqualRetainedTen :
  twoTorsionSeedStateCount ≡ p2RetainedTargetComponentCount ->
  ⊥
twoTorsionFourDoesNotEqualRetainedTen ()

------------------------------------------------------------------------
-- 2. Exact seed is genuinely four-coded.
--
-- These four named points exhaust the repository's finite two-torsion seed.
------------------------------------------------------------------------

twoTorsionSeedWitness0 : Torsion.TwoTorsionCode
twoTorsionSeedWitness0 = Torsion.pointAtInfinityCode

twoTorsionSeedWitness1 : Torsion.TwoTorsionCode
twoTorsionSeedWitness1 = Torsion.pointZeroCode

twoTorsionSeedWitness2 : Torsion.TwoTorsionCode
twoTorsionSeedWitness2 = Torsion.pointOneCode

twoTorsionSeedWitness3 : Torsion.TwoTorsionCode
twoTorsionSeedWitness3 = Torsion.pointMinusOneCode

------------------------------------------------------------------------
-- 3. Promotion firewalls.
------------------------------------------------------------------------

data TwoTorsionSeedIsFullLevelFourMarkedCMSource : Set where
data FourStateCountCreatesTenComponentRecognition : Set where

twoTorsionSeedDoesNotBecomeFullMarkedCMSourceByNaming :
  TwoTorsionSeedIsFullLevelFourMarkedCMSource -> ⊥
twoTorsionSeedDoesNotBecomeFullMarkedCMSourceByNaming ()

fourStateCountDoesNotCreateTenComponentRecognition :
  FourStateCountCreatesTenComponentRecognition -> ⊥
fourStateCountDoesNotCreateTenComponentRecognition ()

------------------------------------------------------------------------
-- 4. Acquisition consequence.
--
-- Any viable p=2 marked CM source built over the concrete two-torsion seed
-- needs extra dependent marking/residual data.  The present file does not
-- manufacture that arithmetic marking.
------------------------------------------------------------------------

data AdditionalLevelFourMarkingRequired : Set where
  additionalLevelFourMarkingRequired : AdditionalLevelFourMarkingRequired

additionalLevelFourMarkingWitness :
  AdditionalLevelFourMarkingRequired
additionalLevelFourMarkingWitness =
  additionalLevelFourMarkingRequired

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2GaussianCMTorsionCandidateBoundary : Set where
  constructor p2-gaussian-cm-torsion-candidate-boundary
  field
    exactTwoTorsionSeedConsumed : Bool
    twoTorsionSeedHasFourFineCodes : Bool
    retainedTargetHasTenComponents : Bool
    fourEqualsTenRuledOut : Bool
    fourStateSeedSufficientAsFullMarkedCMSource : Bool
    additionalDependentMarkingRequired : Bool
    arithmeticLevelFourMarkingConstructedHere : Bool

canonicalP2GaussianCMTorsionCandidateBoundary :
  P2GaussianCMTorsionCandidateBoundary
canonicalP2GaussianCMTorsionCandidateBoundary =
  p2-gaussian-cm-torsion-candidate-boundary
    true true true true false true false
