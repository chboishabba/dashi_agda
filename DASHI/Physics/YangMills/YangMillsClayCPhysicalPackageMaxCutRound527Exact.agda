{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact where

------------------------------------------------------------------------
-- GOAL-1 C / ROUND527: FOUR PHYSICAL SOURCE PACKAGES
--
-- R475 flattened nine source facts.  The underlying constructors show that
-- several of those facts are fields of ONE physical source object and should
-- not be scheduled as independent theorem projects.
--
-- Preferred C frontier:
--
--   C1  one MarkedCurvatureCompositeFamily:
--       same-family marked source data (including the Hilbert modulus)
--       + gauge/local semantics of its completed composites;
--
--   C2  one PhysicalOPERemainderSharedTail identity;
--
--   C3  one physical one-step OPE/AF recurrence identification;
--
--   C4  one DensityAnchoredCanonicalMetricStressLane:
--       canonical metric selected stress coordinate
--       + literal beta-density normalized source anchor.
--
-- From C4, finite stress insertion, source-native Cauchy modulus, marked
-- completion provenance and the literal-density cross-numerator statement are
-- compiler outputs.  R522 may additionally choose the terminal stress tensor
-- from the completed source, making the final Clay-stress equality definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.YangMillsPhysicalOPERemainderSharedTailRound442Exact as Remainder
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact as OPE
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as StressLane
import DASHI.Physics.YangMills.YangMillsSourceFirstStressChoiceRound522Exact as StressChoice
import DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Exact as CurvatureChoice

c1MarkedCurvatureFamilyLevel : ProofLevel
c1MarkedCurvatureFamilyLevel =
  Curvature.literalMarkedCurvatureCompositeSourceLevel

c2PhysicalRemainderSharedTailLevel : ProofLevel
c2PhysicalRemainderSharedTailLevel =
  Remainder.literalRound442PhysicalRemainderIsCompositeTailLevel

c3OneStepAFRecurrenceIdentificationLevel : ProofLevel
c3OneStepAFRecurrenceIdentificationLevel =
  OPE.physicalSameFamilyOPECoefficientOneStepAFIdentificationLevel

c4DensityAnchoredStressLaneLevel : ProofLevel
c4DensityAnchoredStressLaneLevel =
  StressLane.literalDensityAnchoredStressLaneInstantiationLevel

------------------------------------------------------------------------
-- Compiler-owned consequences after the four packages.
------------------------------------------------------------------------

c1NuclearCompletionLevel : ProofLevel
c1NuclearCompletionLevel =
  Curvature.markedCurvatureCompositeNuclearCompilerLevel

c2RemainderDecayLevel : ProofLevel
c2RemainderDecayLevel =
  Remainder.round442PhysicalOPERemainderCompilerLevel

c3AllDepthCoefficientMatchingLevel : ProofLevel
c3AllDepthCoefficientMatchingLevel =
  OPE.coefficientRGRecurrenceUniquenessLevel

c4FiniteMetricInsertionCompilerLevel : ProofLevel
c4FiniteMetricInsertionCompilerLevel =
  StressLane.densityAnchoredCanonicalMetricStressLaneCompilerLevel

c4LegacyPackageStillContainsOldYStressIdentification : Bool
c4LegacyPackageStillContainsOldYStressIdentification = true

c4SourceFirstTerminalMakesStressEqualityDefinitional : Bool
c4SourceFirstTerminalMakesStressEqualityDefinitional = true

c4PostHocRewriteOfExistingYAllowed : Bool
c4PostHocRewriteOfExistingYAllowed = false

round527CPhysicalPackageMaxCutCompilerLevel : ProofLevel
round527CPhysicalPackageMaxCutCompilerLevel = machineChecked

cPhysicalPackageCount : Nat
cPhysicalPackageCount = 4
