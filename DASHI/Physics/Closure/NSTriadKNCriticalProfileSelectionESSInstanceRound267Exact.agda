module DASHI.Physics.Closure.NSTriadKNCriticalProfileSelectionESSInstanceRound267Exact where

------------------------------------------------------------------------
-- ROUND267 / F + G*: CONDITIONAL COMPILER AND NO-PROMOTION BOUNDARY
--
-- IMPORTANT CORRECTION
-- Gallagher--Koch--Planchon construct critical elements for a minimal
-- singularity/global-regularity failure threshold.  Our first-hit/profile lane
-- starts from failure of a mixed-helicity spacetime budget. Those are not the
-- same badness predicate.
--
-- Likewise, Escauriaza--Seregin--Sverak backward uniqueness requires the
-- regularity/terminal-vanishing structure of the critical solution used in
-- their endpoint argument. A nonzero mixed defect does not by itself imply
-- terminal vorticity vanishing.
--
-- Therefore neither of these promotions is source-justified:
--
--   mixed-defect obstruction profile
--     => GKP minimal singular critical element,
--
--   mixed-defect critical profile
--     => ESS terminal-vanishing/backward-uniqueness hypotheses.
--
-- The record below remains useful as the exact CONDITIONAL compiler: if a new
-- theorem supplies those two bridges on the same selected profile, Round257
-- gives the contradiction mechanically.  The physical instances are
-- deliberately marked false.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNProfileDefectDecouplingCriticalElementRound256Exact as R256
import DASHI.Physics.Closure.NSTriadKNCriticalElementBackwardUniquenessRound257Exact as R257
import DASHI.Physics.Closure.NSTriadKNNonlinearProfileMixedDefectSourceRound261Exact as R261
import DASHI.Physics.Closure.NSTriadKNCriticalElementRigiditySourceRound262Exact as R262

record CriticalProfileSelectionESSInstance
    {ℓ : Level} (Profile : Set ℓ) : Set (lsuc ℓ) where
  field
    profileDecomposition : R256.DefectProfileDecomposition Profile
    mixedDefectProfileTheorem : R261.NonlinearMixedDefectProfileTheorem Profile

    -- OPEN F bridge: this must be a critical profile for the SAME mixed-defect
    -- badness criterion, not merely a GKP singularity-critical profile.
    selectedCriticalProfile : R256.SingleCriticalDefectProfile Profile

    -- OPEN G* bridge: ESS hypotheses must be proved for that SAME selected
    -- profile; they do not follow from nonzero mixed defect alone.
    essRigidity : R262.ESSCriticalElementRigidity Profile

    essElementIsSelectedProfile :
      R262.element essRigidity
      ≡ R256.criticalProfile selectedCriticalProfile

    zeroContradictsSelectedObstruction :
      R262.backwardUniquenessForcesZeroVorticity essRigidity →
      R262.nonzeroMixedDefectObstruction essRigidity → ⊥

open CriticalProfileSelectionESSInstance public

buildRound257RigidityAuthority :
  ∀ {ℓ} {Profile : Set ℓ} →
  (A : CriticalProfileSelectionESSInstance Profile) →
  R257.CriticalElementRigidityAuthority Profile
buildRound257RigidityAuthority A = record
  { R257.element = R262.element (essRigidity A)
  ; R257.compactModuloSymmetry =
      R262.compactnessModuloNSSymmetry (essRigidity A)
  ; R257.terminalVanishingOrDecay =
      R262.terminalVorticityVanishing (essRigidity A)
  ; R257.suitableOrStrongSolutionRegularity =
      R262.regularOnBackwardInterval (essRigidity A)
  ; R257.backwardUniquenessApplies =
      R262.coefficientsMeetESSBackwardUniquenessClass (essRigidity A)
  ; R257.backwardUniquenessForcesZero =
      R262.backwardUniquenessForcesZeroVorticity (essRigidity A)
  ; R257.obstructionNonzero =
      R262.nonzeroMixedDefectObstruction (essRigidity A)
  ; R257.zeroContradictsObstruction =
      zeroContradictsSelectedObstruction A
  }

criticalSelectedProfileImpossible :
  ∀ {ℓ} {Profile : Set ℓ} →
  CriticalProfileSelectionESSInstance Profile → ⊥
criticalSelectedProfileImpossible A =
  R257.criticalElementImpossible (buildRound257RigidityAuthority A)

round267ConditionalFGCompilerClosed : Bool
round267ConditionalFGCompilerClosed = true

round267MixedDefectBadnessAutomaticallyGivesGKPCriticalElement : Bool
round267MixedDefectBadnessAutomaticallyGivesGKPCriticalElement = false

round267MixedDefectCriticalProfileAutomaticallyMeetsESSHypotheses : Bool
round267MixedDefectCriticalProfileAutomaticallyMeetsESSHypotheses = false

round267PhysicalLeafFInstalled : Bool
round267PhysicalLeafFInstalled = false

round267PhysicalLeafGstarInstalled : Bool
round267PhysicalLeafGstarInstalled = false

round267PackageAClosed : Bool
round267PackageAClosed = false

round267ConditionalFGCompilerClosedIsTrue :
  round267ConditionalFGCompilerClosed ≡ true
round267ConditionalFGCompilerClosedIsTrue = refl

round267PhysicalLeafFInstalledIsFalse :
  round267PhysicalLeafFInstalled ≡ false
round267PhysicalLeafFInstalledIsFalse = refl

round267PhysicalLeafGstarInstalledIsFalse :
  round267PhysicalLeafGstarInstalled ≡ false
round267PhysicalLeafGstarInstalledIsFalse = refl
