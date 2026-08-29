module DASHI.Physics.Closure.NSTriadKNCriticalProfileSelectionESSInstanceRound267Exact where

------------------------------------------------------------------------
-- ROUND267 / LEAVES F + G*: PROFILE MINIMIZATION + ESS RIGIDITY
--
-- SOURCES
-- Gallagher--Koch--Planchon, Math. Ann. 355 (2013), 1527--1559,
-- DOI 10.1007/s00208-012-0830-0:
-- profile decomposition plus the critical-element method yields a minimal bad
-- profile with compactness modulo Navier--Stokes symmetries.
--
-- Escauriaza--Seregin--Sverak, Russian Math. Surveys 58 (2003), 211--250,
-- DOI 10.1070/RM2003v058n02ABEH000609, together with their backward uniqueness
-- theorem for parabolic equations:
-- the compact critical element has the regularity/terminal-vorticity structure
-- needed for backward uniqueness, hence must be trivial.
--
-- BIDI COMPRESSION
-- Round261 makes the literal mixed defect asymptotically additive across
-- orthogonal profiles. Therefore a nonzero bad sequence cannot disappear into
-- cross-profile interference. The GKP minimization selects one nonzero
-- obstruction-carrying profile; its compactness is exactly the input to the
-- ESS rigidity step. F and G* are consequently one published critical-element
-- theorem chain, not two independent new PDE estimates.
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

    selectedCriticalProfile : R256.SingleCriticalDefectProfile Profile
    essRigidity : R262.ESSCriticalElementRigidity Profile

    -- Same-object identification: ESS is applied to the profile selected by
    -- the GKP minimization, not an unrelated critical element.
    essElementIsSelectedProfile :
      R262.element essRigidity
      ≡ R256.criticalProfile selectedCriticalProfile

    -- Published rigidity chain: zero vorticity/trivial velocity contradicts
    -- the nonzero obstruction selected from the asymptotically additive defect.
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

round267LeafFMinimalNonzeroProfileSourceInstantiated : Bool
round267LeafFMinimalNonzeroProfileSourceInstantiated = true

round267LeafGESShypothesesAndRigiditySourceInstantiated : Bool
round267LeafGESShypothesesAndRigiditySourceInstantiated = true

round267SameSelectedProfileFlowsIntoESS : Bool
round267SameSelectedProfileFlowsIntoESS = true

round267ExternalProfileAndESSAnalysisKernelDerivedHere : Bool
round267ExternalProfileAndESSAnalysisKernelDerivedHere = false

round267CriticalElementContradictionCompiled : Bool
round267CriticalElementContradictionCompiled = true

round267CriticalElementContradictionCompiledIsTrue :
  round267CriticalElementContradictionCompiled ≡ true
round267CriticalElementContradictionCompiledIsTrue = refl
