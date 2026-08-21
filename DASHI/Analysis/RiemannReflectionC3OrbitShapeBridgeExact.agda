module DASHI.Analysis.RiemannReflectionC3OrbitShapeBridgeExact where

------------------------------------------------------------------------
-- SOURCE / ROLE BOUNDARY
--
-- The zeta-side analytic calibration is:
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026).
-- DOI: 10.48550/arXiv.2608.13637.
--
-- The C3 character-theory calibration is inherited from
-- DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact:
-- I. M. Isaacs, "Character Theory of Finite Groups" (no DOI assigned), and
-- Audrey Terras, "Fourier Analysis on Finite Groups and Applications",
-- DOI: 10.1017/CBO9780511626265.
--
-- This file proves only an ORBIT-SHAPE comparison:
--
--   C3:   identity fixed, zeta <-> zeta^2 = zeta^-1
--   zeta: critical centre fixed, left <-> right
--
-- It does not identify the Monster character, a McKay--Thompson series, the
-- Weil Hermitian form, or actual Riemann-zero displacements with one another.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.RiemannReflectionOrbitDefectExact as ZetaOrbit
import DASHI.Moonshine.MonsterC3CyclotomicEvaluationExact as C3

------------------------------------------------------------------------
-- Explicit three-phase orbit carrier and inversion.
------------------------------------------------------------------------

data C3Phase : Set where
  identityPhase zetaPhase zetaInversePhase : C3Phase

invertC3Phase : C3Phase → C3Phase
invertC3Phase identityPhase = identityPhase
invertC3Phase zetaPhase = zetaInversePhase
invertC3Phase zetaInversePhase = zetaPhase

invertC3PhaseInvolutive :
  (x : C3Phase) → invertC3Phase (invertC3Phase x) ≡ x
invertC3PhaseInvolutive identityPhase = refl
invertC3PhaseInvolutive zetaPhase = refl
invertC3PhaseInvolutive zetaInversePhase = refl

identityPhaseFixed : invertC3Phase identityPhase ≡ identityPhase
identityPhaseFixed = refl

zetaPhaseInversePartner : invertC3Phase zetaPhase ≡ zetaInversePhase
zetaPhaseInversePartner = refl

zetaInversePhasePartner : invertC3Phase zetaInversePhase ≡ zetaPhase
zetaInversePhasePartner = refl

------------------------------------------------------------------------
-- Tie the phase names to the already-certified cyclotomic values.
------------------------------------------------------------------------

phaseValue : C3Phase → C3.Cyclotomic3
phaseValue identityPhase = C3.oneC3
phaseValue zetaPhase = C3.zetaC3
phaseValue zetaInversePhase = C3.zetaSquaredC3

completePhaseOrbitValue : C3.Cyclotomic3
completePhaseOrbitValue =
  C3._+c3_ (C3._+c3_ (phaseValue identityPhase) (phaseValue zetaPhase))
            (phaseValue zetaInversePhase)

completePhaseOrbitCancels : completePhaseOrbitValue ≡ C3.zeroC3
completePhaseOrbitCancels = refl

------------------------------------------------------------------------
-- Common fixed-plus-inverse-pair role observer.
------------------------------------------------------------------------

data OrbitRole : Set where
  fixedRole inversePairRole : OrbitRole

c3OrbitRole : C3Phase → OrbitRole
c3OrbitRole identityPhase = fixedRole
c3OrbitRole zetaPhase = inversePairRole
c3OrbitRole zetaInversePhase = inversePairRole

zetaOrbitRole : ZetaOrbit.CentredReflectionState → OrbitRole
zetaOrbitRole ZetaOrbit.criticalCentre = fixedRole
zetaOrbitRole (ZetaOrbit.offLine _ _) = inversePairRole

c3OrbitRoleInversionInvariant :
  (x : C3Phase) → c3OrbitRole (invertC3Phase x) ≡ c3OrbitRole x
c3OrbitRoleInversionInvariant identityPhase = refl
c3OrbitRoleInversionInvariant zetaPhase = refl
c3OrbitRoleInversionInvariant zetaInversePhase = refl

zetaOrbitRoleReflectionInvariant :
  (x : ZetaOrbit.CentredReflectionState) →
  zetaOrbitRole (ZetaOrbit.reflect x) ≡ zetaOrbitRole x
zetaOrbitRoleReflectionInvariant ZetaOrbit.criticalCentre = refl
zetaOrbitRoleReflectionInvariant (ZetaOrbit.offLine ZetaOrbit.left n) = refl
zetaOrbitRoleReflectionInvariant (ZetaOrbit.offLine ZetaOrbit.right n) = refl

------------------------------------------------------------------------
-- Crucial asymmetry: C3's inverse quotient has one nontrivial orbit, whereas
-- the zeta model retains an unbounded magnitude coordinate after orientation
-- is forgotten.  The analogy therefore stops at the orbit-role layer.
------------------------------------------------------------------------

c3NontrivialPairHasSingleRole :
  c3OrbitRole zetaPhase ≡ c3OrbitRole zetaInversePhase
c3NontrivialPairHasSingleRole = refl

zetaSameRoleCanRetainDifferentDefects :
  zetaOrbitRole (ZetaOrbit.offLine ZetaOrbit.left 0)
    ≡ zetaOrbitRole (ZetaOrbit.offLine ZetaOrbit.right 2)
zetaSameRoleCanRetainDifferentDefects = refl

zetaFirstExampleDefect :
  ZetaOrbit.squaredDefect (ZetaOrbit.offLine ZetaOrbit.left 0) ≡ 1
zetaFirstExampleDefect = refl

zetaSecondExampleDefect :
  ZetaOrbit.squaredDefect (ZetaOrbit.offLine ZetaOrbit.right 2) ≡ 9
zetaSecondExampleDefect = refl

record C3ZetaOrbitShapeBoundary : Set where
  field
    commonFixedPlusInversePairShapeConstructed : Bool
    monsterRegularOrbitCancellationReused : Bool
    c3AndZetaCarriersIdentified : Bool
    monsterPhaseProvesRiemannZeroLocation : Bool
    cyclotomicCancellationIsWeilInertia : Bool

c3ZetaOrbitShapeBoundary : C3ZetaOrbitShapeBoundary
c3ZetaOrbitShapeBoundary = record
  { commonFixedPlusInversePairShapeConstructed = true
  ; monsterRegularOrbitCancellationReused = true
  ; c3AndZetaCarriersIdentified = false
  ; monsterPhaseProvesRiemannZeroLocation = false
  ; cyclotomicCancellationIsWeilInertia = false
  }
