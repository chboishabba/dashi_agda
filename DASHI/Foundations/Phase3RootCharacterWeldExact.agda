module DASHI.Foundations.Phase3RootCharacterWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The supplied Tesla369 / PaletteCharacterTable development uses cyclic
-- character coordinates and roots of unity to diagonalize palette rotation.
-- This file does NOT claim source-parity with that later Lean snapshot.  It
-- welds that lesson to DASHI's already-existing Phase3 carrier instead of
-- inventing a second ternary phase datatype.
--
-- DASHI CONTRIBUTION
--
-- Phase3 is treated as the exponent carrier of {1,zeta,zeta^2}.  We prove:
--
--   * zeta^3 = 1 at the finite exponent level;
--   * conjugation/inversion swaps zeta and zeta^2;
--   * the three C3 characters are explicit and diagonalize rotation;
--   * the reflection satisfies s r s = r^-1;
--   * the resulting rotation/reflection actions are literally existing S3
--     permutations on TriTruth.
--
-- This is an exact finite character/root-of-unity model.  It is deliberately
-- not promoted to a complex Hilbert-space or Born-rule interpretation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3

phaseToTri : Phase.Phase3 → Base.TriTruth
phaseToTri Phase.phase0 = Base.tri-low
phaseToTri Phase.phase1 = Base.tri-mid
phaseToTri Phase.phase2 = Base.tri-high

triToPhase : Base.TriTruth → Phase.Phase3
triToPhase Base.tri-low = Phase.phase0
triToPhase Base.tri-mid = Phase.phase1
triToPhase Base.tri-high = Phase.phase2

phaseTriRoundTrip : (p : Phase.Phase3) → triToPhase (phaseToTri p) ≡ p
phaseTriRoundTrip Phase.phase0 = refl
phaseTriRoundTrip Phase.phase1 = refl
phaseTriRoundTrip Phase.phase2 = refl

triPhaseRoundTrip : (t : Base.TriTruth) → phaseToTri (triToPhase t) ≡ t
triPhaseRoundTrip Base.tri-low = refl
triPhaseRoundTrip Base.tri-mid = refl
triPhaseRoundTrip Base.tri-high = refl

phaseMul : Phase.Phase3 → Phase.Phase3 → Phase.Phase3
phaseMul left right = triToPhase (Base.triXor (phaseToTri left) (phaseToTri right))

phaseOne : Phase.Phase3
phaseOne = Phase.phase0

phaseZeta : Phase.Phase3
phaseZeta = Phase.phase1

phaseZetaSquared : Phase.Phase3
phaseZetaSquared = Phase.phase2

zetaSquaredTimesZetaIsOne : phaseMul phaseZetaSquared phaseZeta ≡ phaseOne
zetaSquaredTimesZetaIsOne = refl

zetaCubedIsOne : phaseMul phaseZeta (phaseMul phaseZeta phaseZeta) ≡ phaseOne
zetaCubedIsOne = refl

phaseInverse : Phase.Phase3 → Phase.Phase3
phaseInverse Phase.phase0 = Phase.phase0
phaseInverse Phase.phase1 = Phase.phase2
phaseInverse Phase.phase2 = Phase.phase1

phaseConjugate : Phase.Phase3 → Phase.Phase3
phaseConjugate = phaseInverse

zetaInverseIsZetaSquared : phaseInverse phaseZeta ≡ phaseZetaSquared
zetaInverseIsZetaSquared = refl

zetaSquaredInverseIsZeta : phaseInverse phaseZetaSquared ≡ phaseZeta
zetaSquaredInverseIsZeta = refl

conjugateInvolutive : (p : Phase.Phase3) → phaseConjugate (phaseConjugate p) ≡ p
conjugateInvolutive Phase.phase0 = refl
conjugateInvolutive Phase.phase1 = refl
conjugateInvolutive Phase.phase2 = refl

zetaRotate : Phase.Phase3 → Phase.Phase3
zetaRotate p = phaseMul phaseZeta p

zetaRotateIsExistingRotation : (p : Phase.Phase3) → zetaRotate p ≡ Phase.rotatePhase p
zetaRotateIsExistingRotation Phase.phase0 = refl
zetaRotateIsExistingRotation Phase.phase1 = refl
zetaRotateIsExistingRotation Phase.phase2 = refl

zetaRotateThree : (p : Phase.Phase3) → zetaRotate (zetaRotate (zetaRotate p)) ≡ p
zetaRotateThree Phase.phase0 = refl
zetaRotateThree Phase.phase1 = refl
zetaRotateThree Phase.phase2 = refl

character : Phase.Phase3 → Phase.Phase3 → Phase.Phase3
character Phase.phase0 g = Phase.phase0
character Phase.phase1 g = g
character Phase.phase2 g = phaseInverse g

characterRow : Phase.Phase3 → Phase.Phase3 × (Phase.Phase3 × Phase.Phase3)
characterRow k = character k Phase.phase0 , (character k Phase.phase1 , character k Phase.phase2)

characterRow0Exact : characterRow Phase.phase0 ≡ (Phase.phase0 , (Phase.phase0 , Phase.phase0))
characterRow0Exact = refl

characterRow1Exact : characterRow Phase.phase1 ≡ (Phase.phase0 , (Phase.phase1 , Phase.phase2))
characterRow1Exact = refl

characterRow2Exact : characterRow Phase.phase2 ≡ (Phase.phase0 , (Phase.phase2 , Phase.phase1))
characterRow2Exact = refl

characterPreservesPhaseMul :
  (k left right : Phase.Phase3) →
  character k (phaseMul left right) ≡ phaseMul (character k left) (character k right)
characterPreservesPhaseMul Phase.phase0 Phase.phase0 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase0 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase0 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase1 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase1 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase1 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase2 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase2 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase0 Phase.phase2 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase0 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase0 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase0 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase1 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase1 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase1 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase2 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase2 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase1 Phase.phase2 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase0 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase0 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase0 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase1 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase1 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase1 Phase.phase2 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase2 Phase.phase0 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase2 Phase.phase1 = refl
characterPreservesPhaseMul Phase.phase2 Phase.phase2 Phase.phase2 = refl

characterDiagonalizesRotation :
  (k g : Phase.Phase3) → character k (zetaRotate g) ≡ phaseMul k (character k g)
characterDiagonalizesRotation Phase.phase0 Phase.phase0 = refl
characterDiagonalizesRotation Phase.phase0 Phase.phase1 = refl
characterDiagonalizesRotation Phase.phase0 Phase.phase2 = refl
characterDiagonalizesRotation Phase.phase1 Phase.phase0 = refl
characterDiagonalizesRotation Phase.phase1 Phase.phase1 = refl
characterDiagonalizesRotation Phase.phase1 Phase.phase2 = refl
characterDiagonalizesRotation Phase.phase2 Phase.phase0 = refl
characterDiagonalizesRotation Phase.phase2 Phase.phase1 = refl
characterDiagonalizesRotation Phase.phase2 Phase.phase2 = refl

zetaRotateInverse : Phase.Phase3 → Phase.Phase3
zetaRotateInverse p = phaseMul phaseZetaSquared p

conjugateRotateConjugateIsInverse :
  (p : Phase.Phase3) → phaseConjugate (zetaRotate (phaseConjugate p)) ≡ zetaRotateInverse p
conjugateRotateConjugateIsInverse Phase.phase0 = refl
conjugateRotateConjugateIsInverse Phase.phase1 = refl
conjugateRotateConjugateIsInverse Phase.phase2 = refl

phaseRotationPermutation : Phase.Phase3 → S3.TriPermutation
phaseRotationPermutation Phase.phase0 = S3.permIdentity
phaseRotationPermutation Phase.phase1 = S3.permRotate
phaseRotationPermutation Phase.phase2 = S3.permRotate2

phaseReflectionPermutation : S3.TriPermutation
phaseReflectionPermutation = S3.permSwapMidHigh

rotationPermutationMatchesPhase :
  (rotation p : Phase.Phase3) →
  S3.applyPermutation (phaseRotationPermutation rotation) (phaseToTri p)
  ≡ phaseToTri (phaseMul rotation p)
rotationPermutationMatchesPhase Phase.phase0 Phase.phase0 = refl
rotationPermutationMatchesPhase Phase.phase0 Phase.phase1 = refl
rotationPermutationMatchesPhase Phase.phase0 Phase.phase2 = refl
rotationPermutationMatchesPhase Phase.phase1 Phase.phase0 = refl
rotationPermutationMatchesPhase Phase.phase1 Phase.phase1 = refl
rotationPermutationMatchesPhase Phase.phase1 Phase.phase2 = refl
rotationPermutationMatchesPhase Phase.phase2 Phase.phase0 = refl
rotationPermutationMatchesPhase Phase.phase2 Phase.phase1 = refl
rotationPermutationMatchesPhase Phase.phase2 Phase.phase2 = refl

reflectionPermutationMatchesConjugation :
  (p : Phase.Phase3) →
  S3.applyPermutation phaseReflectionPermutation (phaseToTri p) ≡ phaseToTri (phaseConjugate p)
reflectionPermutationMatchesConjugation Phase.phase0 = refl
reflectionPermutationMatchesConjugation Phase.phase1 = refl
reflectionPermutationMatchesConjugation Phase.phase2 = refl

record Phase3RootCharacterBoundary : Set where
  field
    existingPhaseCarrierReused : Bool
    cubicRootRelationsExact : Bool
    characterTableExact : Bool
    rotationDiagonalized : Bool
    reflectionIsExistingS3Permutation : Bool
    complexAnalyticRealizationConstructed : Bool
    hilbertOrBornInterpretationClaimed : Bool

canonicalPhase3RootCharacterBoundary : Phase3RootCharacterBoundary
canonicalPhase3RootCharacterBoundary = record
  { existingPhaseCarrierReused = true
  ; cubicRootRelationsExact = true
  ; characterTableExact = true
  ; rotationDiagonalized = true
  ; reflectionIsExistingS3Permutation = true
  ; complexAnalyticRealizationConstructed = false
  ; hilbertOrBornInterpretationClaimed = false
  }
