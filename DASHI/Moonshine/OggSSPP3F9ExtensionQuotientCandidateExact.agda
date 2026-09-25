module DASHI.Moonshine.OggSSPP3F9ExtensionQuotientCandidateExact where

------------------------------------------------------------------------
-- p=3 F9 EXTENSION-COORDINATE QUOTIENT CANDIDATE
--
-- DASHI CONTRIBUTION
--
-- The whole finite F9-shaped carrier has six Frobenius orbits and therefore
-- cannot be the arithmetic source for the two-orbit p=3 recognition target.
--
-- The existing exact map
--
--   (a,b) |-> b
--
-- quotients away the base-field coordinate and is C2/Frobenius-equivariant.
-- Its target is the three-state KernelTrit carrier:
--
--   0 fixed,
--   +/- paired.
--
-- This module packages that quotient as the smallest structurally complete
-- candidate for the p=3 marked source socket.  Every finite/action-groupoid
-- obligation is paid.  The ONE deliberately unpaid step is arithmetic/source
-- authority: no theorem here identifies this quotient with the actual marked
-- supersingular moduli object required by P3MarkedFrobeniusSource.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as F9
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Target
import DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact as Socket
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Quotient carrier and induced action are the exact extension coordinate.
------------------------------------------------------------------------

P3ExtensionQuotientState : Set
P3ExtensionQuotientState = Kernel.KernelTrit

quotientF9 :
  F9.F9Point ->
  P3ExtensionQuotientState
quotientF9 = F9.extensionCoordinate

quotientSection :
  P3ExtensionQuotientState ->
  F9.F9Point
quotientSection = F9.extensionCoordinateSurjective

quotientSectionRightInverse :
  (state : P3ExtensionQuotientState) ->
  quotientF9 (quotientSection state) ≡ state
quotientSectionRightInverse =
  F9.extensionCoordinateSurjectiveCorrect

quotientAction :
  Action.InvertibleSymmetryAction
    P3ExtensionQuotientState
    C2.C2
quotientAction =
  Target.constantC2Action

quotientMapEquivariant :
  (g : C2.C2) ->
  (state : F9.F9Point) ->
  quotientF9 (Action.act F9.f9FrobeniusAction g state)
  ≡
  Action.act quotientAction g (quotientF9 state)
quotientMapEquivariant =
  F9.extensionCoordinateEquivariant

------------------------------------------------------------------------
-- 2. Exact two-orbit presentation and stabilizer profile.
------------------------------------------------------------------------

quotientOrbits :
  Orbit.OrbitPresentation quotientAction
quotientOrbits =
  Target.constantTernaryOrbitPresentation

quotientZeroOrbit :
  Target.ConstantTernaryOrbit
quotientZeroOrbit =
  Target.zeroConstantOrbit

quotientNonzeroOrbit :
  Target.ConstantTernaryOrbit
quotientNonzeroOrbit =
  Target.nonzeroConstantOrbit

zeroRepresentativeFixedByFlip :
  Action.act quotientAction C2.flip
    (Orbit.representative quotientOrbits quotientZeroOrbit)
  ≡
  Orbit.representative quotientOrbits quotientZeroOrbit
zeroRepresentativeFixedByFlip = refl

nonzeroRepresentativeMovedByFlip :
  Action.act quotientAction C2.flip
    (Orbit.representative quotientOrbits quotientNonzeroOrbit)
  ≡
  Orbit.representative quotientOrbits quotientNonzeroOrbit
  ->
  ⊥
nonzeroRepresentativeMovedByFlip ()

------------------------------------------------------------------------
-- 3. Coarse-j surface required by the arithmetic socket.
------------------------------------------------------------------------

quotientCoarseJ :
  P3ExtensionQuotientState ->
  ⊤
quotientCoarseJ state = tt

quotientCoarseJConstant :
  (state : P3ExtensionQuotientState) ->
  quotientCoarseJ state ≡ tt
quotientCoarseJConstant state = refl

markedWitness :
  P3ExtensionQuotientState
markedWitness =
  Kernel.positiveTrit

markedWitnessMoves :
  Action.act quotientAction C2.flip markedWitness
  ≡ markedWitness
  ->
  ⊥
markedWitnessMoves ()

------------------------------------------------------------------------
-- 4. Structurally complete source candidate.
--
-- This mirrors every structural field of P3MarkedFrobeniusSource except the
-- source-authority assertion that the flip IS the actual arithmetic Frobenius.
------------------------------------------------------------------------

record P3StructuralSourceCandidate : Set₁ where
  constructor p3-structural-source-candidate
  field
    MarkedState : Set

    action :
      Action.InvertibleSymmetryAction MarkedState C2.C2

    candidateOrbits :
      Orbit.OrbitPresentation action

    coarseJ :
      MarkedState -> ⊤

    coarseJConstant :
      (state : MarkedState) ->
      coarseJ state ≡ tt

    witness : MarkedState

    flipMovesWitness :
      Action.act action C2.flip witness ≡ witness -> ⊥

    descendedFromF9ByEquivariantQuotient : Bool

open P3StructuralSourceCandidate public

canonicalP3ExtensionQuotientCandidate :
  P3StructuralSourceCandidate
canonicalP3ExtensionQuotientCandidate =
  p3-structural-source-candidate
    P3ExtensionQuotientState
    quotientAction
    quotientOrbits
    quotientCoarseJ
    quotientCoarseJConstant
    markedWitness
    markedWitnessMoves
    true

------------------------------------------------------------------------
-- 5. Promotion to the actual arithmetic socket requires an external/source
--    identification witness.  No constructor is supplied here.
------------------------------------------------------------------------

data P3ExtensionQuotientIsActualMarkedArithmeticFrobenius : Set where

promoteWithArithmeticIdentification :
  P3ExtensionQuotientIsActualMarkedArithmeticFrobenius ->
  Socket.P3MarkedFrobeniusSource
promoteWithArithmeticIdentification ()

data F9QuotientStructureAloneCreatesArithmeticAuthority : Set where

f9QuotientStructureDoesNotCreateArithmeticAuthority :
  F9QuotientStructureAloneCreatesArithmeticAuthority -> ⊥
f9QuotientStructureDoesNotCreateArithmeticAuthority ()

------------------------------------------------------------------------
-- 6. The quotient target itself already has full recognition to the current
--    p=3 369 residual target, definitionally at this intermediate level.
------------------------------------------------------------------------

quotientToResidualActionRecognition :
  Recognition.ActionRecognitionFunctor
    quotientAction
    Target.constantC2Action
quotientToResidualActionRecognition =
  Recognition.action-recognition-functor
    (λ state -> state)
    (λ g -> g)
    refl
    (λ g h -> refl)
    (λ g -> refl)
    (λ g state -> refl)

record P3F9ExtensionQuotientCandidateBoundary : Set where
  constructor p3-f9-extension-quotient-candidate-boundary
  field
    wholeF9SixOrbitNoGoReused : Bool
    extensionCoordinateQuotientSurjective : Bool
    quotientActionEquivariant : Bool
    quotientHasTwoOrbitPresentation : Bool
    zeroStabilizerEnhanced : Bool
    nonzeroRepresentativeMoved : Bool
    coarseJConstant : Bool
    markedWitnessMoved : Bool
    allStructuralSocketFieldsPaid : Bool
    actualArithmeticMarkedIdentificationPaid : Bool
    structureAlonePromotesArithmeticAuthority : Bool

canonicalP3F9ExtensionQuotientCandidateBoundary :
  P3F9ExtensionQuotientCandidateBoundary
canonicalP3F9ExtensionQuotientCandidateBoundary =
  p3-f9-extension-quotient-candidate-boundary
    true true true true true true true true true false false

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension
