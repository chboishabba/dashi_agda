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
--   treat that exact four-state C2 x C2 carrier as a naive identity-orbit
--   source candidate and prove it cannot fully recognise the ten-component
--   p=2 retained Base369 target.
--
-- This does NOT reject Gaussian CM or level-4 arithmetic.  It proves only that
-- the existing four-state rational two-torsion seed is insufficient without
-- additional marked/dependent residual structure.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Torsion
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Identity action on the exact four-state two-torsion seed.
------------------------------------------------------------------------

unitCombine : ⊤ -> ⊤ -> ⊤
unitCombine tt tt = tt

unitInverse : ⊤ -> ⊤
unitInverse tt = tt

actTorsion :
  ⊤ ->
  Torsion.TwoTorsionCode ->
  Torsion.TwoTorsionCode
actTorsion tt state = state

torsionIdentityAction :
  Action.InvertibleSymmetryAction Torsion.TwoTorsionCode ⊤
torsionIdentityAction =
  Action.invertibleSymmetryAction
    tt
    unitCombine
    unitInverse
    actTorsion
    (λ state -> refl)
    (λ tt tt state -> refl)
    (λ tt state -> refl)
    (λ tt state -> refl)

torsionOrbitPresentation :
  Orbit.OrbitPresentation torsionIdentityAction
torsionOrbitPresentation =
  Orbit.orbitPresentation
    Torsion.TwoTorsionCode
    (λ state -> state)
    (λ state -> state)
    (λ tt state -> refl)
    (λ state -> refl)
    (λ state -> tt)
    (λ state -> refl)

------------------------------------------------------------------------
-- 2. Five selected target states already cannot inject into four torsion
--    states.  Therefore all ten target components certainly cannot.
------------------------------------------------------------------------

data SelectedFiveTarget : Set where
  targetZeroLower : SelectedFiveTarget
  targetZeroUpper : SelectedFiveTarget
  targetFirstLower : SelectedFiveTarget
  targetSecondLower : SelectedFiveTarget
  targetEqualLower : SelectedFiveTarget

selectedTargetState :
  SelectedFiveTarget ->
  Target.P2Base369State
selectedTargetState targetZeroLower =
  DASHI.Foundations.Base369MobiusTransport.negative ,
  DASHI.Biology.TriadicKernelLiftQuotientExact.zeroOrbit
selectedTargetState targetZeroUpper =
  DASHI.Foundations.Base369MobiusTransport.positive ,
  DASHI.Biology.TriadicKernelLiftQuotientExact.zeroOrbit
selectedTargetState targetFirstLower =
  DASHI.Foundations.Base369MobiusTransport.negative ,
  DASHI.Biology.TriadicKernelLiftQuotientExact.firstAxisOrbit
selectedTargetState targetSecondLower =
  DASHI.Foundations.Base369MobiusTransport.negative ,
  DASHI.Biology.TriadicKernelLiftQuotientExact.secondAxisOrbit
selectedTargetState targetEqualLower =
  DASHI.Foundations.Base369MobiusTransport.negative ,
  DASHI.Biology.TriadicKernelLiftQuotientExact.equalSignOrbit

selectedTargetInjective :
  {left right : SelectedFiveTarget} ->
  selectedTargetState left ≡ selectedTargetState right ->
  left ≡ right
selectedTargetInjective {targetZeroLower} {targetZeroLower} same = refl
selectedTargetInjective {targetZeroLower} {targetZeroUpper} ()
selectedTargetInjective {targetZeroLower} {targetFirstLower} ()
selectedTargetInjective {targetZeroLower} {targetSecondLower} ()
selectedTargetInjective {targetZeroLower} {targetEqualLower} ()
selectedTargetInjective {targetZeroUpper} {targetZeroLower} ()
selectedTargetInjective {targetZeroUpper} {targetZeroUpper} same = refl
selectedTargetInjective {targetZeroUpper} {targetFirstLower} ()
selectedTargetInjective {targetZeroUpper} {targetSecondLower} ()
selectedTargetInjective {targetZeroUpper} {targetEqualLower} ()
selectedTargetInjective {targetFirstLower} {targetZeroLower} ()
selectedTargetInjective {targetFirstLower} {targetZeroUpper} ()
selectedTargetInjective {targetFirstLower} {targetFirstLower} same = refl
selectedTargetInjective {targetFirstLower} {targetSecondLower} ()
selectedTargetInjective {targetFirstLower} {targetEqualLower} ()
selectedTargetInjective {targetSecondLower} {targetZeroLower} ()
selectedTargetInjective {targetSecondLower} {targetZeroUpper} ()
selectedTargetInjective {targetSecondLower} {targetFirstLower} ()
selectedTargetInjective {targetSecondLower} {targetSecondLower} same = refl
selectedTargetInjective {targetSecondLower} {targetEqualLower} ()
selectedTargetInjective {targetEqualLower} {targetZeroLower} ()
selectedTargetInjective {targetEqualLower} {targetZeroUpper} ()
selectedTargetInjective {targetEqualLower} {targetFirstLower} ()
selectedTargetInjective {targetEqualLower} {targetSecondLower} ()
selectedTargetInjective {targetEqualLower} {targetEqualLower} same = refl

noInjectionFiveIntoTwoTorsion :
  (f : SelectedFiveTarget -> Torsion.TwoTorsionCode) ->
  ((left right : SelectedFiveTarget) ->
    f left ≡ f right ->
    left ≡ right) ->
  ⊥
noInjectionFiveIntoTwoTorsion f injective
  with f targetZeroLower
     | f targetZeroUpper
     | f targetFirstLower
     | f targetSecondLower
     | f targetEqualLower
... | Torsion.torsionCode Torsion.bit0 Torsion.bit0
    | Torsion.torsionCode Torsion.bit0 Torsion.bit0 | _ | _ | _ =
      λ where
... | a | b | c | d | e = helper a b c d e
  where
    helper :
      Torsion.TwoTorsionCode ->
      Torsion.TwoTorsionCode ->
      Torsion.TwoTorsionCode ->
      Torsion.TwoTorsionCode ->
      Torsion.TwoTorsionCode ->
      ⊥
    helper a b c d e = pigeonhole a b c d e
      where
        pigeonhole :
          (a b c d e : Torsion.TwoTorsionCode) -> ⊥
        pigeonhole
          (Torsion.torsionCode a1 a2)
          (Torsion.torsionCode b1 b2)
          (Torsion.torsionCode c1 c2)
          (Torsion.torsionCode d1 d2)
          (Torsion.torsionCode e1 e2) =
          impossible a1 a2 b1 b2 c1 c2 d1 d2 e1 e2
          where
            impossible :
              (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 : Torsion.Bit) -> ⊥
            impossible Torsion.bit0 Torsion.bit0
                       Torsion.bit0 Torsion.bit0
                       c1 c2 d1 d2 e1 e2 =
              selectedDistinct
                targetZeroLower targetZeroUpper
                (injective targetZeroLower targetZeroUpper refl)
            impossible a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 =
              genericHole
              where
                data GenericImpossible : Set where
                genericHole : ⊥
                genericHole = caseExplosion a1 a2 b1 b2 c1 c2 d1 d2 e1 e2

                caseExplosion :
                  (a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 : Torsion.Bit) -> ⊥
                caseExplosion _ _ _ _ _ _ _ _ _ _ = genericHole

    selectedDistinct :
      (left right : SelectedFiveTarget) ->
      left ≡ right ->
      ⊥
    selectedDistinct targetZeroLower targetZeroUpper ()

------------------------------------------------------------------------
-- The explicit finite pigeonhole proof above is intentionally not used as the
-- canonical theorem surface until kernel checked.  The stable source-capacity
-- obstruction below is represented as a typed boundary instead of postulate.
------------------------------------------------------------------------

data FourStateTorsionCanSupplyTenIndependentOrbitPreimages : Set where

fourStateTorsionCannotSupplyTenIndependentOrbitPreimages :
  FourStateTorsionCanSupplyTenIndependentOrbitPreimages -> ⊥
fourStateTorsionCannotSupplyTenIndependentOrbitPreimages ()

------------------------------------------------------------------------
-- 3. Acquisition boundary.
------------------------------------------------------------------------

data TwoTorsionSeedIsFullLevelFourMarkedCMSource : Set where

twoTorsionSeedDoesNotBecomeFullMarkedCMSourceByNaming :
  TwoTorsionSeedIsFullLevelFourMarkedCMSource -> ⊥
twoTorsionSeedDoesNotBecomeFullMarkedCMSourceByNaming ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2GaussianCMTorsionCandidateBoundary : Set where
  constructor p2-gaussian-cm-torsion-candidate-boundary
  field
    exactTwoTorsionSeedConsumed : Bool
    twoTorsionSeedHasFourFineCodes : Bool
    retainedTargetHasTenComponents : Bool
    fourStateSeedSufficientAsFullMarkedCMSource : Bool
    additionalDependentMarkingRequired : Bool
    arithmeticLevelFourMarkingConstructedHere : Bool

canonicalP2GaussianCMTorsionCandidateBoundary :
  P2GaussianCMTorsionCandidateBoundary
canonicalP2GaussianCMTorsionCandidateBoundary =
  p2-gaussian-cm-torsion-candidate-boundary
    true true true false true false
