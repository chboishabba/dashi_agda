module DASHI.Physics.ThreeBody.EisensteinC3FourierExact where

------------------------------------------------------------------------
-- THREE-BODY C3 FOURIER DECOMPOSITION ON THE EXACT EISENSTEIN PLANE
--
-- Three labelled planar positions are represented on the repository's exact
-- rational Eisenstein plane.  The cyclic relabelling
--
--   (r1,r2,r3) |-> (r3,r1,r2)
--
-- has order three.  Its discrete Fourier coordinates are
--
--   F0 = r1 + r2 + r3
--   F1 = r1 + omega r2 + omega^2 r3
--   F2 = r1 + omega^2 r2 + omega r3.
--
-- The exact theorem is the expected C3 diagonalisation:
--
--   F0(C r) = F0(r)
--   F1(C r) = omega   F1(r)
--   F2(C r) = omega^2 F2(r).
--
-- This pays the finite symmetry/Fourier weld behind the repository's earlier
-- figure-eight/Z3 analogy.  It does NOT identify this rational lattice carrier
-- with the full continuous Newtonian three-body phase space, prove Jacobi
-- coordinate completeness, construct the shape sphere, or solve/integrate the
-- three-body equations of motion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (trans)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Biology.EisensteinNineRingInterferenceExact as E

record PlanarThreeBodyState : Set where
  constructor planarThreeBodyState
  field
    r1 r2 r3 : E.Eisenstein

open PlanarThreeBodyState public

cyclicPermute : PlanarThreeBodyState → PlanarThreeBodyState
cyclicPermute (planarThreeBodyState first second third) =
  planarThreeBodyState third first second

cyclicPermuteThree :
  (state : PlanarThreeBodyState) →
  cyclicPermute (cyclicPermute (cyclicPermute state)) ≡ state
cyclicPermuteThree (planarThreeBodyState first second third) = refl

------------------------------------------------------------------------
-- Exact DFT modes.
------------------------------------------------------------------------

mode0 : PlanarThreeBodyState → E.Eisenstein
mode0 state = E.add (r1 state) (E.add (r2 state) (r3 state))

mode1 : PlanarThreeBodyState → E.Eisenstein
mode1 state =
  E.add
    (r1 state)
    (E.add
      (E.multiply E.omega (r2 state))
      (E.multiply E.omegaSquared (r3 state)))

mode2 : PlanarThreeBodyState → E.Eisenstein
mode2 state =
  E.add
    (r1 state)
    (E.add
      (E.multiply E.omegaSquared (r2 state))
      (E.multiply E.omega (r3 state)))

eisensteinExt :
  ∀ {left right : E.Eisenstein} →
  E.realCoordinate left ≡ E.realCoordinate right →
  E.omegaCoordinate left ≡ E.omegaCoordinate right →
  left ≡ right
eisensteinExt {E.eisenstein _ _} {E.eisenstein _ _} refl refl = refl

------------------------------------------------------------------------
-- Component expansion lemmas.  Using the existing exact multiplication law
-- makes the Fourier eigenvalue theorem independent of floating-point roots of
-- unity or trigonometric identities.
------------------------------------------------------------------------

mode0CyclicInvariant :
  (state : PlanarThreeBodyState) →
  mode0 (cyclicPermute state) ≡ mode0 state
mode0CyclicInvariant
    (planarThreeBodyState
      (E.eisenstein a ao)
      (E.eisenstein b bo)
      (E.eisenstein c co)) =
  eisensteinExt
    (ℚRing.solve-∀ a b c)
    (ℚRing.solve-∀ ao bo co)

mode1CyclicEigen :
  (state : PlanarThreeBodyState) →
  mode1 (cyclicPermute state)
  ≡ E.multiply E.omega (mode1 state)
mode1CyclicEigen
    (planarThreeBodyState
      (E.eisenstein a ao)
      (E.eisenstein b bo)
      (E.eisenstein c co)) =
  eisensteinExt
    (ℚRing.solve-∀ a ao b bo c co)
    (ℚRing.solve-∀ a ao b bo c co)

mode2CyclicEigen :
  (state : PlanarThreeBodyState) →
  mode2 (cyclicPermute state)
  ≡ E.multiply E.omegaSquared (mode2 state)
mode2CyclicEigen
    (planarThreeBodyState
      (E.eisenstein a ao)
      (E.eisenstein b bo)
      (E.eisenstein c co)) =
  eisensteinExt
    (ℚRing.solve-∀ a ao b bo c co)
    (ℚRing.solve-∀ a ao b bo c co)

------------------------------------------------------------------------
-- Centre-of-mass / relative-mode split on the selected exact carrier.
------------------------------------------------------------------------

eisensteinZero : E.Eisenstein
eisensteinZero = E.eisenstein 0ℚ 0ℚ

CenterOfMassZero : PlanarThreeBodyState → Set
CenterOfMassZero state = mode0 state ≡ eisensteinZero

cyclicPreservesCenterOfMassZero :
  ∀ {state} →
  CenterOfMassZero state →
  CenterOfMassZero (cyclicPermute state)
cyclicPreservesCenterOfMassZero {state} centered =
  trans (mode0CyclicInvariant state) centered

------------------------------------------------------------------------
-- Concrete regression state built only from already-owned phases.
------------------------------------------------------------------------

sampleState : PlanarThreeBodyState
sampleState = planarThreeBodyState E.one E.omega E.omegaSquared

sampleStateMode1 : E.Eisenstein
sampleStateMode1 = mode1 sampleState

sampleStateMode2 : E.Eisenstein
sampleStateMode2 = mode2 sampleState

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data DiscreteCarrierIsFullNewtonianThreeBodyPhaseSpace : Set where

data C3DiagonalisationSolvesThreeBodyDynamics : Set where

data FourierChiralModeIsAutomaticallyShapeSphereOrientation : Set where

noDiscreteCarrierPromotion :
  DiscreteCarrierIsFullNewtonianThreeBodyPhaseSpace → ⊥
noDiscreteCarrierPromotion ()

noDynamicsSolutionFromDiagonalisation :
  C3DiagonalisationSolvesThreeBodyDynamics → ⊥
noDynamicsSolutionFromDiagonalisation ()

noAutomaticShapeSphereIdentification :
  FourierChiralModeIsAutomaticallyShapeSphereOrientation → ⊥
noAutomaticShapeSphereIdentification ()
