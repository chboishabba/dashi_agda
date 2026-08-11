module DASHI.Physics.Closure.NSTriadKNHHGoodLocalMassScalingNoGoRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 38's literal HH-good local weight is
--
--   W(a,b) = a^2 b^4.
--
-- This file first proves that statement's *actual physical scaling* on the
-- repository's `PhysicalVorticityPair`: common amplitude rescaling
--
--   (a,b) -> (s a, s b)
--
-- multiplies the exact `amplitudeQuarticWeight` by
--
--   (s^2)^3 = s^6.
--
-- The proposed shortcut
--
--   W <= C * criticalEnergy * dissipation
--
-- would compare that degree-six quantity with a product of two quadratic
-- resources, hence degree four, using one amplitude-independent constant C.
-- The repository already has a general cubic-vs-quadratic scaling no-go.  We
-- instantiate it in the energy-amplitude variable z=s^2:
--
--   W(z)=z^3,       X D(z)=z^2.
--
-- Therefore no fixed amplitude-independent coefficient can make the raw
-- degree-six local mass uniformly bounded by the degree-four product for
-- arbitrary amplitude.  A successful HH-good route must retain one further
-- quadratic controlled resource (for example initial L2 energy), a genuine
-- time-localized gain, or another physically equivalent source of degree two.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:=_)
open import Data.Rational.Base using (ℚ)
import Data.Rational.Base as Rat
import Data.Rational.Tactic.RingSolver as RatRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact as Good
import DASHI.Physics.Closure.NSTriadKNCubicQuadraticUniformGapNoGo as NoGo

------------------------------------------------------------------------
-- Same-object scaling on the literal Round-38 physical amplitude weight.
------------------------------------------------------------------------

scalePhysicalPair :
  ℚ → Physical.PhysicalVorticityPair → Physical.PhysicalVorticityPair
scalePhysicalPair scalar pair =
  Physical.physical-vorticity-pair
    (Rat._*_ scalar (Physical.leftAmplitude pair))
    (Rat._*_ scalar (Physical.rightAmplitude pair))
    (Physical.directions pair)

literalAmplitudeWeightCommonScale :
  ∀ scalar pair →
  Good.amplitudeQuarticWeight (scalePhysicalPair scalar pair)
  ≡
  Rat._*_
    (Rat._*_
      (L2.square scalar)
      (L2.square scalar))
    (Rat._*_
      (L2.square scalar)
      (Good.amplitudeQuarticWeight pair))
literalAmplitudeWeightCommonScale scalar pair =
  RatRing.solve
    ( scalar
    ∷ Physical.leftAmplitude pair
    ∷ Physical.rightAmplitude pair
    ∷ [])

literalAmplitudeWeightHasDegreeSix : Bool
literalAmplitudeWeightHasDegreeSix = true

------------------------------------------------------------------------
-- Degree-six versus degree-four uniform-bound no-go.
------------------------------------------------------------------------

energyAmplitudeScale : Nat → Nat → Nat
energyAmplitudeScale factor z = factor * z

hhGoodDegreeSixLocalMass : Nat → Nat
hhGoodDegreeSixLocalMass z = z * z * z

hhGoodDegreeFourCriticalDissipation : Nat → Nat
hhGoodDegreeFourCriticalDissipation z = z * z

localMassCubicScaling : ∀ factor z →
  hhGoodDegreeSixLocalMass (energyAmplitudeScale factor z)
  ≡
  (factor * factor)
    * (factor * hhGoodDegreeSixLocalMass z)
localMassCubicScaling =
  solve 2
    (λ factor z →
      ((factor :* z) :* (factor :* z)) :* (factor :* z)
      :=
      (factor :* factor)
        :* (factor :* ((z :* z) :* z)))
    refl

criticalDissipationQuadraticScaling : ∀ factor z →
  hhGoodDegreeFourCriticalDissipation (energyAmplitudeScale factor z)
  ≡
  (factor * factor) * hhGoodDegreeFourCriticalDissipation z
criticalDissipationQuadraticScaling =
  solve 2
    (λ factor z →
      (factor :* z) :* (factor :* z)
      :=
      (factor :* factor) :* (z :* z))
    refl

hhGoodLocalMassScaling : NoGo.CubicQuadraticScaling Nat
hhGoodLocalMassScaling = record
  { scale = energyAmplitudeScale
  ; nonlinear = hhGoodDegreeSixLocalMass
  ; energy = hhGoodDegreeFourCriticalDissipation
  ; nonlinearCubic = localMassCubicScaling
  ; energyQuadratic = criticalDissipationQuadraticScaling
  }

unitLocalMassPositive :
  0 < hhGoodDegreeSixLocalMass 1
unitLocalMassPositive = s≤s z≤n

rawHHGoodLocalMassQuadraticProductRefuted :
  (constant : Nat) →
  (uniformBound :
    ∀ z →
    hhGoodDegreeSixLocalMass z
    ≤ constant * hhGoodDegreeFourCriticalDissipation z) →
  ⊥
rawHHGoodLocalMassQuadraticProductRefuted constant uniformBound =
  NoGo.positiveCubicWitnessRefutesUniformQuadraticBound
    hhGoodLocalMassScaling constant uniformBound 1 unitLocalMassPositive

rawUnitCoefficientShortcutRefuted :
  (uniformBound :
    ∀ z →
    hhGoodDegreeSixLocalMass z
    ≤ hhGoodDegreeFourCriticalDissipation z) →
  ⊥
rawUnitCoefficientShortcutRefuted uniformBound =
  rawHHGoodLocalMassQuadraticProductRefuted 1
    (λ z →
      subst
        (λ upper → hhGoodDegreeSixLocalMass z ≤ upper)
        (sym (NatP.*-identityˡ (hhGoodDegreeFourCriticalDissipation z)))
        (uniformBound z))

hhGoodRawLocalMassQuadraticProductNoGoClosed : Bool
hhGoodRawLocalMassQuadraticProductNoGoClosed = true

hhGoodNeedsAdditionalQuadraticResource : Bool
hhGoodNeedsAdditionalQuadraticResource = true

hhGoodRawLocalMassQuadraticProductNoGoClosedIsTrue :
  hhGoodRawLocalMassQuadraticProductNoGoClosed ≡ true
hhGoodRawLocalMassQuadraticProductNoGoClosedIsTrue = refl
