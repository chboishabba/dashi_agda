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
--   a^2 b^4.
--
-- Under common amplitude rescaling a,b -> s a,s b this is degree six.  The
-- proposed shortcut from the continuation analysis,
--
--   weightedLocalMass <= C * criticalEnergy * dissipation,
--
-- would compare that degree-six quantity against a product of two quadratic
-- energies, hence degree four, with one amplitude-independent coefficient C.
--
-- The repository already contains the generic theorem that a positive cubic
-- quantity in an energy-amplitude variable cannot admit a fixed quadratic
-- majorant at every amplitude.  Here we instantiate it exactly with
--
--   z = amplitude^2,
--   W(z) = z^3,          -- physical degree six
--   X D(z) = z^2.       -- physical degree four
--
-- Thus *no fixed amplitude-independent constant* C can make W <= C X D
-- uniformly for arbitrary data.  This rejects the raw W<=XD shortcut before
-- any owner budget is tuned.  A successful HH-good route must retain another
-- quadratic resource, e.g. the data-controlled L2 energy, a time-localized
-- gain, or an equivalent physical amplitude factor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _≤_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:=_)

import DASHI.Physics.Closure.NSTriadKNCubicQuadraticUniformGapNoGo as NoGo

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
unitLocalMassPositive = NatP.s≤s NatP.z≤n

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
        (NatP.*-identityˡ (hhGoodDegreeFourCriticalDissipation z))
        (uniformBound z))
  where
  open import Relation.Binary.PropositionalEquality using (subst)

hhGoodRawLocalMassQuadraticProductNoGoClosed : Bool
hhGoodRawLocalMassQuadraticProductNoGoClosed = true

hhGoodNeedsAdditionalQuadraticResource : Bool
hhGoodNeedsAdditionalQuadraticResource = true

hhGoodRawLocalMassQuadraticProductNoGoClosedIsTrue :
  hhGoodRawLocalMassQuadraticProductNoGoClosed ≡ true
hhGoodRawLocalMassQuadraticProductNoGoClosedIsTrue = refl
