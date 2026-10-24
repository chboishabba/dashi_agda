module DASHI.Physics.QFT.MMPDrivenRelativeWilsonCauchyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Wilson
import DASHI.Physics.QFT.MMPWilsonHadamardSameBackgroundBidiExact as Hadamard

------------------------------------------------------------------------
-- An actual finite, endpoint-indexed two-path specialization of the
-- preexisting DASHI Wilson group/path theorem. No fresh Wilson covariance
-- axiom, no parallel group algebra, and no physical Dirac state invented.
--
-- Original math/physics roots:
-- Wilson (1974) lattice holonomy, Sanders (2009/10) relative Cauchy
-- evolution of locally covariant free Dirac field, Zahn (2014, 2015)
-- charged background perturbation / renormalization.
-- The path here is an ALGEBRAIC relative evolution contour, not a
-- constructed globally hyperbolic 4D spacetime or spin-C propagator.
------------------------------------------------------------------------

data TimeBoundary : Set where
  initial final : TimeBoundary

data BackgroundStep : TimeBoundary → TimeBoundary → Set where
  undriven : BackgroundStep initial final
  driven : BackgroundStep initial final
  reverseUndriven : BackgroundStep final initial

timeField :
  ∀ {G : Set} →
  (H : Group.Group G) →
  (base source : G) →
  Wilson.GaugeField {G = G} BackgroundStep
timeField H base source .initial .final undriven = base
timeField H base source .initial .final driven = source
timeField H base source .final .initial reverseUndriven =
  Group.inverse H base

relativeContour : Wilson.Path BackgroundStep initial initial
relativeContour =
  Wilson._▷_ driven
    (Wilson._▷_ reverseUndriven Wilson.empty)

relativeWilson :
  ∀ {G : Set} →
  (H : Group.Group G) →
  (base source : G) → G
relativeWilson H base source =
  Wilson.holonomy H (timeField H base source) relativeContour

-- This exact reduction demonstrates a relative (driven versus reference)
-- evolution loop, with the reference segment oriented backwards.
relativeWilsonFactor :
  ∀ {G : Set} →
  (H : Group.Group G) →
  (base source : G) →
  relativeWilson H base source ≡
    Group.multiply H source (Group.inverse H base)
relativeWilsonFactor H base source =
  cong (Group.multiply H source)
    (Group.identityRight H (Group.inverse H base))

sameBackgroundRelativeIdentity :
  ∀ {G : Set} →
  (H : Group.Group G) →
  (base : G) →
  relativeWilson H base base ≡ Group.identity H
sameBackgroundRelativeIdentity H base =
  trans (relativeWilsonFactor H base base)
    (Group.inverseRight H base)

relativeWilsonGaugeCovariant :
  ∀ {G : Set} →
  (H : Group.Group G) →
  (gamma : Wilson.GaugeTransformation TimeBoundary G) →
  (base source : G) →
  Wilson.holonomy H
    (Wilson.gaugeAction H gamma (timeField H base source))
    relativeContour
  ≡
  Group.multiply H
    (Group.multiply H
      (gamma initial)
      (relativeWilson H base source))
    (Group.inverse H (gamma initial))
relativeWilsonGaugeCovariant H gamma base source =
  Wilson.holonomyGaugeCovariant
    H gamma (timeField H base source) relativeContour

-- Gauge-invariant relative LOOP values require a conjugation-invariant
-- function, not a bare non-Abelian matrix component.
relativeWilsonClassInvariant :
  ∀ {G Scalar : Set} →
  (H : Group.Group G) →
  (value : G → Scalar) →
  (classValue : Wilson.ClassFunction H value) →
  (gamma : Wilson.GaugeTransformation TimeBoundary G) →
  (base source : G) →
  Wilson.loopObservable H value
    (Wilson.gaugeAction H gamma (timeField H base source))
    relativeContour
  ≡
  Wilson.loopObservable H value
    (timeField H base source) relativeContour
relativeWilsonClassInvariant H value classValue gamma base source =
  Wilson.loopObservableGaugeInvariant H value classValue
    gamma (timeField H base source) relativeContour

-- The separately sourced smooth-state-difference AND residual-Cauchy
-- operators remain downstream conditions. This explicit source pointer
-- is non-inhabiting; it does not fill their physical analytic hypotheses.
existingHadamardWilsonDifferenceOwner : Set
existingHadamardWilsonDifferenceOwner =
  Hadamard.PhysicalPromotionBoundary
