module DASHI.Physics.YangMills.YangMillsKleinNoetherGaugeInvariantBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Felix Klein,
-- "Vergleichende Betrachtungen über neuere geometrische Forschungen"
-- (the Erlangen Programme, 1872).  No DOI was assigned to the original.
--
-- Emmy Noether,
-- "Invariante Variationsprobleme" (1918).  No DOI was assigned to the
-- original.  M. A. Tavel translation:
-- DOI: 10.48550/arXiv.physics/0503066.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Reuse the generic Klein group-action surface to state gauge invariance
-- exactly: a rational action observable is constant on every witnessed gauge
-- orbit.  The downstream Noether/covariant-conservation data are represented
-- separately because ordinary orbit invariance does not by itself construct a
-- differentiable gauge group, a variational derivative, a covariant current,
-- the Bianchi identity, a Euclidean measure or a quantum Hamiltonian gap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact as K
import DASHI.Mathematics.Symmetry.NoetherDissipationDefectExact as N

record GaugeInvariantRationalAction : Set₁ where
  field
    gaugeAction : K.GroupAction
    actionFunctional : K.X gaugeAction → ℚ
    actionGaugeInvariant :
      K.Invariant gaugeAction actionFunctional

open GaugeInvariantRationalAction public

gaugeEquivalentConfigurationsHaveEqualAction :
  ∀ actionData {left right} →
  K.SameOrbit (gaugeAction actionData) left right →
  actionFunctional actionData right
  ≡ actionFunctional actionData left
gaugeEquivalentConfigurationsHaveEqualAction actionData =
  K.invariantOnOrbit
    (gaugeAction actionData)
    (actionFunctional actionData)
    (actionGaugeInvariant actionData)

record InfinitesimalGaugeNoetherSurface
    (actionData : GaugeInvariantRationalAction) : Set₁ where
  field
    differentiableGaugeParameters : Set
    fieldVariation : Set
    actionFirstVariation : Set
    currentCarrier : Set
    covariantDivergence : Set
    noetherIdentity : Set

record YangMillsCovariantConservationSurface : Set₁ where
  field
    connectionCarrier : Set
    curvatureCarrier : Set
    covariantExteriorDerivative : Set
    bianchiIdentity : Set
    yangMillsEulerLagrangeEquation : Set
    gaugeCovariantCurrentIdentity : Set

ordinaryAndCovariantConservationAreDistinct :
  N.ordinaryConservation ≡ N.covariantConservation → ⊥
ordinaryAndCovariantConservationAreDistinct ()

data YangMillsSymmetryStage : Set where
  finiteGaugeOrbitInvariance : YangMillsSymmetryStage
  infinitesimalNoetherIdentity : YangMillsSymmetryStage
  covariantBianchiIdentity : YangMillsSymmetryStage
  reflectionPositiveEuclideanMeasure : YangMillsSymmetryStage
  reconstructedHamiltonian : YangMillsSymmetryStage
  positiveMassGap : YangMillsSymmetryStage

finiteOrbitInvarianceIsNotNoetherDifferentiation :
  finiteGaugeOrbitInvariance ≡ infinitesimalNoetherIdentity → ⊥
finiteOrbitInvarianceIsNotNoetherDifferentiation ()

bianchiIdentityIsNotReflectionPositivity :
  covariantBianchiIdentity ≡ reflectionPositiveEuclideanMeasure → ⊥
bianchiIdentityIsNotReflectionPositivity ()

reconstructionIsNotPositiveGapByDefinition :
  reconstructedHamiltonian ≡ positiveMassGap → ⊥
reconstructionIsNotPositiveGapByDefinition ()

record KleinNoetherYangMillsBridge : Set₁ where
  field
    invariantFiniteAction : GaugeInvariantRationalAction
    infinitesimalNoetherSurface :
      InfinitesimalGaugeNoetherSurface invariantFiniteAction
    covariantConservationSurface :
      YangMillsCovariantConservationSurface

-- No field of KleinNoetherYangMillsBridge claims reflection positivity,
-- continuum reconstruction, nontriviality or a positive spectral gap.
