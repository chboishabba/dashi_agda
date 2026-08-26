module DASHI.Core.PressureQuadraticHealingExact where

------------------------------------------------------------------------
-- PRESSURE + CERTIFIED DEPENDENCY-GEOMETRY HEALING
--
-- PRIMARY CALIBRATION
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026.
-- DOI: 10.1145/3798129.3800762.
-- arXiv:2508.03961; DOI: 10.48550/arXiv.2508.03961.
--
-- REPOSITORY CONTEXT
--
-- `DASHI.Pressure` already owns the finite pressure lattice and
-- `SensibLawResidualLattice` already maps receipt-backed residual joins into
-- that lattice.  `ResidualObserverQuadraticControlExact` separately owns
-- comparison by a certified affine-spectral quadratic-domination factor.
--
-- DASHI CONTRIBUTION
--
-- Keep these two axes independent.  A candidate is no worse than another when
-- it is simultaneously no worse in immediate pressure AND no worse in its
-- certified residual dependency factor.  This is a Pareto/product preorder;
-- no arbitrary weighted scalarization is introduced.
--
-- Selection remains restricted to proof-bearing admissible actions whose
-- post-states preserve a required capability.  Via
-- `FutureLanguageQuadraticControlExact`, that capability may be an exact
-- consumer-visible future trace.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_)

import DASHI.Pressure as Pressure
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.ResidualObserverQuadraticControlExact as Quadratic
import DASHI.Core.TypedDependencyCore as Dependency

PressureScore : Set → Set → Set
PressureScore State Action = State → Action → Pressure.Pressure

NoWorsePressure :
  ∀ {State Action : Set} →
  PressureScore State Action → State → Action → Action → Set
NoWorsePressure pressure state preferred alternative =
  pressure state preferred Pressure.⊑p pressure state alternative

NoWorseHealing :
  ∀ {State Action Vector : Set} →
  PressureScore State Action →
  Quadratic.CertifiedQuadraticDependency State Action Vector →
  State → Action → Action → Set
NoWorseHealing pressure dependency state preferred alternative =
  NoWorsePressure pressure state preferred alternative
  × Quadratic.NoWorseAffineSpectralFactor
      dependency state preferred alternative

noWorseHealingRefl :
  ∀ {State Action Vector : Set}
    (pressure : PressureScore State Action)
    (dependency : Quadratic.CertifiedQuadraticDependency State Action Vector)
    state action →
  NoWorseHealing pressure dependency state action action
noWorseHealingRefl pressure dependency state action =
  Pressure.refl-⊑p
  , Quadratic.noWorseAffineSpectralFactorRefl dependency state action

noWorseHealingTrans :
  ∀ {State Action Vector : Set}
    {pressure : PressureScore State Action}
    {dependency : Quadratic.CertifiedQuadraticDependency State Action Vector}
    {state : State} {a b c : Action} →
  NoWorseHealing pressure dependency state a b →
  NoWorseHealing pressure dependency state b c →
  NoWorseHealing pressure dependency state a c
noWorseHealingTrans (pressureAB , dependencyAB) (pressureBC , dependencyBC) =
  Pressure.trans-⊑p pressureAB pressureBC
  , Quadratic.noWorseAffineSpectralFactorTrans dependencyAB dependencyBC

record LeastPressureQuadraticCapabilityPreservingChoice
    {State Action Vector : Set}
    (system : Dependency.DependentActionSystem State Action)
    (pressure : PressureScore State Action)
    (dependency : Quadratic.CertifiedQuadraticDependency State Action Vector)
    (capability : Residual.StateCapability State)
    (state : State) : Set₁ where
  field
    chosenAction : Action
    chosenAdmissible :
      Dependency.AdmissibleAction system state chosenAction
    chosenPreservesCapability :
      capability (Dependency.after chosenAdmissible)
    leastHealingAmongCapabilityPreserving :
      ∀ (alternative : Action) →
      (alternativeAdmissible :
        Dependency.AdmissibleAction system state alternative) →
      capability (Dependency.after alternativeAdmissible) →
      NoWorseHealing pressure dependency state chosenAction alternative

open LeastPressureQuadraticCapabilityPreservingChoice public

------------------------------------------------------------------------
-- Boundary:
--
-- This preorder does not assert that pressure and spectral factor are the only
-- relevant objectives, nor that every pair has a unique least element.  It
-- simply prevents a local candidate from being called uniformly better when it
-- improves one declared axis by worsening the other, or when it destroys the
-- required post-state capability.
------------------------------------------------------------------------
