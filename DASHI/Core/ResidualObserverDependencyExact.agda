module DASHI.Core.ResidualObserverDependencyExact where

------------------------------------------------------------------------
-- RESIDUAL OBSERVER DEPENDENCY / DECOUPLING CORE
--
-- This module is deliberately a seam between existing DASHI machinery rather
-- than a parallel discrepancy framework.  ObserverRefinementLatticeExact owns
-- fibres and strict refinement; TypedDependencyCore owns proof-bearing
-- state/action admissibility.  Here we add only the information that was
-- missing between them: an action-indexed observation of residual coupling,
-- together with a minimal preorder for comparing admissible moves by how much
-- residual coupling they leave behind.
--
-- The motivating discrepancy-theory calibration is the Bansal--Jiang use of
-- affine spectral-independence constraints to decouple discrepancy evolution
-- across rows during an SDP-guided discrete Brownian rounding process.  Nothing
-- below claims their spectral theorem, Komlos bound, Brownian analysis, or SDP.
-- It extracts the reusable theorem shape: current coarse observation need not
-- determine future coupling geometry, so dependency data can be a strict
-- observer refinement and can legitimately participate in action selection.
--
-- Sources / calibration:
--
-- Nikhil Bansal, "Constructive Algorithms for Discrepancy Minimization",
-- FOCS 2010, DOI 10.1109/FOCS.2010.7.
--
-- Wojciech Banaszczyk, "Balancing vectors and Gaussian measures of
-- n-dimensional convex bodies", Random Structures & Algorithms 12(4), 1998,
-- DOI 10.1002/(SICI)1098-2418(199807)12:4<351::AID-RSA3>3.0.CO;2-S.
--
-- Nikhil Bansal and Haotian Jiang,
-- "Decoupling via Affine Spectral-Independence: Beck-Fiala and Komlos Bounds
-- Beyond Banaszczyk", STOC 2026, DOI 10.1145/3798129.3800762;
-- arXiv:2508.03961, DOI 10.48550/arXiv.2508.03961.
--
-- Boundary: a finite dependency code or coupling score is not automatically a
-- covariance matrix, Gram operator, spectral-independence constant, or
-- semidefinite certificate.  Existing DASHI Gram/operator modules may later
-- instantiate this seam when the required linear-algebraic carrier is present.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Action-indexed residual dependency observation.
------------------------------------------------------------------------

record ResidualDependencyObserver
    (State Action Index Code : Set) : Set₁ where
  field
    Influences : State → Action → Index → Index → Set
    dependencyCode : State → Action → Code

open ResidualDependencyObserver public

residualDependencyAt :
  ∀ {State Action Index Code : Set} →
  ResidualDependencyObserver State Action Index Code →
  Action →
  Observer.Observer State Code
residualDependencyAt dependency action state =
  dependencyCode dependency state action

refinedObservationAt :
  ∀ {State Action Index Code Coarse : Set} →
  ResidualDependencyObserver State Action Index Code →
  Observer.Observer State Coarse →
  Action →
  Observer.Observer State (Coarse × Code)
refinedObservationAt dependency coarse action =
  Observer.pairObserver coarse (residualDependencyAt dependency action)

refinedObservationRefinesCoarse :
  ∀ {State Action Index Code Coarse : Set}
    (dependency : ResidualDependencyObserver State Action Index Code)
    (coarse : Observer.Observer State Coarse)
    (action : Action) →
  Observer.Refines coarse (refinedObservationAt dependency coarse action)
refinedObservationRefinesCoarse dependency coarse action =
  Observer.pairRefinesLeft coarse (residualDependencyAt dependency action)

------------------------------------------------------------------------
-- Exact witness that present observation has quotiented away action-relevant
-- dependency geometry.
------------------------------------------------------------------------

record HiddenResidualDependency
    {State Action Index Code Coarse : Set}
    (dependency : ResidualDependencyObserver State Action Index Code)
    (coarse : Observer.Observer State Coarse)
    (action : Action) : Set where
  constructor hiddenResidualDependency
  field
    left right : State
    sameCoarseObservation : coarse left ≡ coarse right
    dependencyCodeSeparates :
      dependencyCode dependency left action ≡
      dependencyCode dependency right action →
      ⊥

open HiddenResidualDependency public

hiddenResidualDependencyGivesStrictRefinement :
  ∀ {State Action Index Code Coarse : Set}
    {dependency : ResidualDependencyObserver State Action Index Code}
    {coarse : Observer.Observer State Coarse}
    {action : Action} →
  HiddenResidualDependency dependency coarse action →
  Observer.StrictRefinement
    coarse
    (refinedObservationAt dependency coarse action)
hiddenResidualDependencyGivesStrictRefinement witness =
  Observer.strictPairRefinement
    _ _
    (left witness)
    (right witness)
    (sameCoarseObservation witness)
    (dependencyCodeSeparates witness)

------------------------------------------------------------------------
-- Non-factorability, in the same exact style as other DASHI observer bridges.
------------------------------------------------------------------------

DependencyCodeDescendsAt :
  ∀ {State Action Index Code Coarse : Set} →
  ResidualDependencyObserver State Action Index Code →
  Observer.Observer State Coarse →
  Action →
  Set
DependencyCodeDescendsAt {State} {Code = Code} {Coarse = Coarse}
    dependency coarse action =
  Σ (Coarse → Code)
    (λ reconstruct →
      ∀ state →
      reconstruct (coarse state) ≡
      dependencyCode dependency state action)

hiddenResidualDependencyBlocksDescent :
  ∀ {State Action Index Code Coarse : Set}
    {dependency : ResidualDependencyObserver State Action Index Code}
    {coarse : Observer.Observer State Coarse}
    {action : Action} →
  HiddenResidualDependency dependency coarse action →
  DependencyCodeDescendsAt dependency coarse action →
  ⊥
hiddenResidualDependencyBlocksDescent witness descent =
  dependencyCodeSeparates witness
    (trans
      (sym (commutes (left witness)))
      (trans
        (cong reconstruct (sameCoarseObservation witness))
        (commutes (right witness))))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

------------------------------------------------------------------------
-- Quantitative seam.
------------------------------------------------------------------------

CouplingScore : Set → Set → Set
CouplingScore State Action = State → Action → Nat

NoWorseCoupled :
  ∀ {State Action : Set} →
  CouplingScore State Action → State → Action → Action → Set
NoWorseCoupled score state preferred alternative =
  score state preferred ≤ score state alternative

noWorseCoupledRefl :
  ∀ {State Action : Set}
    (score : CouplingScore State Action)
    (state : State)
    (action : Action) →
  NoWorseCoupled score state action action
noWorseCoupledRefl score state action = ≤-refl

noWorseCoupledTrans :
  ∀ {State Action : Set}
    {score : CouplingScore State Action}
    {state : State}
    {a b c : Action} →
  NoWorseCoupled score state a b →
  NoWorseCoupled score state b c →
  NoWorseCoupled score state a c
noWorseCoupledTrans = ≤-trans

------------------------------------------------------------------------
-- Least-coupled choice among actions that are actually admissible.
------------------------------------------------------------------------

record LeastCoupledAdmissibleChoice
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    (score : CouplingScore State Action)
    (state : State) : Set₁ where
  field
    chosenAction : Action
    chosenAdmissible :
      Dependency.AdmissibleAction system state chosenAction
    leastAmongAdmissible :
      ∀ (alternative : Action) →
      Dependency.AdmissibleAction system state alternative →
      NoWorseCoupled score state chosenAction alternative

open LeastCoupledAdmissibleChoice public

------------------------------------------------------------------------
-- Capability-preserving optimization.
--
-- The brain/conscious-access application exposed an important generic boundary:
-- reducing coupling to zero by deleting required communication is not useful
-- decoupling.  A state capability is therefore a proof-relevant requirement on
-- the post-action state.  Optimization may compare coupling only inside the
-- subset of proof-bearing transitions that preserve that capability.
------------------------------------------------------------------------

StateCapability : Set → Set₁
StateCapability State = State → Set

record LeastCoupledCapabilityPreservingChoice
    {State Action : Set}
    (system : Dependency.DependentActionSystem State Action)
    (score : CouplingScore State Action)
    (capability : StateCapability State)
    (state : State) : Set₁ where
  field
    chosenCapabilityAction : Action
    chosenCapabilityAdmissible :
      Dependency.AdmissibleAction system state chosenCapabilityAction
    chosenPreservesCapability :
      capability (Dependency.after chosenCapabilityAdmissible)
    leastAmongCapabilityPreserving :
      ∀ (alternative : Action) →
      (alternativeAdmissible :
        Dependency.AdmissibleAction system state alternative) →
      capability (Dependency.after alternativeAdmissible) →
      NoWorseCoupled score state chosenCapabilityAction alternative

open LeastCoupledCapabilityPreservingChoice public

------------------------------------------------------------------------
-- Post-action residual score and actual decoupling.
------------------------------------------------------------------------

ResidualStateScore : Set → Set
ResidualStateScore State = State → Nat

Decouples :
  ∀ {State Action : Set}
    {system : Dependency.DependentActionSystem State Action} →
  ResidualStateScore State →
  ∀ {before action} →
  Dependency.AdmissibleAction system before action →
  Set
Decouples score {before = before} admissible =
  score (Dependency.after admissible) ≤ score before

StrictlyDecouples :
  ∀ {State Action : Set}
    {system : Dependency.DependentActionSystem State Action} →
  ResidualStateScore State →
  ∀ {before action} →
  Dependency.AdmissibleAction system before action →
  Set
StrictlyDecouples score {before = before} admissible =
  score (Dependency.after admissible) < score before

strictlyDecouplesImpliesDecouples :
  ∀ {State Action : Set}
    {system : Dependency.DependentActionSystem State Action}
    {score : ResidualStateScore State}
    {before action}
    {admissible : Dependency.AdmissibleAction system before action} →
  StrictlyDecouples score admissible →
  Decouples score admissible
strictlyDecouplesImpliesDecouples = <⇒≤

record CapabilityPreservingDecoupling
    {State Action : Set}
    {system : Dependency.DependentActionSystem State Action}
    (score : ResidualStateScore State)
    (capability : StateCapability State)
    {before action}
    (admissible : Dependency.AdmissibleAction system before action) : Set where
  constructor capabilityPreservingDecoupling
  field
    preservesRequiredCapability :
      capability (Dependency.after admissible)
    residualCouplingDoesNotIncrease :
      Decouples score admissible

open CapabilityPreservingDecoupling public

------------------------------------------------------------------------
-- Boundary receipt kept theorem-bearing: the generic seam proves refinement,
-- non-descent, admissibility-aware ordering, and capability-preserving
-- decoupling, but deliberately does not promote those facts into a spectral-
-- independence theorem.
------------------------------------------------------------------------

record ResidualDependencyBoundary : Set where
  constructor residualDependencyBoundary
  field
    dependencyCanStrictlyRefineCurrentObservation : Bool
    dependencyCanStrictlyRefineCurrentObservationIsTrue :
      dependencyCanStrictlyRefineCurrentObservation ≡ true
    hiddenDependencyCanBlockCoarseDescent : Bool
    hiddenDependencyCanBlockCoarseDescentIsTrue :
      hiddenDependencyCanBlockCoarseDescent ≡ true
    admissibilityPrecedesCouplingOptimization : Bool
    admissibilityPrecedesCouplingOptimizationIsTrue :
      admissibilityPrecedesCouplingOptimization ≡ true
    decouplingMayRequireCapabilityConstraint : Bool
    decouplingMayRequireCapabilityConstraintIsTrue :
      decouplingMayRequireCapabilityConstraint ≡ true
    finiteScoreAutomaticallySpectral : Bool
    finiteScoreAutomaticallySpectralIsFalse :
      finiteScoreAutomaticallySpectral ≡ false

canonicalResidualDependencyBoundary : ResidualDependencyBoundary
canonicalResidualDependencyBoundary =
  residualDependencyBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
