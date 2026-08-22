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
-- Beyond Banaszczyk", STOC 2026; arXiv:2508.03961,
-- DOI 10.48550/arXiv.2508.03961.
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
--
-- Influences retains the typed relational object.  dependencyCode is an
-- explicitly chosen finite/quotient observation suitable for consumer-side
-- refinement.  No completeness relationship between the two is assumed.
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
-- Quantitative seam.
--
-- A coupling score is intentionally only Nat-valued here.  It can count edges,
-- active cross-blocks, maximum dependency degree, failed separations, or any
-- other proved finite statistic.  A later linear-algebraic instantiation may
-- map a genuine Gram/covariance/off-diagonal operator estimate into this
-- ordering, but this generic core does not pretend that every score is
-- spectral.
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
--
-- This keeps optimization subordinate to TypedDependencyCore's proof gate:
-- a low-scoring action constructor cannot win unless it also carries an
-- AdmissibleAction witness at the current fine state.
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
-- Post-action residual score and actual decoupling.
--
-- This is separate from the action-ranking score above.  The first can rank
-- candidate perturbations before execution; the second certifies what a
-- proof-bearing transition actually does to a residual state statistic.
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

------------------------------------------------------------------------
-- Boundary receipt kept theorem-bearing: the generic seam proves refinement
-- and admissibility-aware ordering, but deliberately does not promote those
-- facts into a spectral-independence theorem.
------------------------------------------------------------------------

record ResidualDependencyBoundary : Set where
  constructor residualDependencyBoundary
  field
    dependencyCanStrictlyRefineCurrentObservation : Bool
    dependencyCanStrictlyRefineCurrentObservationIsTrue :
      dependencyCanStrictlyRefineCurrentObservation ≡ true
    admissibilityPrecedesCouplingOptimization : Bool
    admissibilityPrecedesCouplingOptimizationIsTrue :
      admissibilityPrecedesCouplingOptimization ≡ true
    finiteScoreAutomaticallySpectral : Bool
    finiteScoreAutomaticallySpectralIsFalse :
      finiteScoreAutomaticallySpectral ≡ false

canonicalResidualDependencyBoundary : ResidualDependencyBoundary
canonicalResidualDependencyBoundary =
  residualDependencyBoundary true refl true refl false refl
