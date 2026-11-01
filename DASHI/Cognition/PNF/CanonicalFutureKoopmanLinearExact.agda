module DASHI.Cognition.PNF.CanonicalFutureKoopmanLinearExact where

------------------------------------------------------------------------
-- CANONICAL FUTURE QUOTIENT -> EXACT LINEAR OBSERVABLE DYNAMICS
--
-- SOURCE-FACING MOTIVATION
-- Steven L. Brunton, Bingni W. Brunton, Joshua L. Proctor, J. Nathan Kutz,
-- "Koopman Invariant Subspaces and Finite Linear Representations of Nonlinear
-- Dynamical Systems for Control", PLOS ONE 11(2): e0150171 (2016).
-- DOI: 10.1371/journal.pone.0150171.
--
-- SOURCE BOUNDARY
-- Brunton et al. study Koopman-invariant observable subspaces and finite linear
-- representations for nonlinear dynamics/control.  DASHI's theorem below is a
-- separate constructive statement: once the consumer-specific canonical future
-- quotient and its action are already proved, rational observables on that
-- quotient carry an exact linear pullback operator automatically.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge
import DASHI.Cognition.PNF.CanonicalFutureMinimalDynamicalRealizationExact as Minimal
import DASHI.Cognition.PNF.CanonicalFutureObservableAlgebraExact as Algebra

------------------------------------------------------------------------
-- Quotient observables form a rational module pointwise.  Equality is stated
-- pointwise, so no function-extensionality principle is required.
------------------------------------------------------------------------

record RationalQuotientObservable
    {State Action Observation : Set}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) : Set₁ where
  constructor rationalQuotientObservable
  field
    value : Future.QuotientCode presentation → ℚ

open RationalQuotientObservable public

_+O_ :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  RationalQuotientObservable presentation →
  RationalQuotientObservable presentation →
  RationalQuotientObservable presentation
left +O right = rationalQuotientObservable λ code →
  value left code + value right code

scaleO :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  ℚ → RationalQuotientObservable presentation →
  RationalQuotientObservable presentation
scaleO scalar observable = rationalQuotientObservable λ code →
  scalar * value observable code

PointwiseEqual :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  RationalQuotientObservable presentation →
  RationalQuotientObservable presentation → Set
PointwiseEqual left right = (code : _) → value left code ≡ value right code

------------------------------------------------------------------------
-- Koopman pullback on the canonical quotient: K_a f = f o quotientStep_a.
------------------------------------------------------------------------

koopman :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  Minimal.CanonicalFutureDynamicalRealization step label observe presentation →
  Action →
  RationalQuotientObservable presentation →
  RationalQuotientObservable presentation
koopman realization action observable = rationalQuotientObservable λ code →
  value observable (Minimal.quotientStep realization action code)

koopmanAdditive :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe}
    (realization : Minimal.CanonicalFutureDynamicalRealization
      step label observe presentation)
    (action : Action)
    (left right : RationalQuotientObservable presentation) →
  PointwiseEqual
    (koopman realization action (left +O right))
    (koopman realization action left +O koopman realization action right)
koopmanAdditive realization action left right code = refl

koopmanHomogeneous :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe}
    (realization : Minimal.CanonicalFutureDynamicalRealization
      step label observe presentation)
    (action : Action) (scalar : ℚ)
    (observable : RationalQuotientObservable presentation) →
  PointwiseEqual
    (koopman realization action (scaleO scalar observable))
    (scaleO scalar (koopman realization action observable))
koopmanHomogeneous realization action scalar observable code = refl

------------------------------------------------------------------------
-- Fine-state evaluation agrees exactly with quotient Koopman evolution.
------------------------------------------------------------------------

liftRationalObservable :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    (presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe) →
  RationalQuotientObservable presentation →
  Algebra.FutureInvariantObservable
    {step = step} {label = label} {observe = observe} ℚ
liftRationalObservable presentation observable =
  Algebra.liftQuotientObservable presentation (value observable)

koopmanExactlyAdvancesFineObservation :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe}
    (realization : Minimal.CanonicalFutureDynamicalRealization
      step label observe presentation)
    (action : Action)
    (observable : RationalQuotientObservable presentation)
    (state : State) →
  Algebra.evaluate
    (Algebra.actionPullback action
      (liftRationalObservable presentation observable)) state
  ≡ value (koopman realization action observable)
      (Future.classOf presentation state)
koopmanExactlyAdvancesFineObservation realization action observable state =
  cong (value observable) (Minimal.actionDescends realization action state)

------------------------------------------------------------------------
-- Finite-trace Koopman operator on quotient observables.
------------------------------------------------------------------------

koopmanTrace :
  ∀ {State Action Observation}
    {step : Action → State → State}
    {label : Action → String}
    {observe : State → Observation}
    {presentation : Future.FutureEquivalencePresentation
      (Bridge.deterministicSystem step label) observe} →
  Minimal.CanonicalFutureDynamicalRealization step label observe presentation →
  List Action →
  RationalQuotientObservable presentation →
  RationalQuotientObservable presentation
koopmanTrace realization [] observable = observable
koopmanTrace realization (action ∷ actions) observable =
  koopman realization action (koopmanTrace realization actions observable)

------------------------------------------------------------------------
-- Boundary: exact linearity here is on the full rational observable carrier of
-- the canonical quotient.  A finite k-dimensional matrix representation still
-- requires a finite enumeration/basis of QuotientCode; minimum dimension is a
-- separate theorem under a declared realization class.
------------------------------------------------------------------------
