{-# OPTIONS --safe #-}

module DASHI.Moonshine.JInvariantTetrationAbelModularTransportExact where

------------------------------------------------------------------------
-- EXPONENTIAL ABEL / MODULAR PERIOD TRANSPORT
--
-- This is a conditional algebraic theorem, NOT a construction of Kneser's
-- analytic tetration or a claim that Abel summation is an Abel coordinate.
--
-- Existing owners to reuse at the concrete-instance boundary:
--   DASHI.Analysis.AbelZeta (Abel *summation*, distinct problem)
--   DASHI.Moonshine.ModularCurveJFrickeInterfaceExact
--   DASHI.Moonshine.JInvariantAnalyticJCoarseFineObserverExact
--   DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact
--   DASHI.Topology.TetrationalGateField (finite tower, distinct problem)
--
-- The carrier Point is explicitly the domain on which exp and the chosen
-- Abel branch are simultaneously available and stable under exp.
-- Establishing such a concrete analytic domain remains a separate gate.
------------------------------------------------------------------------

open import Agda.Primitive using (Set; Set₁)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

private
  variable
    A B : Set

congLocal : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
congLocal f refl = refl

transLocal : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transLocal refl refl = refl

record AbelModularExpSystem : Set₁ where
  field
    Point : Set
    Coordinate : Set
    JValue : Set

    exponential : Point → Point
    abel : Point → Coordinate
    translate : Coordinate → Coordinate
    modularJ : Coordinate → JValue

    -- A(exp w) = T(A(w)) on the specified common branch/domain.
    abelExponentialLaw :
      (w : Point) →
      abel (exponential w) ≡ translate (abel w)

    -- j(T tau) = j(tau); for actual modular j, T(tau)=tau+1.
    modularTranslationLaw :
      (tau : Coordinate) →
      modularJ (translate tau) ≡ modularJ tau

open AbelModularExpSystem public

transportedJ : (S : AbelModularExpSystem) → Point S → JValue S
transportedJ S w = modularJ S (abel S w)

transportedJInvariantUnderExp :
  (S : AbelModularExpSystem) →
  (w : Point S) →
  transportedJ S (exponential S w) ≡ transportedJ S w
transportedJInvariantUnderExp S w =
  transLocal
    (congLocal (modularJ S) (abelExponentialLaw S w))
    (modularTranslationLaw S (abel S w))

expIter :
  (S : AbelModularExpSystem) →
  Nat → Point S → Point S
expIter S zero w = w
expIter S (suc n) w = exponential S (expIter S n w)

transportedJInvariantUnderExpIter :
  (S : AbelModularExpSystem) →
  (n : Nat) →
  (w : Point S) →
  transportedJ S (expIter S n w) ≡ transportedJ S w
transportedJInvariantUnderExpIter S zero w = refl
transportedJInvariantUnderExpIter S (suc n) w =
  transLocal
    (transportedJInvariantUnderExp S (expIter S n w))
    (transportedJInvariantUnderExpIter S n w)

-- Finite observations are downstream of the exact transported J value.
-- No inverse from finite observations to analytic points is asserted.

record JValueObserver (S : AbelModularExpSystem) : Set₁ where
  field
    Observation : Set
    observeJ : JValue S → Observation

open JValueObserver public

observedTransportedJ :
  (S : AbelModularExpSystem) →
  (O : JValueObserver S) →
  Point S → Observation O
observedTransportedJ S O w = observeJ O (transportedJ S w)

observedTransportedJInvariantUnderExp :
  (S : AbelModularExpSystem) →
  (O : JValueObserver S) →
  (w : Point S) →
  observedTransportedJ S O (exponential S w) ≡
  observedTransportedJ S O w
observedTransportedJInvariantUnderExp S O w =
  congLocal (observeJ O) (transportedJInvariantUnderExp S w)

observedTransportedJInvariantUnderExpIter :
  (S : AbelModularExpSystem) →
  (O : JValueObserver S) →
  (n : Nat) →
  (w : Point S) →
  observedTransportedJ S O (expIter S n w) ≡
  observedTransportedJ S O w
observedTransportedJInvariantUnderExpIter S O n w =
  congLocal (observeJ O) (transportedJInvariantUnderExpIter S n w)

ObserverFibre :
  (S : AbelModularExpSystem) →
  (O : JValueObserver S) →
  Observation O → Point S → Set
ObserverFibre S O state w =
  observedTransportedJ S O w ≡ state

exponentialPreservesObserverFibre :
  (S : AbelModularExpSystem) →
  (O : JValueObserver S) →
  (state : Observation O) →
  (w : Point S) →
  ObserverFibre S O state w →
  ObserverFibre S O state (exponential S w)
exponentialPreservesObserverFibre S O state w inFibre =
  transLocal (observedTransportedJInvariantUnderExp S O w) inFibre
