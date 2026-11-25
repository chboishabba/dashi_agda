module DASHI.Analysis.GRHSignedPhaseTransverseRecoveryExact where

-- Paper 9 #1546 (2b8bff03), signed two-slice kernel donor.
-- Classical homogeneous symmetric polynomial algebra; DASHI consumer weld.
-- Local polynomial chart only: no analytic zero sum or character transport.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _/_)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized

two four seven nine half : ℚ
two = + 2 / 1
four = + 4 / 1
seven = + 7 / 1
nine = + 9 / 1
half = + 1 / 2

record Sixth : Set where
  constructor sixth
  field axis mixed : ℚ

record Eighth : Set where
  constructor eighth
  field axis diagonal mixed : ℚ

-- The two observation-adapted homogeneous polynomial charts.
eval6 : Sixth → ℚ → ℚ → ℚ
eval6 (sixth a c) x y =
  a * (x * x * x - y * y * y) + c * x * y * (x - y)

eval8 : Eighth → ℚ → ℚ → ℚ
eval8 (eighth a b c) x y =
  a * (x * x - y * y) * (x * x - y * y) +
  b * x * x * y * y + c * x * y * (x - y) * (x - y)

record SixthObs : Set where
  constructor sixthObs
  field axis transverse : ℚ

record EighthObs : Set where
  constructor eighthObs
  field axis diagonal transverse : ℚ

observe6 : Sixth → SixthObs
observe6 (sixth a c) = sixthObs a (0ℚ - seven * a - two * c)

observe8 : Eighth → EighthObs
observe8 (eighth a b c) = eighthObs a b (nine * a + four * b + two * c)

recover6 : SixthObs → Sixth
recover6 (sixthObs a t) = sixth a ((0ℚ - t - seven * a) * half)

recover8 : EighthObs → Eighth
recover8 (eighthObs a b t) = eighth a b ((t - nine * a - four * b) * half)

mixed6RoundTrip : (a c : ℚ) →
  (0ℚ - (0ℚ - seven * a - two * c) - seven * a) * half ≡ c
mixed6RoundTrip a c = solve 2
  (λ a c → ((con 0ℚ :- (con 0ℚ :- con seven :* a :- con two :* c)
             :- con seven :* a) :* con half) := c)
  refl a c

mixed8RoundTrip : (a b c : ℚ) →
  (nine * a + four * b + two * c - nine * a - four * b) * half ≡ c
mixed8RoundTrip a b c = solve 3
  (λ a b c → (((con nine :* a :+ con four :* b :+ con two :* c)
              :- con nine :* a :- con four :* b) :* con half) := c)
  refl a b c

recoverObserve6 : (f : Sixth) → recover6 (observe6 f) ≡ f
recoverObserve6 (sixth a c) rewrite mixed6RoundTrip a c = refl

recoverObserve8 : (f : Eighth) → recover8 (observe8 f) ≡ f
recoverObserve8 (eighth a b c) rewrite mixed8RoundTrip a b c = refl

transverse6RoundTrip : (a t : ℚ) →
  0ℚ - seven * a - two * ((0ℚ - t - seven * a) * half) ≡ t
transverse6RoundTrip a t = solve 2
  (λ a t → (con 0ℚ :- con seven :* a :-
            con two :* ((con 0ℚ :- t :- con seven :* a) :* con half)) := t)
  refl a t

transverse8RoundTrip : (a b t : ℚ) →
  nine * a + four * b + two * ((t - nine * a - four * b) * half) ≡ t
transverse8RoundTrip a b t = solve 3
  (λ a b t → (con nine :* a :+ con four :* b :+
            con two :* ((t :- con nine :* a :- con four :* b) :* con half)) := t)
  refl a b t

observeRecover6 : (o : SixthObs) → observe6 (recover6 o) ≡ o
observeRecover6 (sixthObs a t) rewrite transverse6RoundTrip a t = refl

observeRecover8 : (o : EighthObs) → observe8 (recover8 o) ≡ o
observeRecover8 (eighthObs a b t) rewrite transverse8RoundTrip a b t = refl

-- Literal slice identification, not just a formal coordinate renaming.
axis6Exact : (a c : ℚ) → eval6 (sixth a c) 1ℚ 0ℚ ≡ a
axis6Exact a c = solve 2 (λ a c →
  (a :* (con 1ℚ :* con 1ℚ :* con 1ℚ :- con 0ℚ :* con 0ℚ :* con 0ℚ)
   :+ c :* con 1ℚ :* con 0ℚ :* (con 1ℚ :- con 0ℚ)) := a) refl a c

diag6Exact : (a c : ℚ) → eval6 (sixth a c) 1ℚ 1ℚ ≡ 0ℚ
diag6Exact a c = solve 2 (λ a c →
  (a :* (con 1ℚ :* con 1ℚ :* con 1ℚ :- con 1ℚ :* con 1ℚ :* con 1ℚ)
   :+ c :* con 1ℚ :* con 1ℚ :* (con 1ℚ :- con 1ℚ)) := con 0ℚ) refl a c

-- Explicit solver expressions match the original evaluation syntax; constants
-- are reduced by the rational ring normalizer, not floating point.
slice6Exact : (a c : ℚ) →
  eval6 (sixth a c) 1ℚ two ≡ SixthObs.transverse (observe6 (sixth a c))
slice6Exact a c = solve 2 (λ a c →
  (a :* (con 1ℚ :* con 1ℚ :* con 1ℚ :- con two :* con two :* con two)
     :+ c :* con 1ℚ :* con two :* (con 1ℚ :- con two))
  := (con 0ℚ :- con seven :* a :- con two :* c)) refl a c

axis8Exact : (a b c : ℚ) → eval8 (eighth a b c) 1ℚ 0ℚ ≡ a
axis8Exact a b c = solve 3 (λ a b c →
  (a :* (con 1ℚ :* con 1ℚ :- con 0ℚ :* con 0ℚ)
     :* (con 1ℚ :* con 1ℚ :- con 0ℚ :* con 0ℚ)
     :+ b :* con 1ℚ :* con 1ℚ :* con 0ℚ :* con 0ℚ
     :+ c :* con 1ℚ :* con 0ℚ :* (con 1ℚ :- con 0ℚ) :* (con 1ℚ :- con 0ℚ))
  := a) refl a b c

diag8Exact : (a b c : ℚ) → eval8 (eighth a b c) 1ℚ 1ℚ ≡ b
diag8Exact a b c = solve 3 (λ a b c →
  (a :* (con 1ℚ :* con 1ℚ :- con 1ℚ :* con 1ℚ)
     :* (con 1ℚ :* con 1ℚ :- con 1ℚ :* con 1ℚ)
     :+ b :* con 1ℚ :* con 1ℚ :* con 1ℚ :* con 1ℚ
     :+ c :* con 1ℚ :* con 1ℚ :* (con 1ℚ :- con 1ℚ) :* (con 1ℚ :- con 1ℚ))
  := b) refl a b c

slice8Exact : (a b c : ℚ) →
  eval8 (eighth a b c) 1ℚ two ≡ EighthObs.transverse (observe8 (eighth a b c))
slice8Exact a b c = solve 3 (λ a b c →
  (a :* (con 1ℚ :* con 1ℚ :- con two :* con two)
     :* (con 1ℚ :* con 1ℚ :- con two :* con two)
     :+ b :* con 1ℚ :* con 1ℚ :* con two :* con two
     :+ c :* con 1ℚ :* con two :* (con 1ℚ :- con two) :* (con 1ℚ :- con two))
  := (con nine :* a :+ con four :* b :+ con two :* c)) refl a b c

phaseSym : {A : Set} {x y : A} → x ≡ y → y ≡ x
phaseSym refl = refl

phaseCong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
phaseCong f refl = refl

-- Every declared coefficient-chart consumer descends after transverse repair.
sixthFactors : {Outcome : Set} (consumer : Sixth → Outcome) →
  Consumer.FactorsThrough observe6 consumer
sixthFactors consumer = Factorized.factorizedRefinement
  (λ o → consumer (recover6 o))
  (λ f → phaseSym (phaseCong consumer (recoverObserve6 f)))

eighthFactors : {Outcome : Set} (consumer : Eighth → Outcome) →
  Consumer.FactorsThrough observe8 consumer
eighthFactors consumer = Factorized.factorizedRefinement
  (λ o → consumer (recover8 o))
  (λ f → phaseSym (phaseCong consumer (recoverObserve8 f)))

-- Exact lost-mode witnesses on the old observations.
old6 : Sixth → ℚ
old6 = Sixth.axis

record Old8 : Set where
  constructor old8
  field axis diagonal : ℚ

oldObserve8 : Eighth → Old8
oldObserve8 (eighth a b c) = old8 a b

zeroNotOne : 0ℚ ≡ 1ℚ → ⊥
zeroNotOne ()

sixthLostMixed : Consumer.ConsumerNonDescentWitness old6 Sixth.mixed
sixthLostMixed = Consumer.consumerNonDescentWitness
  (sixth 0ℚ 0ℚ) (sixth 0ℚ 1ℚ) refl zeroNotOne

eighthLostMixed : Consumer.ConsumerNonDescentWitness oldObserve8 Eighth.mixed
eighthLostMixed = Consumer.consumerNonDescentWitness
  (eighth 0ℚ 0ℚ 0ℚ) (eighth 0ℚ 0ℚ 1ℚ) refl zeroNotOne

physical6 : Sixth
physical6 = sixth 1ℚ (- (+ 15 / 1))

physical8 : Eighth
physical8 = eighth 1ℚ (+ 16 / 1) (- (+ 28 / 1))

-- A declared linear consumer (e.g. a finite weighted evaluation) needs no
-- transverse coordinate exactly when its mixed coefficient is zero.
linear6 : ℚ → ℚ → Sixth → ℚ
linear6 p q (sixth a c) = p * a + q * c

linear8 : ℚ → ℚ → ℚ → Eighth → ℚ
linear8 p r q (eighth a b c) = p * a + r * b + q * c

old6LinearSuffices : (p q : ℚ) → q ≡ 0ℚ →
  Consumer.FactorsThrough old6 (linear6 p q)
old6LinearSuffices p q qZero rewrite qZero = Factorized.factorizedRefinement
  (λ a → p * a)
  (λ { (sixth a c) → solve 3 (λ p a c →
       (p :* a :+ con 0ℚ :* c) := (p :* a)) refl p a c })

old8LinearSuffices : (p r q : ℚ) → q ≡ 0ℚ →
  Consumer.FactorsThrough oldObserve8 (linear8 p r q)
old8LinearSuffices p r q qZero rewrite qZero = Factorized.factorizedRefinement
  (λ { (old8 a b) → p * a + r * b })
  (λ { (eighth a b c) → solve 5 (λ p r a b c →
       (p :* a :+ r :* b :+ con 0ℚ :* c) := (p :* a :+ r :* b))
       refl p r a b c })

phaseTrans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
phaseTrans refl e = e

old6LinearRequires : (p q : ℚ) →
  Consumer.FactorsThrough old6 (linear6 p q) → q ≡ 0ℚ
old6LinearRequires p q factor =
  phaseTrans (phaseSym (solve 2 (λ p q →
          (p :* con 0ℚ :+ q :* con 1ℚ) := q) refl p q))
    (phaseTrans (phaseSym (Consumer.factorsThroughImpliesFibreConstant factor
      (sixth 0ℚ 0ℚ) (sixth 0ℚ 1ℚ) refl))
      (solve 2 (λ p q → (p :* con 0ℚ :+ q :* con 0ℚ) := con 0ℚ)
        refl p q))

old8LinearRequires : (p r q : ℚ) →
  Consumer.FactorsThrough oldObserve8 (linear8 p r q) → q ≡ 0ℚ
old8LinearRequires p r q factor =
  phaseTrans (phaseSym (solve 3 (λ p r q →
          (p :* con 0ℚ :+ r :* con 0ℚ :+ q :* con 1ℚ) := q) refl p r q))
    (phaseTrans (phaseSym (Consumer.factorsThroughImpliesFibreConstant factor
      (eighth 0ℚ 0ℚ 0ℚ) (eighth 0ℚ 0ℚ 1ℚ) refl))
      (solve 3 (λ p r q →
        (p :* con 0ℚ :+ r :* con 0ℚ :+ q :* con 0ℚ) := con 0ℚ)
        refl p r q))
