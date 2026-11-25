module DASHI.Moonshine.JInvariantEisensteinThreeB54CoefficientBridgeExact where

-- Source-written, not kernel checked. Classical X0(3) rational
-- parametrization (Maier, JRMS 24 (2009), arXiv:math/0611041).
-- Finite coefficient and polynomial identities only; no implied
-- equivariant isomorphism or native analytic modular-curve theorem.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import DASHI.Moonshine.JInvariantEisensteinCoefficientTowerExact as E
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as L
import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as M
import DASHI.Moonshine.Monster196884FibreInterferenceExact as F

weight12FirstCoefficient :
  (+ 3) * E.e4Coefficient 1 + (- (+ 2)) * E.e6Coefficient 1
    ≡ (+ 32) * (+ M.monster3BConformalTrace)
weight12FirstCoefficient = refl

constantFromSignedEisenstein :
  E.e4Coefficient 1 + (- E.e6Coefficient 1) ≡ + 744
constantFromSignedEisenstein = refl

e8SourceCoefficient : E.e4Coefficient 1 ≡ + L.e8RootCount
e8SourceCoefficient = refl

-- Eta ratio t=q^-1 prod_(3 ∤ n)(1-q^n)^12.
-- Through degree two its unit is (1-q)^12(1-q^2)^12.
-- Choose(12,2)=66, so 54 is the signed coefficient, not an assigned index.
etaRatioFirstTrace :
  (+ 66) + (- (+ 12)) ≡ + M.monster3BConformalTrace
etaRatioFirstTrace = refl

-- The denominator-cleared rational map on the original t coordinate.
levelThreeNumerator : (t : ℤ) →
  (t + (+ 27)) * ((t + (+ 243)) * (t + (+ 243)) * (t + (+ 243)))
  ≡ t * t * t * t + (+ 756) * (t * t * t)
    + (+ F.fineSectorDimension) * (t * t)
    + (+ 19131876) * t + (+ 387420489)
levelThreeNumerator t =
  solve 1
    (λ x →
      (x :+ con (+ 27)) :*
        ((x :+ con (+ 243)) :* (x :+ con (+ 243)) :* (x :+ con (+ 243)))
      := x :* x :* x :* x :+ con (+ 756) :* (x :* x :* x)
        :+ con (+ F.fineSectorDimension) :* (x :* x)
        :+ con (+ 19131876) :* x :+ con (+ 387420489))
    refl t

fineFromLevelThree :
  (+ 3) * (+ 243) * (+ 243) + (+ 81) * (+ 243)
    ≡ + F.fineSectorDimension
fineFromLevelThree = refl

jFirstFromLevelThree :
  (+ F.fineSectorDimension) + (+ M.monster3BConformalTrace)
    ≡ + M.monster3BConformalDimension
jFirstFromLevelThree = refl

-- Independent low-order eta/E4 quotient computation, preserving
-- the 24-coloured oscillator coefficient and the Leech shell.
e4CubeSecond :
  (+ 3) * E.e4Coefficient 2
    + (+ 3) * E.e4Coefficient 1 * E.e4Coefficient 1 ≡ + 179280
e4CubeSecond = refl

oscillatorSecond : (+ 300) + (+ 24) ≡ (+ 6) * (+ M.monster3BConformalTrace)
oscillatorSecond = refl

leechAndOscillator :
  (+ L.leechMinimalVectorCount) + (+ 6) * (+ M.monster3BConformalTrace)
    ≡ + M.monster3BConformalDimension
leechAndOscillator = refl

fineLeechDifference :
  (+ L.leechMinimalVectorCount) + (+ 5) * (+ M.monster3BConformalTrace)
    ≡ + F.fineSectorDimension
fineLeechDifference = refl

jFromEisensteinEta :
  (+ 3) * E.e4Coefficient 2
    + (+ 3) * E.e4Coefficient 1 * E.e4Coefficient 1
    + (+ 24) * ((+ 3) * E.e4Coefficient 1) + (+ 324)
    ≡ + M.monster3BConformalDimension
jFromEisensteinEta = refl
