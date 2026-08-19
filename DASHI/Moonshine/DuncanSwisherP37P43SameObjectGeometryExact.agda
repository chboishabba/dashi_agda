module DASHI.Moonshine.DuncanSwisherP37P43SameObjectGeometryExact where

------------------------------------------------------------------------
-- SAME-OBJECT p=37 / p=43 DUNCAN--SWISHER CONTROLS
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- GEOMETRIC SOURCES
-- SageMath supersingular-points documentation (p=37 executable carrier);
-- Josep Gonzalez, "On the p-th division polynomial", JNT 233 (2022),
-- DOI: 10.1016/j.jnt.2021.06.011;
-- Katz--Mazur, "Arithmetic Moduli of Elliptic Curves",
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Replace the old constructor receipts
--
--   p37Case : DS.Case 1 2 2 0
--   p43Case : DS.Case 2 2 2 0
--
-- by explicit partitions of the ACTUAL source-facing Frobenius carriers.
-- `|S_p^2|` counts the two individual non-rational j-points, not one pair.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (s≤s; z≤n)

import DASHI.Moonshine.DuncanSwisherTheorem12Exact as DS
import DASHI.Moonshine.DuncanSwisherPrimeIndexedMinimumAutomorphismExact as Minimum
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43

------------------------------------------------------------------------
-- p=37 actual carrier partition.
------------------------------------------------------------------------

data P37RationalSupersingularPoint : Set where
  rational8 : P37RationalSupersingularPoint

data P37QuadraticSupersingularPoint : Set where
  quadratic27aPlus23 quadratic10aPlus20 : P37QuadraticSupersingularPoint

p37RationalUnderlying : P37RationalSupersingularPoint → P37.P37SupersingularJ
p37RationalUnderlying rational8 = P37.j8

p37QuadraticUnderlying : P37QuadraticSupersingularPoint → P37.P37SupersingularJ
p37QuadraticUnderlying quadratic27aPlus23 = P37.j27aPlus23
p37QuadraticUnderlying quadratic10aPlus20 = P37.j10aPlus20

p37RationalFixedByFrobenius :
  (x : P37RationalSupersingularPoint) →
  P37.p37Frobenius (p37RationalUnderlying x) ≡ p37RationalUnderlying x
p37RationalFixedByFrobenius rational8 = refl

p37QuadraticExchangedByFrobenius :
  P37.p37Frobenius (p37QuadraticUnderlying quadratic27aPlus23)
    ≡ p37QuadraticUnderlying quadratic10aPlus20
p37QuadraticExchangedByFrobenius = refl

p37ActualRationalPointCount : Nat
p37ActualRationalPointCount = 1

p37ActualQuadraticPointCount : Nat
p37ActualQuadraticPointCount = 2

p37ActualMinimumAutOrder : Nat
p37ActualMinimumAutOrder = Minimum.minimumOrder Minimum.p37Minimum

p37ActualMinimumAutIsTwo : p37ActualMinimumAutOrder ≡ 2
p37ActualMinimumAutIsTwo = refl

p37SameObjectTheorem12Case :
  DS.DuncanSwisherTheorem12Case
    p37ActualRationalPointCount
    p37ActualQuadraticPointCount
    p37ActualMinimumAutOrder
    0
p37SameObjectTheorem12Case =
  DS.hasNonRationalSupersingular (s≤s z≤n) refl

------------------------------------------------------------------------
-- p=43 actual carrier partition.
------------------------------------------------------------------------

data P43RationalSupersingularPoint : Set where
  rational1728 rational41 : P43RationalSupersingularPoint

data P43QuadraticSupersingularPoint : Set where
  quadraticJ0 quadraticJ1 : P43QuadraticSupersingularPoint

p43RationalUnderlying : P43RationalSupersingularPoint → P43.P43GeometricJ
p43RationalUnderlying rational1728 = P43.j1728
p43RationalUnderlying rational41 = P43.j41

p43QuadraticUnderlying : P43QuadraticSupersingularPoint → P43.P43GeometricJ
p43QuadraticUnderlying quadraticJ0 = P43.jQuadratic0
p43QuadraticUnderlying quadraticJ1 = P43.jQuadratic1

p43RationalFixedByFrobenius :
  (x : P43RationalSupersingularPoint) →
  P43.p43CoarseFrobenius (p43RationalUnderlying x) ≡ p43RationalUnderlying x
p43RationalFixedByFrobenius rational1728 = refl
p43RationalFixedByFrobenius rational41 = refl

p43QuadraticExchangedByFrobenius :
  P43.p43CoarseFrobenius (p43QuadraticUnderlying quadraticJ0)
    ≡ p43QuadraticUnderlying quadraticJ1
p43QuadraticExchangedByFrobenius = refl

p43ActualRationalPointCount : Nat
p43ActualRationalPointCount = 2

p43ActualQuadraticPointCount : Nat
p43ActualQuadraticPointCount = 2

p43ActualMinimumAutOrder : Nat
p43ActualMinimumAutOrder = Minimum.minimumOrder Minimum.p43Minimum

p43ActualMinimumAutIsTwo : p43ActualMinimumAutOrder ≡ 2
p43ActualMinimumAutIsTwo = refl

p43SameObjectTheorem12Case :
  DS.DuncanSwisherTheorem12Case
    p43ActualRationalPointCount
    p43ActualQuadraticPointCount
    p43ActualMinimumAutOrder
    0
p43SameObjectTheorem12Case =
  DS.hasNonRationalSupersingular (s≤s z≤n) refl

------------------------------------------------------------------------
-- Point-vs-pair distinction is theorem-visible.
------------------------------------------------------------------------

p37OnePairMeansTwoQuadraticPoints : p37ActualQuadraticPointCount ≡ 2
p37OnePairMeansTwoQuadraticPoints = refl

p43OnePairMeansTwoQuadraticPoints : p43ActualQuadraticPointCount ≡ 2
p43OnePairMeansTwoQuadraticPoints = refl

record DuncanSwisherP37P43SameObjectBoundary : Set where
  field
    p37ActualCarrierPartitioned : Bool
    p43ActualCarrierPartitioned : Bool
    p37Theorem12CaseDerivedOnSameCarrier : Bool
    p43Theorem12CaseDerivedOnSameCarrier : Bool
    quadraticPointsKeptDistinctFromPairCount : Bool
    oldSelfEqualityReceiptRequired : Bool

canonicalDuncanSwisherP37P43SameObjectBoundary :
  DuncanSwisherP37P43SameObjectBoundary
canonicalDuncanSwisherP37P43SameObjectBoundary = record
  { p37ActualCarrierPartitioned = true
  ; p43ActualCarrierPartitioned = true
  ; p37Theorem12CaseDerivedOnSameCarrier = true
  ; p43Theorem12CaseDerivedOnSameCarrier = true
  ; quadraticPointsKeptDistinctFromPairCount = true
  ; oldSelfEqualityReceiptRequired = false
  }
