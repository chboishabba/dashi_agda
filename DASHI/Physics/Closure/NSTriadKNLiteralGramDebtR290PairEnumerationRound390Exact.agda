module DASHI.Physics.Closure.NSTriadKNLiteralGramDebtR290PairEnumerationRound390Exact where

------------------------------------------------------------------------
-- ROUND390 / SAME-OBJECT R378-DEBT PAIR ENUMERATION INTO R290
--
-- R386 turns the literal R378 output debt into R180.gramDebt of the actual
-- double-mixed cells.  R383 expands that debt into the finite unordered pair
-- sum.  R389 supplies the corresponding R290 pair for every double-mixed cell
-- pair whose physical decay rate is positive.
--
-- This module makes those indices identical: for an arbitrary finite list of
-- physical incidences it recursively builds exactly one R290 object for each
-- unordered list-position pair and proves that R385.sumGram of that list is
-- the literal R180 Gram debt of the double-mixed cells.
--
-- Positivity is an explicit constructor premise only; no Gram sign or estimate
-- is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Rational using (Positive)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389

F : C3.RealField _
F = Rational.rationalRealField

module Enumerate
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (positivePairRate :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive
        (R291.pairRate
          (R389.DoubleMixedPair.physicalDoubleMixedPair physicalSystem S alpha beta))) where

  module P = R389.DoubleMixedPair physicalSystem S

  headR290Pairs :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence →
    List R290.DampedGramPair
  headR290Pairs alpha [] = []
  headR290Pairs alpha (beta ∷ rest) =
    P.pairRatePositiveBuildsR290 alpha beta (positivePairRate alpha beta)
    ∷ headR290Pairs alpha rest

  allR290Pairs :
    List Physical.PhysicalTriadIncidence → List R290.DampedGramPair
  allR290Pairs [] = []
  allR290Pairs (alpha ∷ rest) =
    headR290Pairs alpha rest ++ allR290Pairs rest
    where
    _++_ : ∀ {A : Set} → List A → List A → List A
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  doubleMixedCells :
    List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  doubleMixedCells = map (R225.doubleMixedCell S P.D.Pair.velocity)

  sumGramAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumGram (append left right)
    ≡ R385.sumGram left + R385.sumGram right
    where
    append : ∀ {A : Set} → List A → List A → List A
    append [] ys = ys
    append (x ∷ xs) ys = x ∷ append xs ys
  sumGramAppend [] right = refl
  sumGramAppend (pair ∷ rest) right
    rewrite sumGramAppend rest right = refl

  headPairsGramExact :
    (alpha : Physical.PhysicalTriadIncidence)
    (rest : List Physical.PhysicalTriadIncidence) →
    R385.sumGram (headR290Pairs alpha rest)
    ≡ R383.headPairSum
        (R225.doubleMixedCell S P.D.Pair.velocity alpha)
        (doubleMixedCells rest)
  headPairsGramExact alpha [] = refl
  headPairsGramExact alpha (beta ∷ rest)
    rewrite headPairsGramExact alpha rest = refl

  allPairsGramExact :
    (items : List Physical.PhysicalTriadIncidence) →
    R385.sumGram (allR290Pairs items)
    ≡ R383.allPairSum (doubleMixedCells items)
  allPairsGramExact [] = refl
  allPairsGramExact (alpha ∷ rest) =
    trans
      (sumGramAppend (headR290Pairs alpha rest) (allR290Pairs rest))
      (cong₂ _+_
        (headPairsGramExact alpha rest)
        (allPairsGramExact rest))

  r180DebtIsR290PairGramSum :
    (items : List Physical.PhysicalTriadIncidence) →
    R180.gramDebt (doubleMixedCells items)
    ≡ R385.sumGram (allR290Pairs items)
  r180DebtIsR290PairGramSum items =
    trans
      (R383.r180GramDebtIsAllPairSum (doubleMixedCells items))
      (sym (allPairsGramExact items))

round390LiteralGramDebtEnumeratedByR290Pairs : Bool
round390LiteralGramDebtEnumeratedByR290Pairs = true

round390PairEnumerationIntroducesCardinalityEstimate : Bool
round390PairEnumerationIntroducesCardinalityEstimate = false

round390TemporalIntegrationUsed : Bool
round390TemporalIntegrationUsed = false

round390LiteralGramDebtEnumeratedByR290PairsIsTrue :
  round390LiteralGramDebtEnumeratedByR290Pairs ≡ true
round390LiteralGramDebtEnumeratedByR290PairsIsTrue = refl
