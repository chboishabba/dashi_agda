module DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact where

------------------------------------------------------------------------
-- ROUND396 / AUTHORITY REPAIR: POSITIVITY ONLY ON PAIRS ACTUALLY ENUMERATED
--
-- R390 used a module parameter
--
--   (alpha beta : PhysicalTriadIncidence) -> Positive(pairRate alpha beta)
--
-- even though it only consumes pairs drawn from one finite cell list.  That
-- global premise is too strong: the primitive physical incidence carrier also
-- contains zero-mode incidences, while the eventual physical proof only needs
-- positivity on the selected nonzero-output fibres.
--
-- This owner localizes the premise exactly.  PairRatePositiveOn xs recursively
-- stores positivity only for unordered list-position pairs that occur in xs.
-- The R290 enumeration and exact R180 Gram-debt equality then use precisely
-- those witnesses and no others.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; map; _++_)
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

data _OccursIn_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x OccursIn (x ∷ xs)
  there : ∀ {y xs} → x OccursIn xs → x OccursIn (y ∷ xs)

module LocalEnumerate
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module P = R389.DoubleMixedPair physicalSystem S

  data PairRatePositiveOn : List Physical.PhysicalTriadIncidence → Set where
    positiveNil : PairRatePositiveOn []
    positiveCons :
      ∀ {alpha rest} →
      ((beta : Physical.PhysicalTriadIncidence) →
        beta OccursIn rest →
        Positive
          (R291.pairRate (P.physicalDoubleMixedPair alpha beta))) →
      PairRatePositiveOn rest →
      PairRatePositiveOn (alpha ∷ rest)

  headR290Pairs :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta OccursIn rest →
      Positive (R291.pairRate (P.physicalDoubleMixedPair alpha beta))) →
    List R290.DampedGramPair
  headR290Pairs alpha [] positive = []
  headR290Pairs alpha (beta ∷ rest) positive =
    P.pairRatePositiveBuildsR290 alpha beta (positive beta here)
    ∷ headR290Pairs alpha rest
        (λ gamma member → positive gamma (there member))

  allR290Pairs :
    (items : List Physical.PhysicalTriadIncidence) →
    PairRatePositiveOn items →
    List R290.DampedGramPair
  allR290Pairs [] positiveNil = []
  allR290Pairs (alpha ∷ rest) (positiveCons headPositive tailPositive) =
    headR290Pairs alpha rest headPositive ++
      allR290Pairs rest tailPositive

  doubleMixedCells :
    List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  doubleMixedCells = map (R225.doubleMixedCell S P.D.Pair.velocity)

  sumGramAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumGram (left ++ right)
    ≡ R385.sumGram left + R385.sumGram right
  sumGramAppend [] right = refl
  sumGramAppend (pair ∷ rest) right
    rewrite sumGramAppend rest right = refl

  headPairsGramExact :
    (alpha : Physical.PhysicalTriadIncidence)
    (rest : List Physical.PhysicalTriadIncidence)
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta OccursIn rest →
      Positive (R291.pairRate (P.physicalDoubleMixedPair alpha beta))) →
    R385.sumGram (headR290Pairs alpha rest positive)
    ≡ R383.headPairSum
        (R225.doubleMixedCell S P.D.Pair.velocity alpha)
        (doubleMixedCells rest)
  headPairsGramExact alpha [] positive = refl
  headPairsGramExact alpha (beta ∷ rest) positive
    rewrite headPairsGramExact alpha rest
      (λ gamma member → positive gamma (there member)) = refl

  allPairsGramExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : PairRatePositiveOn items) →
    R385.sumGram (allR290Pairs items positive)
    ≡ R383.allPairSum (doubleMixedCells items)
  allPairsGramExact [] positiveNil = refl
  allPairsGramExact (alpha ∷ rest)
      (positiveCons headPositive tailPositive) =
    trans
      (sumGramAppend
        (headR290Pairs alpha rest headPositive)
        (allR290Pairs rest tailPositive))
      (cong₂ _+_
        (headPairsGramExact alpha rest headPositive)
        (allPairsGramExact rest tailPositive))

  r180DebtIsLocalR290PairGramSum :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : PairRatePositiveOn items) →
    R180.gramDebt (doubleMixedCells items)
    ≡ R385.sumGram (allR290Pairs items positive)
  r180DebtIsLocalR290PairGramSum items positive =
    trans
      (R383.r180GramDebtIsAllPairSum (doubleMixedCells items))
      (sym (allPairsGramExact items positive))

round396PairRatePositivityLocalizedToSelectedList : Bool
round396PairRatePositivityLocalizedToSelectedList = true

round396GlobalAllIncidencePositivityRequired : Bool
round396GlobalAllIncidencePositivityRequired = false

round396LiteralDebtStillEnumeratedExactly : Bool
round396LiteralDebtStillEnumeratedExactly = true

round396GlobalAllIncidencePositivityRequiredIsFalse :
  round396GlobalAllIncidencePositivityRequired ≡ false
round396GlobalAllIncidencePositivityRequiredIsFalse = refl
