module DASHI.Physics.Closure.NSTriadKNR573FourSignSecondMomentAggregationExact where

------------------------------------------------------------------------
-- PERIODIC B / R573 FOUR-SIGN INNER CELL -> SECOND-MOMENT AGGREGATION
--
-- R572/R573 expose each nested inner interaction before norms as exactly four
-- R571 helicity channels (++,+-,-+,--).  The local R571 machinery pays one
-- signed channel by one preferred second-moment sample.
--
-- This theorem performs the ONLY safe positive recombination:
--
--   q++ + q+- + q-+ + q--
--     <= |q++|_R571 + |q+-|_R571 + |q-+|_R571 + |q--|_R571
--     <= C (M2++ + M2+- + M2-+ + M2--).
--
-- It does not identify the four vector channels with scalar samples.  That
-- same-object Hermitian scalarization remains the physical representation leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment
import DASHI.Physics.Closure.NSTriadKNR571PreferredOneSidedSecondMomentExact as Preferred

record FourSignR571SecondMomentCell : Set₁ where
  field
    qPP qPM qMP qMM : ℚ

    sPP sPM sMP sMM : Moment.PairedSecondMomentSample

    budget : Preferred.PreferredOneSidedSecondMomentBudget

    qPPBelowMagnitude :
      qPP ≤ Moment.pairedMagnitude sPP
    qPMBelowMagnitude :
      qPM ≤ Moment.pairedMagnitude sPM
    qMPBelowMagnitude :
      qMP ≤ Moment.pairedMagnitude sMP
    qMMBelowMagnitude :
      qMM ≤ Moment.pairedMagnitude sMM

    ppPreferred :
      Moment.pairedMagnitude sPP
      ≤ Preferred.preferredCoefficient budget
          * Moment.weightedSecondMoment sPP

    pmPreferred :
      Moment.pairedMagnitude sPM
      ≤ Preferred.preferredCoefficient budget
          * Moment.weightedSecondMoment sPM

    mpPreferred :
      Moment.pairedMagnitude sMP
      ≤ Preferred.preferredCoefficient budget
          * Moment.weightedSecondMoment sMP

    mmPreferred :
      Moment.pairedMagnitude sMM
      ≤ Preferred.preferredCoefficient budget
          * Moment.weightedSecondMoment sMM

open FourSignR571SecondMomentCell public

fourSignScalar :
  FourSignR571SecondMomentCell → ℚ
fourSignScalar C =
  qPP C + qPM C + qMP C + qMM C

fourSignM2 :
  FourSignR571SecondMomentCell → ℚ
fourSignM2 C =
  Moment.weightedSecondMoment (sPP C)
  + Moment.weightedSecondMoment (sPM C)
  + Moment.weightedSecondMoment (sMP C)
  + Moment.weightedSecondMoment (sMM C)

fourSignScalarBelowPairedMagnitudes :
  (C : FourSignR571SecondMomentCell) →
  fourSignScalar C
  ≤
  Moment.pairedMagnitude (sPP C)
  + Moment.pairedMagnitude (sPM C)
  + Moment.pairedMagnitude (sMP C)
  + Moment.pairedMagnitude (sMM C)
fourSignScalarBelowPairedMagnitudes C =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (qPPBelowMagnitude C)
        (qPMBelowMagnitude C))
      (qMPBelowMagnitude C))
    (qMMBelowMagnitude C)

fourSignPairedMagnitudesBelowM2 :
  (C : FourSignR571SecondMomentCell) →
  Moment.pairedMagnitude (sPP C)
    + Moment.pairedMagnitude (sPM C)
    + Moment.pairedMagnitude (sMP C)
    + Moment.pairedMagnitude (sMM C)
  ≤
  Preferred.preferredCoefficient (budget C) * fourSignM2 C
fourSignPairedMagnitudesBelowM2 C =
  let
    summed =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (ppPreferred C)
            (pmPreferred C))
          (mpPreferred C))
        (mmPreferred C)

    target =
      solve
        ( Preferred.preferredCoefficient (budget C)
        ∷ Moment.weightedSecondMoment (sPP C)
        ∷ Moment.weightedSecondMoment (sPM C)
        ∷ Moment.weightedSecondMoment (sMP C)
        ∷ Moment.weightedSecondMoment (sMM C)
        ∷ [])
  in
  subst
    (λ rhs →
      Moment.pairedMagnitude (sPP C)
        + Moment.pairedMagnitude (sPM C)
        + Moment.pairedMagnitude (sMP C)
        + Moment.pairedMagnitude (sMM C)
      ≤ rhs)
    target
    summed

fourSignR573CellBelowPreferredM2 :
  (C : FourSignR571SecondMomentCell) →
  fourSignScalar C
  ≤
  Preferred.preferredCoefficient (budget C) * fourSignM2 C
fourSignR573CellBelowPreferredM2 C =
  ℚP.≤-trans
    (fourSignScalarBelowPairedMagnitudes C)
    (fourSignPairedMagnitudesBelowM2 C)

fourSignSecondMomentAggregationClosed : Bool
fourSignSecondMomentAggregationClosed = true

r573VectorChannelsScalarizedToTheseSamplesHere : Bool
r573VectorChannelsScalarizedToTheseSamplesHere = false

positiveRecombinationOccursOnlyAfterSignedChannelSplit : Bool
positiveRecombinationOccursOnlyAfterSignedChannelSplit = true

clayPromotion : Bool
clayPromotion = false

fourSignSecondMomentAggregationClosedIsTrue :
  fourSignSecondMomentAggregationClosed ≡ true
fourSignSecondMomentAggregationClosedIsTrue = refl

positiveRecombinationOccursOnlyAfterSignedChannelSplitIsTrue :
  positiveRecombinationOccursOnlyAfterSignedChannelSplit ≡ true
positiveRecombinationOccursOnlyAfterSignedChannelSplitIsTrue = refl
