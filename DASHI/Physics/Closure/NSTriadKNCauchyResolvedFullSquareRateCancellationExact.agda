{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact where

------------------------------------------------------------------------
-- CAUCHY-RESOLVED FULL-SQUARE RATE CANCELLATION
--
-- If a symmetric pair kernel K satisfies
--
--   K(i,j) * (r(i) + r(j)) = 1,
--
-- then for every scalar pair observable G,
--
--   sum_{i,j} K(i,j) * (r(i)+r(j)) * G(i,j)
--     = sum_{i,j} G(i,j).
--
-- This is the exact algebraic cancellation carried by the nonseparable
-- R406/R538 Cauchy denominator.  It is finite algebra only: no sign, norm,
-- spacetime bound, Schur estimate or Navier--Stokes estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

------------------------------------------------------------------------
-- Generic finite full-square theorem.
------------------------------------------------------------------------

resolvedRateAtom :
  ∀ {A : Set} →
  (A → A → ℚ) →
  (A → ℚ) →
  (A → A → ℚ) →
  A → A → ℚ
resolvedRateAtom kernel rate observable i j =
  kernel i j * (rate i + rate j) * observable i j

resolvedRateAtomCancels :
  ∀ {A : Set}
    (kernel : A → A → ℚ)
    (rate : A → ℚ)
    (observable : A → A → ℚ) →
  ((i j : A) → kernel i j * (rate i + rate j) ≡ 1ℚ) →
  (i j : A) →
  resolvedRateAtom kernel rate observable i j ≡ observable i j
resolvedRateAtomCancels kernel rate observable law i j
  rewrite law i j =
  solve (observable i j ∷ [])

rowCongruent :
  ∀ {A : Set}
    (F G : A → A → ℚ) →
  ((i j : A) → F i j ≡ G i j) →
  (i : A) (items : List A) →
  R539.rowSum F i items ≡ R539.rowSum G i items
rowCongruent F G pointwise i [] = refl
rowCongruent F G pointwise i (j ∷ rest) =
  cong₂ _+_ (pointwise i j) (rowCongruent F G pointwise i rest)

columnCongruent :
  ∀ {A : Set}
    (F G : A → A → ℚ) →
  ((i j : A) → F i j ≡ G i j) →
  (items : List A) (j : A) →
  R539.columnSum F items j ≡ R539.columnSum G items j
columnCongruent F G pointwise [] j = refl
columnCongruent F G pointwise (i ∷ rest) j =
  cong₂ _+_ (pointwise i j) (columnCongruent F G pointwise rest j)

fullSquareCongruent :
  ∀ {A : Set}
    (F G : A → A → ℚ) →
  ((i j : A) → F i j ≡ G i j) →
  (items : List A) →
  R543.fullSquareSum F items ≡ R543.fullSquareSum G items
fullSquareCongruent F G pointwise [] = refl
fullSquareCongruent F G pointwise (i ∷ rest)
  rewrite pointwise i i
        | rowCongruent F G pointwise i rest
        | columnCongruent F G pointwise rest i
        | fullSquareCongruent F G pointwise rest = refl

cauchyResolvedFullSquareRateCancellation :
  ∀ {A : Set}
    (kernel : A → A → ℚ)
    (rate : A → ℚ)
    (observable : A → A → ℚ)
    (items : List A) →
  ((i j : A) → kernel i j * (rate i + rate j) ≡ 1ℚ) →
  R543.fullSquareSum
    (resolvedRateAtom kernel rate observable) items
  ≡ R543.fullSquareSum observable items
cauchyResolvedFullSquareRateCancellation kernel rate observable items law =
  fullSquareCongruent
    (resolvedRateAtom kernel rate observable)
    observable
    (resolvedRateAtomCancels kernel rate observable law)
    items

------------------------------------------------------------------------
-- Literal R538 physical-pair specialization.
------------------------------------------------------------------------

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalResolved
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  cellRate : Physical.PhysicalTriadIncidence → ℚ
  cellRate = Pair.D.Pair.cellRate

  physicalPairResolventLaw :
    (positive :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive (R291.pairRate (Swap.Q alpha beta))) →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Swap.pairResolvent alpha beta
      * (cellRate alpha + cellRate beta)
    ≡ 1ℚ
  physicalPairResolventLaw positive alpha beta =
    Reciprocal.safeRationalReciprocalTimesPositive
      (R291.pairRate (Swap.Q alpha beta))
      (positive alpha beta)

  physicalCauchyFullSquareRateCancellation :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Positive (R291.pairRate (Swap.Q alpha beta))) →
    (observable :
      Physical.PhysicalTriadIncidence →
      Physical.PhysicalTriadIncidence → ℚ) →
    R543.fullSquareSum
      (resolvedRateAtom Swap.pairResolvent cellRate observable) items
    ≡ R543.fullSquareSum observable items
  physicalCauchyFullSquareRateCancellation items positive observable =
    cauchyResolvedFullSquareRateCancellation
      Swap.pairResolvent
      cellRate
      observable
      items
      (physicalPairResolventLaw positive)

  module OnNonzeroOutput
      (viscosityPositive : Positive (Field30.viscosity physicalSystem))
      (output : Z3.FourierMode)
      (outputNonzero :
        Z3.NonZeroMode output) where

    module Rate = R400.PhysicalRate physicalSystem S viscosityPositive

    physicalPairResolventLawOnOutput :
      (alpha beta : Physical.PhysicalTriadIncidence) →
      Physical.k alpha ≡ output →
      Physical.k beta ≡ output →
      Swap.pairResolvent alpha beta
        * (cellRate alpha + cellRate beta)
      ≡ 1ℚ
    physicalPairResolventLawOnOutput alpha beta alphaOutput betaOutput =
      let
        alphaPositive =
          Rate.cellRatePositiveFromNonzeroOutput
            output outputNonzero alpha alphaOutput
        betaPositive =
          Rate.cellRatePositiveFromNonzeroOutput
            output outputNonzero beta betaOutput
        pairPositive =
          Rate.pairRatePositiveFromCellRates
            alpha beta alphaPositive betaPositive
      in
      Reciprocal.safeRationalReciprocalTimesPositive
        (R291.pairRate (Swap.Q alpha beta))
        pairPositive

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

cauchyResolvedFullSquareRateCancellationClosed : Bool
cauchyResolvedFullSquareRateCancellationClosed = true

literalR538PairResolventRateCancellationClosed : Bool
literalR538PairResolventRateCancellationClosed = true

literalNonzeroOutputPairResolventRateCancellationClosed : Bool
literalNonzeroOutputPairResolventRateCancellationClosed = true

cauchyCancellationIntroducesEstimate : Bool
cauchyCancellationIntroducesEstimate = false

cauchyCancellationClosesR568 : Bool
cauchyCancellationClosesR568 = false

cauchyCancellationUsesAbsoluteValue : Bool
cauchyCancellationUsesAbsoluteValue = false

cauchyResolvedFullSquareRateCancellationClosedIsTrue :
  cauchyResolvedFullSquareRateCancellationClosed ≡ true
cauchyResolvedFullSquareRateCancellationClosedIsTrue = refl

literalR538PairResolventRateCancellationClosedIsTrue :
  literalR538PairResolventRateCancellationClosed ≡ true
literalR538PairResolventRateCancellationClosedIsTrue = refl

literalNonzeroOutputPairResolventRateCancellationClosedIsTrue :
  literalNonzeroOutputPairResolventRateCancellationClosed ≡ true
literalNonzeroOutputPairResolventRateCancellationClosedIsTrue = refl

cauchyCancellationIntroducesEstimateIsFalse :
  cauchyCancellationIntroducesEstimate ≡ false
cauchyCancellationIntroducesEstimateIsFalse = refl

cauchyCancellationClosesR568IsFalse :
  cauchyCancellationClosesR568 ≡ false
cauchyCancellationClosesR568IsFalse = refl
