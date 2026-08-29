module DASHI.Physics.Closure.NSTriadKNRawCurlCellMassEnergyDissipationRound217Exact where

------------------------------------------------------------------------
-- ROUND217 / RAW-CURL CELL MASS -> ENERGY-DISSIPATION PRODUCT
--
-- Round178 gives the pointwise physical raw-curl estimate
--
--   M_pq <= 9 |k|^2 E_p E_q.
--
-- On a resonant pair k=p+q the Euclidean square triangle estimate has the
-- radical-free form
--
--   |k|^2 <= 2 (|p|^2 + |q|^2).
--
-- Therefore
--
--   M_pq <= 18 ((|p|^2 E_p) E_q + E_p (|q|^2 E_q)).
--
-- The right hand side is exactly eighteen times the Round109 modal
-- energy-dissipation pair kernel.  Hence after any physical Boolean selector,
-- Round109's no-cardinality selected-pair theorem gives
--
--   sum M_pq <= 36 E D.
--
-- This pays the INCOHERENT / cell-mass portion of the quartic companion with
-- the ordinary energy-dissipation product.  It does not pay coherent Gram
-- covariance; that remains the genuine signed-network leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178

 two eighteen thirtySix : ℚ
 two = 1ℚ + 1ℚ
 eighteen = R178.nine * two
 thirtySix = eighteen * two

 twoNN : 0ℚ ≤ two
 twoNN = Rational.addNonnegative R178.oneNN R178.oneNN

 eighteenNN : 0ℚ ≤ eighteen
 eighteenNN = R178.R96.productNonnegative R178.threeNN R178.threeNN
   |> λ nineNN → R178.R96.productNonnegative nineNN twoNN
   where
   infixl 0 _|>_
   _|>_ : ∀ {a b : Set} → a → (a → b) → b
   x |> f = f x

record RawCellRadialData : Set where
  constructor raw-cell-radial-data
  field
    cellMass outputSquare pSquare qSquare energyP energyQ : ℚ
    cellMassNN : 0ℚ ≤ cellMass
    outputSquareNN : 0ℚ ≤ outputSquare
    pSquareNN : 0ℚ ≤ pSquare
    qSquareNN : 0ℚ ≤ qSquare
    energyPNN : 0ℚ ≤ energyP
    energyQNN : 0ℚ ≤ energyQ

    rawCurlMassBound :
      cellMass ≤ R178.nine * outputSquare * energyP * energyQ

    resonantSquareTriangle :
      outputSquare ≤ two * (pSquare + qSquare)

open RawCellRadialData public

pairEDKernel : RawCellRadialData → ℚ
pairEDKernel C =
  (pSquare C * energyP C) * energyQ C
  + energyP C * (qSquare C * energyQ C)

rawCellMassBelowEighteenEDKernel :
  (C : RawCellRadialData) →
  cellMass C ≤ eighteen * pairEDKernel C
rawCellMassBelowEighteenEDKernel C =
  let
    pqNN : 0ℚ ≤ pSquare C + qSquare C
    pqNN = Rational.addNonnegative (pSquareNN C) (qSquareNN C)

    radialUpperNN : 0ℚ ≤ two * (pSquare C + qSquare C)
    radialUpperNN = R178.R96.productNonnegative twoNN pqNN

    firstScale :
      outputSquare C * energyP C
      ≤ (two * (pSquare C + qSquare C)) * energyP C
    firstScale =
      Rational.nonnegativeProductMonotone
        (outputSquareNN C) (energyPNN C)
        radialUpperNN (energyPNN C)
        (resonantSquareTriangle C) ℚP.≤-refl

    leftNN : 0ℚ ≤ outputSquare C * energyP C
    leftNN = R178.R96.productNonnegative (outputSquareNN C) (energyPNN C)

    rightNN : 0ℚ ≤ (two * (pSquare C + qSquare C)) * energyP C
    rightNN = R178.R96.productNonnegative radialUpperNN (energyPNN C)

    secondScale :
      (outputSquare C * energyP C) * energyQ C
      ≤ ((two * (pSquare C + qSquare C)) * energyP C) * energyQ C
    secondScale =
      Rational.nonnegativeProductMonotone
        leftNN (energyQNN C) rightNN (energyQNN C)
        firstScale ℚP.≤-refl

    nineNN : 0ℚ ≤ R178.nine
    nineNN = R178.R96.productNonnegative R178.threeNN R178.threeNN

    leftTripleNN :
      0ℚ ≤ (outputSquare C * energyP C) * energyQ C
    leftTripleNN = R178.R96.productNonnegative leftNN (energyQNN C)

    rightTripleNN :
      0ℚ ≤ ((two * (pSquare C + qSquare C)) * energyP C) * energyQ C
    rightTripleNN = R178.R96.productNonnegative rightNN (energyQNN C)

    scaled :
      R178.nine * ((outputSquare C * energyP C) * energyQ C)
      ≤ R178.nine * (((two * (pSquare C + qSquare C)) * energyP C) * energyQ C)
    scaled =
      Rational.nonnegativeProductMonotone
        nineNN leftTripleNN nineNN rightTripleNN
        ℚP.≤-refl secondScale

    rawMeaning :
      R178.nine * outputSquare C * energyP C * energyQ C
      ≡ R178.nine * ((outputSquare C * energyP C) * energyQ C)
    rawMeaning = solve
      (R178.nine ∷ outputSquare C ∷ energyP C ∷ energyQ C ∷ [])

    endpoint :
      R178.nine * (((two * (pSquare C + qSquare C)) * energyP C) * energyQ C)
      ≡ eighteen * pairEDKernel C
    endpoint = solve
      ( R178.nine ∷ two ∷ pSquare C ∷ qSquare C
      ∷ energyP C ∷ energyQ C ∷ [])
  in
  ℚP.≤-trans
    (rawCurlMassBound C)
    (subst
      (λ lower → lower ≤ eighteen * pairEDKernel C)
      rawMeaning
      (subst
        (λ upper →
          R178.nine * ((outputSquare C * energyP C) * energyQ C) ≤ upper)
        endpoint
        scaled))

record CellEDPayment : Set where
  constructor cell-ed-payment
  field
    mass kernel : ℚ
    massBound : mass ≤ eighteen * kernel

open CellEDPayment public

sumMass sumKernel : List CellEDPayment → ℚ
sumMass [] = 0ℚ
sumMass (C ∷ rest) = mass C + sumMass rest
sumKernel [] = 0ℚ
sumKernel (C ∷ rest) = kernel C + sumKernel rest

sumMassBelowEighteenKernel :
  (cells : List CellEDPayment) →
  sumMass cells ≤ eighteen * sumKernel cells
sumMassBelowEighteenKernel [] =
  subst (0ℚ ≤_) (solve (eighteen ∷ [])) ℚP.≤-refl
sumMassBelowEighteenKernel (C ∷ rest) =
  let
    summed = ℚP.+-mono-≤ (massBound C) (sumMassBelowEighteenKernel rest)
    endpoint :
      eighteen * kernel C + eighteen * sumKernel rest
      ≡ eighteen * sumKernel (C ∷ rest)
    endpoint = solve (eighteen ∷ kernel C ∷ sumKernel rest ∷ [])
  in
  subst
    (λ upper → sumMass (C ∷ rest) ≤ upper)
    endpoint summed

cellMassSumBelowThirtySixED :
  (cells : List CellEDPayment) →
  (energy dissipation : ℚ) →
  0ℚ ≤ sumKernel cells →
  0ℚ ≤ energy * dissipation →
  sumKernel cells ≤ energy * dissipation + energy * dissipation →
  sumMass cells ≤ thirtySix * (energy * dissipation)
cellMassSumBelowThirtySixED cells energy dissipation kernelNN edNN selectedPairBound =
  let
    twoEDNN : 0ℚ ≤ energy * dissipation + energy * dissipation
    twoEDNN = Rational.addNonnegative edNN edNN

    scaledKernel :
      eighteen * sumKernel cells
      ≤ eighteen * (energy * dissipation + energy * dissipation)
    scaledKernel =
      Rational.nonnegativeProductMonotone
        eighteenNN kernelNN eighteenNN twoEDNN
        ℚP.≤-refl selectedPairBound

    endpoint :
      eighteen * (energy * dissipation + energy * dissipation)
      ≡ thirtySix * (energy * dissipation)
    endpoint = solve (eighteen ∷ energy ∷ dissipation ∷ [])
  in
  ℚP.≤-trans
    (sumMassBelowEighteenKernel cells)
    (subst
      (λ upper → eighteen * sumKernel cells ≤ upper)
      endpoint scaledKernel)

round217RawCellMassToEDKernelClosed : Bool
round217RawCellMassToEDKernelClosed = true

round217SelectedCellMassNoCardinalityTaxClosed : Bool
round217SelectedCellMassNoCardinalityTaxClosed = true

round217CellMassPortionOfQuarticCompanionPaid : Bool
round217CellMassPortionOfQuarticCompanionPaid = true

round217CoherentGramResidualPaid : Bool
round217CoherentGramResidualPaid = false

round217PackageAClosed : Bool
round217PackageAClosed = false

round217ClayPromotion : Bool
round217ClayPromotion = false

round217RawCellMassToEDKernelClosedIsTrue :
  round217RawCellMassToEDKernelClosed ≡ true
round217RawCellMassToEDKernelClosedIsTrue = refl

round217SelectedCellMassNoCardinalityTaxClosedIsTrue :
  round217SelectedCellMassNoCardinalityTaxClosed ≡ true
round217SelectedCellMassNoCardinalityTaxClosedIsTrue = refl

round217CoherentGramResidualPaidIsFalse :
  round217CoherentGramResidualPaid ≡ false
round217CoherentGramResidualPaidIsFalse = refl

round217PackageAClosedIsFalse : round217PackageAClosed ≡ false
round217PackageAClosedIsFalse = refl

round217ClayPromotionIsFalse : round217ClayPromotion ≡ false
round217ClayPromotionIsFalse = refl
