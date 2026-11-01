module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierParsevalFromInversionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Prove finite Parseval from the normalized coefficient definition and finite
-- Fourier inversion.  The proof is valid for arbitrary finite point and mode
-- lists over the rational carrier:
--
--   fhat(k) = c sum_x f(x) chi(k,x),
--   f(x)    = sum_k fhat(k) chi(k,x).
--
-- It derives
--
--   sum_k fhat(k)^2 = c sum_x f(x)^2
--
-- by finite distributivity and interchange of the two sums.  Thus Parseval is
-- not a separate field once inversion has been constructed from character
-- orthogonality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_) 
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

sumBy : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

sumByCong :
  ∀ {A : Set}
    (items : List A)
    (first second : A → ℚ) →
  ((item : A) → first item ≡ second item) →
  sumBy items first ≡ sumBy items second
sumByCong [] first second pointwise = refl
sumByCong (item ∷ items) first second pointwise
  rewrite pointwise item
        | sumByCong items first second pointwise =
  refl

sumByZero :
  ∀ {A : Set} (items : List A) →
  sumBy items (λ _ → 0ℚ) ≡ 0ℚ
sumByZero [] = refl
sumByZero (_ ∷ items)
  rewrite sumByZero items =
  solve []

sumByAdd :
  ∀ {A : Set}
    (items : List A)
    (first second : A → ℚ) →
  sumBy items (λ item → first item + second item)
  ≡ sumBy items first + sumBy items second
sumByAdd [] first second = solve []
sumByAdd (item ∷ items) first second
  rewrite sumByAdd items first second =
  solve
    ( first item ∷ second item
    ∷ sumBy items first ∷ sumBy items second ∷ [])

sumByScaleLeft :
  ∀ {A : Set}
    (scale : ℚ)
    (items : List A)
    (value : A → ℚ) →
  sumBy items (λ item → scale * value item)
  ≡ scale * sumBy items value
sumByScaleLeft scale [] value = solve []
sumByScaleLeft scale (item ∷ items) value
  rewrite sumByScaleLeft scale items value =
  solve (scale ∷ value item ∷ sumBy items value ∷ [])

sumByScaleRight :
  ∀ {A : Set}
    (items : List A)
    (value : A → ℚ)
    (scale : ℚ) →
  sumBy items (λ item → value item * scale)
  ≡ sumBy items value * scale
sumByScaleRight [] value scale = solve []
sumByScaleRight (item ∷ items) value scale
  rewrite sumByScaleRight items value scale =
  solve (value item ∷ sumBy items value ∷ scale ∷ [])

sumSwap :
  ∀ {A B : Set}
    (first : List A)
    (second : List B)
    (value : A → B → ℚ) →
  sumBy first (λ a → sumBy second (value a))
  ≡ sumBy second (λ b → sumBy first (λ a → value a b))
sumSwap [] second value =
  sym (sumByZero second)
sumSwap (a ∷ first) second value =
  let
    ih = sumSwap first second value

    leftExpanded :
      sumBy second (value a)
        + sumBy first (λ next → sumBy second (value next))
      ≡ sumBy second (value a)
        + sumBy second (λ b → sumBy first (λ next → value next b))
    leftExpanded = cong (sumBy second (value a) +_) ih

    combine :
      sumBy second (value a)
        + sumBy second (λ b → sumBy first (λ next → value next b))
      ≡ sumBy second
          (λ b → value a b + sumBy first (λ next → value next b))
    combine =
      sym
        (sumByAdd
          second
          (value a)
          (λ b → sumBy first (λ next → value next b)))
  in
  trans leftExpanded combine

square : ℚ → ℚ
square value = value * value

record FiniteFourierInversionData (Point Mode : Set) : Set₁ where
  constructor finite-fourier-inversion-data
  field
    points : List Point
    modes : List Mode
    normalization : ℚ
    signal : Point → ℚ
    character : Mode → Point → ℚ

open FiniteFourierInversionData public

rawCoefficient :
  ∀ {Point Mode : Set} →
  FiniteFourierInversionData Point Mode →
  Mode → ℚ
rawCoefficient dataSet mode =
  sumBy (points dataSet)
    (λ point → signal dataSet point * character dataSet mode point)

coefficient :
  ∀ {Point Mode : Set} →
  FiniteFourierInversionData Point Mode →
  Mode → ℚ
coefficient dataSet mode =
  normalization dataSet * rawCoefficient dataSet mode

record CompleteFiniteFourierData (Point Mode : Set) : Set₁ where
  constructor complete-finite-fourier-data
  field
    inversionData : FiniteFourierInversionData Point Mode
    inversion :
      (point : Point) →
      sumBy (modes inversionData)
        (λ mode →
          coefficient inversionData mode
          * character inversionData mode point)
      ≡ signal inversionData point

open CompleteFiniteFourierData public

physicalL2Squared :
  ∀ {Point Mode : Set} →
  CompleteFiniteFourierData Point Mode → ℚ
physicalL2Squared dataSet =
  normalization (inversionData dataSet)
  * sumBy (points (inversionData dataSet))
      (λ point → square (signal (inversionData dataSet) point))

fourierL2Squared :
  ∀ {Point Mode : Set} →
  CompleteFiniteFourierData Point Mode → ℚ
fourierL2Squared dataSet =
  sumBy (modes (inversionData dataSet))
    (λ mode → square (coefficient (inversionData dataSet) mode))

finiteParsevalFromInversion :
  ∀ {Point Mode : Set}
    (dataSet : CompleteFiniteFourierData Point Mode) →
  fourierL2Squared dataSet ≡ physicalL2Squared dataSet
finiteParsevalFromInversion dataSet =
  let
    data = inversionData dataSet

    coefficientSquareExpand :
      (mode : Mode) →
      square (coefficient data mode)
      ≡ normalization data
        * sumBy (points data)
            (λ point →
              coefficient data mode
              * (signal data point * character data mode point))
    coefficientSquareExpand mode =
      let
        scaledSum =
          sumByScaleLeft
            (coefficient data mode)
            (points data)
            (λ point → signal data point * character data mode point)
      in
      trans
        (solve
          ( normalization data
          ∷ rawCoefficient data mode
          ∷ []))
        (trans
          (cong (normalization data *_)
            (sym scaledSum))
          (sumByCong
            (points data)
            (λ point →
              normalization data
              * (coefficient data mode
                * (signal data point * character data mode point)))
            (λ point →
              normalization data
              * (coefficient data mode
                * (signal data point * character data mode point)))
            (λ point → refl)))

    expandAll :
      fourierL2Squared dataSet
      ≡ sumBy (modes data)
          (λ mode →
            normalization data
            * sumBy (points data)
                (λ point →
                  coefficient data mode
                  * (signal data point * character data mode point)))
    expandAll =
      sumByCong
        (modes data)
        (λ mode → square (coefficient data mode))
        (λ mode →
          normalization data
          * sumBy (points data)
              (λ point →
                coefficient data mode
                * (signal data point * character data mode point)))
        coefficientSquareExpand

    factorNormalization :
      sumBy (modes data)
        (λ mode →
          normalization data
          * sumBy (points data)
              (λ point →
                coefficient data mode
                * (signal data point * character data mode point)))
      ≡ normalization data
        * sumBy (modes data)
            (λ mode →
              sumBy (points data)
                (λ point →
                  coefficient data mode
                  * (signal data point * character data mode point)))
    factorNormalization =
      sumByScaleLeft
        (normalization data)
        (modes data)
        (λ mode →
          sumBy (points data)
            (λ point →
              coefficient data mode
              * (signal data point * character data mode point)))

    swapSums :
      sumBy (modes data)
        (λ mode →
          sumBy (points data)
            (λ point →
              coefficient data mode
              * (signal data point * character data mode point)))
      ≡ sumBy (points data)
          (λ point →
            sumBy (modes data)
              (λ mode →
                coefficient data mode
                * (signal data point * character data mode point)))
    swapSums =
      sumSwap
        (modes data)
        (points data)
        (λ mode point →
          coefficient data mode
          * (signal data point * character data mode point))

    factorSignalAtPoint :
      (point : Point) →
      sumBy (modes data)
        (λ mode →
          coefficient data mode
          * (signal data point * character data mode point))
      ≡ signal data point
        * sumBy (modes data)
            (λ mode →
              coefficient data mode * character data mode point)
    factorSignalAtPoint point =
      trans
        (sumByCong
          (modes data)
          (λ mode →
            coefficient data mode
            * (signal data point * character data mode point))
          (λ mode →
            signal data point
            * (coefficient data mode * character data mode point))
          (λ mode →
            solve
              ( coefficient data mode
              ∷ signal data point
              ∷ character data mode point
              ∷ [])))
        (sumByScaleLeft
          (signal data point)
          (modes data)
          (λ mode → coefficient data mode * character data mode point))

    collapsePoint :
      (point : Point) →
      sumBy (modes data)
        (λ mode →
          coefficient data mode
          * (signal data point * character data mode point))
      ≡ square (signal data point)
    collapsePoint point =
      trans
        (factorSignalAtPoint point)
        (cong (signal data point *_)
          (inversion dataSet point))

    collapseAll :
      sumBy (points data)
        (λ point →
          sumBy (modes data)
            (λ mode →
              coefficient data mode
              * (signal data point * character data mode point)))
      ≡ sumBy (points data)
          (λ point → square (signal data point))
    collapseAll =
      sumByCong
        (points data)
        (λ point →
          sumBy (modes data)
            (λ mode →
              coefficient data mode
              * (signal data point * character data mode point)))
        (λ point → square (signal data point))
        collapsePoint
  in
  trans expandAll
    (trans factorNormalization
      (trans
        (cong (normalization data *_) swapSums)
        (cong (normalization data *_) collapseAll)))
