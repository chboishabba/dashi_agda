module DASHI.Physics.YangMills.BalabanCMP109MinimalScaleDerivativeBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Correct a quantitatively important scale mismatch in the local Gate-I route.
-- The source hypothesis preceding CMP109 equation (0.1) requires an odd
-- blocking factor L > 11.  The repository's literal minimal source-admissible
-- realization is therefore
--
--   L = 13, |B| = 13^4 = 28561.
--
-- A Lie(SU(2))-valued four-dimensional bond field on one such block has
--
--   3 * 4 * 28561 = 342732
--
-- scalar state coordinates, not the 3072 coordinates of the side-four test
-- carrier.  Consequently the old blanket pointwise reference-entry estimate
-- rho = 1/8192 cannot simply be reused with the same rectangular Schur proof:
-- its two-background coefficient would be
--
--   12 * 342732 * (2/8192)^2
--     = 257049/1048576
--     > 3711/262144,
--
-- so it misses the nonlinear block-average IFT budget by a wide margin.
--
-- This module proves that no-go arithmetically and gives a conservative repair.
-- A scale-13 pointwise reference-entry bound
--
--   rho_13 = 1/65536
--
-- implies, by the same square-root-free rectangular Schur argument,
--
--   ||(DQ_U-DQ_A)h||^2
--     <= 257049/67108864 ||h||^2
--     < 3711/262144 ||h||^2,
--
-- with exact slack 692967/67108864.
--
-- This does not assert that 1/65536 is sharp.  In the literal equation-(0.12)
-- derivative the block weight 1/28561 and contour incidence should permit a
-- substantially better source-specific estimate.  The theorem establishes the
-- exact quantitative target that any same-object L=13 proof must beat, and
-- prevents an invalid side-four-to-CMP109 identification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanFiniteFibreAverageExact as Fibre
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanSelectedGaugeDerivativeTwoBackgroundVariationExact as GaugeVariation
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

minimalBlockSiteCount minimalStateCoordinateCount averageRowCount : ℚ
minimalBlockSiteCount = + 28561 / 1
minimalStateCoordinateCount = + 342732 / 1
averageRowCount = + 12 / 1

sourceMinimalSideExact : Minimal.side ≡ 13
sourceMinimalSideExact = refl

sourceMinimalVolumeExact : Minimal.volume ≡ 28561
sourceMinimalVolumeExact = refl

------------------------------------------------------------------------
-- The old side-four blanket radius is not scale-safe under a full dense Schur
-- count at L=13.
------------------------------------------------------------------------

oldReferenceEntryRadius : ℚ
oldReferenceEntryRadius = + 1 / 8192

oldTwoBackgroundEntryRadius : ℚ
oldTwoBackgroundEntryRadius = + 1 / 4096

oldMinimalDenseSchurCoefficient : ℚ
oldMinimalDenseSchurCoefficient = + 257049 / 1048576

oldMinimalDenseCoefficientExact :
  averageRowCount * minimalStateCoordinateCount
    * (oldTwoBackgroundEntryRadius * oldTwoBackgroundEntryRadius)
  ≡ oldMinimalDenseSchurCoefficient
oldMinimalDenseCoefficientExact = ℚRing.solve []

oldMinimalDenseBudgetFails :
  GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
  < oldMinimalDenseSchurCoefficient
oldMinimalDenseBudgetFails =
  toWitness
    {a? = GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      <? oldMinimalDenseSchurCoefficient} _

------------------------------------------------------------------------
-- Conservative source-admissible replacement target.
------------------------------------------------------------------------

minimalSafeReferenceEntryRadius : ℚ
minimalSafeReferenceEntryRadius = + 1 / 65536

minimalSafeTwoBackgroundRadius : ℚ
minimalSafeTwoBackgroundRadius = + 1 / 32768

minimalSafeRowMass : ℚ
minimalSafeRowMass = + 85683 / 8192

minimalSafeColumnMass : ℚ
minimalSafeColumnMass = + 3 / 8192

minimalSafeSchurSquaredCoefficient : ℚ
minimalSafeSchurSquaredCoefficient = + 257049 / 67108864

minimalSafeBudgetSlack : ℚ
minimalSafeBudgetSlack = + 692967 / 67108864

minimalSafeRowMassExact :
  minimalStateCoordinateCount * minimalSafeTwoBackgroundRadius
  ≡ minimalSafeRowMass
minimalSafeRowMassExact = ℚRing.solve []

minimalSafeColumnMassExact :
  averageRowCount * minimalSafeTwoBackgroundRadius
  ≡ minimalSafeColumnMass
minimalSafeColumnMassExact = ℚRing.solve []

minimalSafeSchurCoefficientExact :
  minimalSafeRowMass * minimalSafeColumnMass
  ≡ minimalSafeSchurSquaredCoefficient
minimalSafeSchurCoefficientExact = ℚRing.solve []

minimalSafeCoefficientPlusSlackExact :
  minimalSafeSchurSquaredCoefficient + minimalSafeBudgetSlack
  ≡ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
minimalSafeCoefficientPlusSlackExact = ℚRing.solve []

minimalSafeBudgetSlackNonnegative : 0ℚ ≤ minimalSafeBudgetSlack
minimalSafeBudgetSlackNonnegative =
  toWitness {a? = 0ℚ ≤? minimalSafeBudgetSlack} _

minimalSafeSchurFitsIFTBudget :
  minimalSafeSchurSquaredCoefficient
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
minimalSafeSchurFitsIFTBudget =
  subst
    (λ upper → minimalSafeSchurSquaredCoefficient ≤ upper)
    minimalSafeCoefficientPlusSlackExact
    (subst
      (λ lower → lower
        ≤ minimalSafeSchurSquaredCoefficient + minimalSafeBudgetSlack)
      (sym (ℚP.+-identityʳ minimalSafeSchurSquaredCoefficient))
      (ℚP.+-mono-≤ ℚP.≤-refl minimalSafeBudgetSlackNonnegative))

absoluteDifferenceBelowSafeTwoRadius : ∀ left right →
  ∣ left ∣ ≤ minimalSafeReferenceEntryRadius →
  ∣ right ∣ ≤ minimalSafeReferenceEntryRadius →
  ∣ left - right ∣ ≤ minimalSafeTwoBackgroundRadius
absoluteDifferenceBelowSafeTwoRadius left right leftBound rightBound =
  let
    rewriteDifference : left - right ≡ left + (- right)
    rewriteDifference = ℚRing.solve []
    triangle = ℚP.∣p+q∣≤∣p∣+∣q∣ left (- right)
    removeNeg : ∣ left ∣ + ∣ - right ∣ ≡ ∣ left ∣ + ∣ right ∣
    removeNeg = cong (∣ left ∣ +_) (ℚP.∣-p∣≡∣p∣ right)
    bounded = ℚP.+-mono-≤ leftBound rightBound
    radiusExact :
      minimalSafeReferenceEntryRadius + minimalSafeReferenceEntryRadius
      ≡ minimalSafeTwoBackgroundRadius
    radiusExact = ℚRing.solve []
  in
  subst
    (λ lower → lower ≤ minimalSafeTwoBackgroundRadius)
    (sym (cong ∣_∣ rewriteDifference))
    (ℚP.≤-trans triangle
      (subst
        (λ lower → lower ≤ minimalSafeTwoBackgroundRadius)
        (sym removeNeg)
        (subst
          (λ upper → ∣ left ∣ + ∣ right ∣ ≤ upper)
          radiusExact bounded)))

------------------------------------------------------------------------
-- Generic literal carrier theorem.  Any actual L=13 selected carrier only has
-- to supply its complete row/column lists and their source-forced counts.
------------------------------------------------------------------------

minimalScaleTwoBackgroundSchur :
  ∀ {Row Column : Set}
    (rows : List Row) (columns : List Column)
    (left right : Row → Column → ℚ)
    (vector : Column → ℚ) →
  length rows ≡ 12 →
  length columns ≡ 342732 →
  (∀ row column → ∣ left row column ∣ ≤ minimalSafeReferenceEntryRadius) →
  (∀ row column → ∣ right row column ∣ ≤ minimalSafeReferenceEntryRadius) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (λ row column → left row column - right row column)
      vector)
  ≤ minimalSafeSchurSquaredCoefficient
      * RectSchur.rectVectorNormSq columns vector
minimalScaleTwoBackgroundSchur
    rows columns left right vector rowCount columnCount leftBound rightBound =
  let
    matrix : _
    matrix = λ row column → left row column - right row column

    pointwise : ∀ row column →
      ∣ matrix row column ∣ ≤ minimalSafeTwoBackgroundRadius
    pointwise row column =
      absoluteDifferenceBelowSafeTwoRadius
        (left row column) (right row column)
        (leftBound row column) (rightBound row column)

    rowMass : ∀ row →
      RectSchur.rectAbsoluteRowMass columns matrix row ≤ minimalSafeRowMass
    rowMass row =
      let
        summed = Schur.sumPointwiseBelow columns
          (λ column → ∣ matrix row column ∣)
          (λ _ → minimalSafeTwoBackgroundRadius)
          (pointwise row)
        constantExact = Fibre.sumRationalConstant
          columns minimalSafeTwoBackgroundRadius
        countScale :
          Fibre.natAsRational (length columns)
            * minimalSafeTwoBackgroundRadius
          ≡ minimalSafeRowMass
        countScale rewrite columnCount = ℚRing.solve []
      in
      subst
        (λ upper → RectSchur.rectAbsoluteRowMass columns matrix row ≤ upper)
        (trans constantExact countScale)
        summed

    columnMass : ∀ column →
      RectSchur.rectAbsoluteColumnMass rows matrix column ≤ minimalSafeColumnMass
    columnMass column =
      let
        summed = Schur.sumPointwiseBelow rows
          (λ row → ∣ matrix row column ∣)
          (λ _ → minimalSafeTwoBackgroundRadius)
          (λ row → pointwise row column)
        constantExact = Fibre.sumRationalConstant
          rows minimalSafeTwoBackgroundRadius
        countScale :
          Fibre.natAsRational (length rows)
            * minimalSafeTwoBackgroundRadius
          ≡ minimalSafeColumnMass
        countScale rewrite rowCount = ℚRing.solve []
      in
      subst
        (λ upper → RectSchur.rectAbsoluteColumnMass rows matrix column ≤ upper)
        (trans constantExact countScale)
        summed

    schur = RectSchur.finiteRectangularSchurSquared
      rows columns matrix vector minimalSafeRowMass minimalSafeColumnMass
      (toWitness {a? = 0ℚ ≤? minimalSafeRowMass} _)
      (toWitness {a? = 0ℚ ≤? minimalSafeColumnMass} _)
      rowMass columnMass
  in
  subst
    (λ coefficient →
      RectSchur.rectVectorNormSq rows (RectSchur.rectApply columns matrix vector)
      ≤ coefficient * RectSchur.rectVectorNormSq columns vector)
    minimalSafeSchurCoefficientExact
    schur

minimalScaleTwoBackgroundFitsIFTBudget :
  ∀ {Row Column : Set}
    (rows : List Row) (columns : List Column)
    (left right : Row → Column → ℚ)
    (vector : Column → ℚ) →
  length rows ≡ 12 →
  length columns ≡ 342732 →
  (∀ row column → ∣ left row column ∣ ≤ minimalSafeReferenceEntryRadius) →
  (∀ row column → ∣ right row column ∣ ≤ minimalSafeReferenceEntryRadius) →
  RectSchur.rectVectorNormSq rows
    (RectSchur.rectApply columns
      (λ row column → left row column - right row column)
      vector)
  ≤ GaugeVariation.blockAverageDerivativeRemainingSquaredBudget
      * RectSchur.rectVectorNormSq columns vector
minimalScaleTwoBackgroundFitsIFTBudget
    rows columns left right vector rowCount columnCount leftBound rightBound =
  let
    base = minimalScaleTwoBackgroundSchur
      rows columns left right vector rowCount columnCount leftBound rightBound
    norm = RectSchur.rectVectorNormSq columns vector
    normNonnegative = Schur.sumNonnegative columns _
      (λ column → FiniteL2.squareNonnegative (vector column))
    instance
      normNN : NonNegative norm
      normNN = ℚ.nonNegative normNonnegative
  in
  ℚP.≤-trans base
    (ℚP.*-monoʳ-≤-nonNeg norm minimalSafeSchurFitsIFTBudget)

cmp109MinimalScaleMismatchNoGoLevel : ProofLevel
cmp109MinimalScaleMismatchNoGoLevel = machineChecked

cmp109MinimalScaleSafeBlanketBudgetLevel : ProofLevel
cmp109MinimalScaleSafeBlanketBudgetLevel = machineChecked

cmp109MinimalScaleWeightedSourceImprovementLevel : ProofLevel
cmp109MinimalScaleWeightedSourceImprovementLevel = conditional
