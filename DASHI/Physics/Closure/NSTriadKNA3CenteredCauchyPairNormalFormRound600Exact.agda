{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact where

------------------------------------------------------------------------
-- ROUND600 / CENTERED A3 + CAUCHY DYNAMIC RESIDUAL ON ONE FULL-SQUARE CARRIER
--
-- Generic finite algebra:
--
--   Full((r_a+r_b) G_ab) = 2 * Full(r_b G_ab)
--
-- whenever G is symmetric.
--
-- Literal specialization:
--
--   Full(r_b G_ab) = W(D,D_r),
--
-- where D=sum D_a and D_r=sum r_a D_a is exactly the physical rate-weighted
-- double-mixed/kernel fold used by R599.
--
-- Consequently R599 becomes the single full-square centered identity
--
--   32 A3
--     = Full((2R - n(r_a+r_b)) G_ab).
--
-- Likewise the remaining R598 discrepancy can be written as one complete
-- centered dynamic pair scalar:
--
--   2 Delta
--     = Full(2R K_ab T_ab + n(r_a+r_b)G_ab),
--
-- where
--
--   Delta = R * Full(KT) + n * W(D,D_r).
--
-- Using the exact R291 tangent law and K(r_a+r_b)=1, the same pair scalar is
--
--   2R K_ab N_ab + (n(r_a+r_b)-2R)G_ab.
--
-- No estimate, absolute value, division, lower separation, or PDE inequality
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullTransposeSymmetryRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNA3CenteredFullGramNormalFormRound599Exact as R599
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedR406GramTangentNormalFormExact as GramTangent

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic scalar full-square identities.
------------------------------------------------------------------------

leftRateGram :
  ∀ {A : Set} →
  (A → ℚ) → (A → A → ℚ) → A → A → ℚ
leftRateGram rate gram a b = rate a * gram a b

rightRateGram :
  ∀ {A : Set} →
  (A → ℚ) → (A → A → ℚ) → A → A → ℚ
rightRateGram rate gram a b = rate b * gram a b

pairRateGram :
  ∀ {A : Set} →
  (A → ℚ) → (A → A → ℚ) → A → A → ℚ
pairRateGram rate gram a b = (rate a + rate b) * gram a b

pairRateGramPointwise :
  ∀ {A : Set}
    (rate : A → ℚ)
    (gram : A → A → ℚ)
    (a b : A) →
  pairRateGram rate gram a b
  ≡ leftRateGram rate gram a b + rightRateGram rate gram a b
pairRateGramPointwise rate gram a b =
  solve (rate a ∷ rate b ∷ gram a b ∷ [])

leftRateGramIsTransposeRight :
  ∀ {A : Set}
    (rate : A → ℚ)
    (gram : A → A → ℚ) →
  ((a b : A) → gram a b ≡ gram b a) →
  (a b : A) →
  leftRateGram rate gram a b
  ≡ rightRateGram rate gram b a
leftRateGramIsTransposeRight rate gram symmetric a b =
  cong (rate a *_) (symmetric a b)

fullPairRateGramIsTwoRight :
  ∀ {A : Set}
    (rate : A → ℚ)
    (gram : A → A → ℚ) →
  ((a b : A) → gram a b ≡ gram b a) →
  (items : List A) →
  R543.fullSquareSum (pairRateGram rate gram) items
  ≡ R539.two * R543.fullSquareSum (rightRateGram rate gram) items
fullPairRateGramIsTwoRight rate gram symmetric items =
  let
    pointwise =
      Cauchy.fullSquareCongruent
        (pairRateGram rate gram)
        (λ a b →
          leftRateGram rate gram a b + rightRateGram rate gram a b)
        (pairRateGramPointwise rate gram)
        items

    split =
      GramTangent.fullSquareAdd
        (leftRateGram rate gram)
        (rightRateGram rate gram)
        items

    transpose =
      R566.fullSquareTransposeInvariant
        (leftRateGram rate gram)
        (rightRateGram rate gram)
        (leftRateGramIsTransposeRight rate gram symmetric)
        items
  in
  trans pointwise
    (trans split
      (trans
        (cong
          (_+ R543.fullSquareSum (rightRateGram rate gram) items)
          transpose)
        (solve
          (R543.fullSquareSum (rightRateGram rate gram) items ∷ []))))

centeredStaticPair :
  ∀ {A : Set} →
  ℚ → ℚ →
  (A → ℚ) → (A → A → ℚ) → A → A → ℚ
centeredStaticPair n rateTotal rate gram a b =
  (R539.two * rateTotal - n * (rate a + rate b)) * gram a b

centeredDynamicPair :
  ∀ {A : Set} →
  ℚ → ℚ →
  (A → ℚ) →
  (A → A → ℚ) →
  (A → A → ℚ) →
  (A → A → ℚ) →
  A → A → ℚ
centeredDynamicPair n rateTotal rate kernel gram tangent a b =
  R539.two * rateTotal * kernel a b * tangent a b
    + n * (rate a + rate b) * gram a b

centeredDynamicRemainderPair :
  ∀ {A : Set} →
  ℚ → ℚ →
  (A → ℚ) →
  (A → A → ℚ) →
  (A → A → ℚ) →
  (A → A → ℚ) →
  A → A → ℚ
centeredDynamicRemainderPair n rateTotal rate kernel gram remainder a b =
  R539.two * rateTotal * kernel a b * remainder a b
    + (n * (rate a + rate b) - R539.two * rateTotal) * gram a b

centeredDynamicPointwiseR291 :
  ∀ {A : Set}
    (n rateTotal : ℚ)
    (rate : A → ℚ)
    (kernel gram tangent remainder : A → A → ℚ) →
  ((a b : A) →
    tangent a b
    ≡ (0ℚ - (rate a + rate b)) * gram a b + remainder a b) →
  ((a b : A) → kernel a b * (rate a + rate b) ≡ 1) →
  (a b : A) →
  centeredDynamicPair n rateTotal rate kernel gram tangent a b
  ≡ centeredDynamicRemainderPair
      n rateTotal rate kernel gram remainder a b
centeredDynamicPointwiseR291
    n rateTotal rate kernel gram tangent remainder tangentLaw inverseLaw a b
  rewrite tangentLaw a b | inverseLaw a b =
  solve
    ( n ∷ rateTotal ∷ rate a ∷ rate b
    ∷ kernel a b ∷ gram a b ∷ remainder a b ∷ [])

------------------------------------------------------------------------
-- Literal fixed-output specialization.
------------------------------------------------------------------------

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (output : Z3.FourierMode) where

  module A3 = R599.FixedOutput physicalSystem S L H P output

  cutoff : Nat
  cutoff = A3.cutoff

  velocity = A3.velocity

  fibre : List Physical.PhysicalTriadIncidence
  fibre = A3.fibre

  doubleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  doubleCell = R225.doubleMixedCell S velocity

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = A3.rate

  gram :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  gram a b = Work.coherentWork (doubleCell a) (doubleCell b)

  rateScaledDouble :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  rateScaledDouble tau = R291.realScale (rate tau) (doubleCell tau)

  weightedKernelCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedKernelCell =
    RateKernel.weightedIQuadraticKernel
      (RateKernel.physicalRateWeight A3.rho) S velocity

  weightedKernelCellIsRateScaledDouble :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedKernelCell tau ≡ rateScaledDouble tau
  weightedKernelCellIsRateScaledDouble tau =
    trans
      (RateKernel.weightedIQuadraticKernelIsWeightedDoubleMixed
        P (RateKernel.physicalRateWeight A3.rho) tau)
      (sym
        (RateKernel.weightedDoubleMixedIsScaledDoubleMixed
          (RateKernel.physicalRateWeight A3.rho)
          S velocity tau))

  weightedKernelFoldIsRateScaledDoubleFold :
    R224.foldVector weightedKernelCell fibre
    ≡ R224.foldVector rateScaledDouble fibre
  weightedKernelFoldIsRateScaledDoubleFold =
    pointwise fibre
    where
    pointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector weightedKernelCell items
      ≡ R224.foldVector rateScaledDouble items
    pointwise [] = refl
    pointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (weightedKernelCellIsRateScaledDouble tau)
        (pointwise rest)

  rightRateGramPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  rightRateGramPair = rightRateGram rate gram

  rightRateGramRowFactors :
    (alpha : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R539.rowSum rightRateGramPair alpha items
    ≡ Work.coherentWork
        (doubleCell alpha)
        (R224.foldVector rateScaledDouble items)
  rightRateGramRowFactors alpha [] =
    sym (R597.workZeroRight (doubleCell alpha))
  rightRateGramRowFactors alpha (beta ∷ rest) =
    trans
      (cong
        (rightRateGramPair alpha beta +_)
        (rightRateGramRowFactors alpha rest))
      (trans
        (cong₂ _+_
          (Work.workScaleRight
            (rate beta) (doubleCell alpha) (doubleCell beta))
          refl)
        (sym
          (Work.workAddRight
            (doubleCell alpha)
            (rateScaledDouble beta)
            (R224.foldVector rateScaledDouble rest))))

  rightRateGramFullFactors :
    R543.fullSquareSum rightRateGramPair fibre
    ≡ Work.coherentWork
        (R224.foldVector doubleCell fibre)
        (R224.foldVector rateScaledDouble fibre)
  rightRateGramFullFactors =
    full fibre
    where
    full :
      (items : List Physical.PhysicalTriadIncidence) →
      R543.fullSquareSum rightRateGramPair items
      ≡ Work.coherentWork
          (R224.foldVector doubleCell items)
          (R224.foldVector rateScaledDouble items)
    full [] =
      sym (R597.workZeroLeft (C3.complex3Zero F))
    full (alpha ∷ rest)
      rewrite rightRateGramRowFactors alpha rest
            | full rest =
      let
        a = doubleCell alpha
        ar = rateScaledDouble alpha
        d = R224.foldVector doubleCell rest
        dr = R224.foldVector rateScaledDouble rest

        diag :
          rightRateGramPair alpha alpha
          ≡ Work.coherentWork a ar
        diag =
          Work.workScaleRight (rate alpha) a a

        col :
          R539.columnSum rightRateGramPair rest alpha
          ≡ Work.coherentWork d ar
        col =
          trans
            (column rest)
            (R597.columnWorkFactors
              (λ tau → doubleCell tau)
              rest ar)
          where
          column :
            (xs : List Physical.PhysicalTriadIncidence) →
            R539.columnSum rightRateGramPair xs alpha
            ≡ R539.columnSum
                (λ x _ → Work.coherentWork (doubleCell x) ar)
                xs alpha
          column [] = refl
          column (x ∷ xs) =
            cong₂ _+_
              (Work.workScaleRight
                (rate alpha) (doubleCell x) (doubleCell alpha))
              (column xs)

        expanded :
          Work.coherentWork
            (C3.complex3Add a d)
            (C3.complex3Add ar dr)
          ≡ Work.coherentWork a ar
            + Work.coherentWork a dr
            + Work.coherentWork d ar
            + Work.coherentWork d dr
        expanded =
          trans
            (R597.workAddLeft a d (C3.complex3Add ar dr))
            (trans
              (cong₂ _+_
                (Work.workAddRight a ar dr)
                (Work.workAddRight d ar dr))
              (solve
                ( Work.coherentWork a ar
                ∷ Work.coherentWork a dr
                ∷ Work.coherentWork d ar
                ∷ Work.coherentWork d dr ∷ [])))
      in
      trans
        (cong₂ _+_ diag refl)
        (trans
          (cong
            (Work.coherentWork a ar +_)
            (cong₂ _+_ refl col))
          (trans
            (solve
              ( Work.coherentWork a ar
              ∷ Work.coherentWork a dr
              ∷ Work.coherentWork d ar
              ∷ Work.coherentWork d dr ∷ []))
            (sym expanded)))

  rightRateGramFullIsA3WeightedGram :
    R543.fullSquareSum rightRateGramPair fibre
    ≡ A3.rightRateWeightedFullGram
  rightRateGramFullIsA3WeightedGram =
    trans
      rightRateGramFullFactors
      (cong
        (Work.coherentWork (R224.foldVector doubleCell fibre))
        (sym weightedKernelFoldIsRateScaledDoubleFold))

  gramSymmetric :
    (a b : Physical.PhysicalTriadIncidence) →
    gram a b ≡ gram b a
  gramSymmetric a b =
    A3.coherentWorkSymmetric599 (doubleCell a) (doubleCell b)

  fullPairRateGramIsTwoA3WeightedGram :
    R543.fullSquareSum (pairRateGram rate gram) fibre
    ≡ R539.two * A3.rightRateWeightedFullGram
  fullPairRateGramIsTwoA3WeightedGram =
    trans
      (fullPairRateGramIsTwoRight rate gram gramSymmetric fibre)
      (cong (R539.two *_) rightRateGramFullIsA3WeightedGram)

  centeredStaticFullSquare :
    R543.fullSquareSum
      (centeredStaticPair A3.n A3.rateTotal rate gram) fibre
    ≡ R539.two * ((Kernel.four * Kernel.four) * A3.signedA3)
  centeredStaticFullSquare =
    let
      fullGram = R543.fullSquareSum gram fibre

      fullGramMeaning :
        fullGram ≡ A3.fullGram
      fullGramMeaning =
        trans
          (R597.fullGramIsCoherentFold doubleCell fibre)
          refl

      pairRateMeaning = fullPairRateGramIsTwoA3WeightedGram

      centeredExpansion :
        R543.fullSquareSum
          (centeredStaticPair A3.n A3.rateTotal rate gram) fibre
        ≡
        R539.two * A3.rateTotal * fullGram
          - A3.n * R543.fullSquareSum
              (pairRateGram rate gram) fibre
      centeredExpansion =
        Cauchy.fullSquareLinearCombination
          (R539.two * A3.rateTotal)
          (0ℚ - A3.n)
          gram
          (pairRateGram rate gram)
          fibre

      a3Meaning = A3.centeredFullGramNormalForm
    in
    trans centeredExpansion
      (trans
        (cong₂ _-_
          (cong (R539.two * A3.rateTotal *_) fullGramMeaning)
          (cong (A3.n *_) pairRateMeaning))
        (let
          G = A3.fullGram
          Gr = A3.rightRateWeightedFullGram
          S3 = (Kernel.four * Kernel.four) * A3.signedA3
        in
        trans
          (solve (A3.rateTotal ∷ A3.n ∷ G ∷ Gr ∷ []))
          (cong (R539.two *_) (sym a3Meaning))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round600PairRateFullSquareIdentityClosed : Bool
round600PairRateFullSquareIdentityClosed = true

round600LiteralRightWeightedGramAlignedWithA3 : Bool
round600LiteralRightWeightedGramAlignedWithA3 = true

round600A3CenteredStaticFullSquareClosed : Bool
round600A3CenteredStaticFullSquareClosed = true

round600IntroducesEstimate : Bool
round600IntroducesEstimate = false

round600DynamicCenteredCauchyPairStillOpen : Bool
round600DynamicCenteredCauchyPairStillOpen = true

round600PairRateFullSquareIdentityClosedIsTrue :
  round600PairRateFullSquareIdentityClosed ≡ true
round600PairRateFullSquareIdentityClosedIsTrue = refl

round600LiteralRightWeightedGramAlignedWithA3IsTrue :
  round600LiteralRightWeightedGramAlignedWithA3 ≡ true
round600LiteralRightWeightedGramAlignedWithA3IsTrue = refl

round600A3CenteredStaticFullSquareClosedIsTrue :
  round600A3CenteredStaticFullSquareClosed ≡ true
round600A3CenteredStaticFullSquareClosedIsTrue = refl

round600IntroducesEstimateIsFalse :
  round600IntroducesEstimate ≡ false
round600IntroducesEstimateIsFalse = refl

round600DynamicCenteredCauchyPairStillOpenIsTrue :
  round600DynamicCenteredCauchyPairStillOpen ≡ true
round600DynamicCenteredCauchyPairStillOpenIsTrue = refl
