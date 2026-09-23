{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCauchyR397R406ReconciliationExact where

------------------------------------------------------------------------
-- CAUCHY / R397 / R406 EXACT FINITE RECONCILIATION
--
-- On one finite physical incidence list with R396-local pair positivity:
--
--   orderedOffDiag(Gram) = 2 * sumGram(R396 pairs)
--
-- and, for the same Cauchy-resolved tangent scalar,
--
--   orderedOffDiag(K * GramTangent)
--     = 2 * sumWeightedFluxTangent(R396 pairs).
--
-- The full-square resolved tangent additionally contains exactly the diagonal
-- self-flux tangent.  Hence the Cauchy-reduced R406 expression
--
--   orderedOffDiag(Gram) + fullSquare(K * GramTangent)
--
-- is exactly
--
--   selfFluxTangent
--     + 2 * (sumGram + sumWeightedFluxTangent)
--
-- and R385 reduces the parenthesis to the literal weighted nonlinear
-- remainder.  Thus
--
--   = selfFluxTangent + 2 * sumWeightedRemainder.
--
-- This is a regression/reconciliation theorem only.  It introduces no
-- estimate and, importantly, does NOT identify the R406 remainder with A3.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedR406GramTangentNormalFormExact as Resolved

F : C3.RealField _
F = Rational.rationalRealField

module Reconcile
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module P = R389.DoubleMixedPair physicalSystem S
  module Local = R396.LocalEnumerate physicalSystem S
  module Swap = R538.PairSwap physicalSystem S
  module C = Resolved.Physical physicalSystem S

  cell : Physical.PhysicalTriadIncidence → C3.Complex3 F
  cell alpha = R291.cellA (P.physicalDoubleMixedPair alpha alpha)

  pairGram :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairGram = C.pairGram

  pairTangent :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairTangent = C.pairTangent

  resolvedTangent :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  resolvedTangent alpha beta =
    Swap.pairResolvent alpha beta * pairTangent alpha beta

  pairGramIsR383 :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairGram alpha beta ≡ R383.pairGram (cell alpha) (cell beta)
  pairGramIsR383 alpha beta = refl

  pairGramSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairGram alpha beta ≡ pairGram beta alpha
  pairGramSymmetric alpha beta =
    cong (R291.two *_)
      (R287.realHermitianCrossSymmetric (cell alpha) (cell beta))

  pairTangentSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairTangent alpha beta ≡ pairTangent beta alpha
  pairTangentSymmetric alpha beta =
    let
      qab = P.physicalDoubleMixedPair alpha beta
      qba = P.physicalDoubleMixedPair beta alpha
      x = R179.realHermitianCross (R291.tangentA qab) (R291.cellB qab)
      y = R179.realHermitianCross (R291.cellA qab) (R291.tangentB qab)

      first :
        R179.realHermitianCross (R291.tangentA qab) (R291.cellB qab)
        ≡
        R179.realHermitianCross (R291.cellA qba) (R291.tangentB qba)
      first =
        R287.realHermitianCrossSymmetric
          (R291.tangentA qab) (R291.cellB qab)

      second :
        R179.realHermitianCross (R291.cellA qab) (R291.tangentB qab)
        ≡
        R179.realHermitianCross (R291.tangentA qba) (R291.cellB qba)
      second =
        R287.realHermitianCrossSymmetric
          (R291.cellA qab) (R291.tangentB qab)
    in
    trans
      (cong (R291.two *_) (cong₂ _+_ first second))
      (cong (R291.two *_) (solve (x ∷ y ∷ [])))

  resolvedTangentSymmetric :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    resolvedTangent alpha beta ≡ resolvedTangent beta alpha
  resolvedTangentSymmetric alpha beta =
    cong₂ _*_
      (Swap.pairResolventSymmetric alpha beta)
      (pairTangentSymmetric alpha beta)

  rowGramIsHeadPairSum :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    R539.rowSum pairGram alpha rest
    ≡ R383.headPairSum (cell alpha) (map cell rest)
  rowGramIsHeadPairSum alpha [] = refl
  rowGramIsHeadPairSum alpha (beta ∷ rest) =
    cong₂ _+_
      (pairGramIsR383 alpha beta)
      (rowGramIsHeadPairSum alpha rest)

  unorderedGramIsAllPairSum :
    (items : List Physical.PhysicalTriadIncidence) →
    R539.unorderedPairSum pairGram items
    ≡ R383.allPairSum (map cell items)
  unorderedGramIsAllPairSum [] = refl
  unorderedGramIsAllPairSum (alpha ∷ rest) =
    cong₂ _+_
      (rowGramIsHeadPairSum alpha rest)
      (unorderedGramIsAllPairSum rest)

  orderedGramIsTwoLiteralSumGram :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R539.orderedOffDiagonalSum pairGram items
    ≡ R539.two * R385.sumGram (Local.allR290Pairs items positive)
  orderedGramIsTwoLiteralSumGram items positive =
    trans
      (R539.orderedOffDiagonalIsTwoUnordered
        pairGram pairGramSymmetric items)
      (trans
        (cong (R539.two *_) (unorderedGramIsAllPairSum items))
        (cong (R539.two *_) (sym (Local.allPairsGramExact items positive))))

  sumWeightedFluxTangentAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFluxTangent (left ++ right)
    ≡ R385.sumWeightedFluxTangent left
      + R385.sumWeightedFluxTangent right
  sumWeightedFluxTangentAppend [] right = refl
  sumWeightedFluxTangentAppend (p ∷ rest) right
    rewrite sumWeightedFluxTangentAppend rest right = refl

  headWeightedFluxTangentExact :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Data.Rational.Base.Positive
        (R291.pairRate (P.physicalDoubleMixedPair alpha beta))) →
    R385.sumWeightedFluxTangent
      (Local.headR290Pairs alpha rest positive)
    ≡ R539.rowSum resolvedTangent alpha rest
  headWeightedFluxTangentExact alpha [] positive = refl
  headWeightedFluxTangentExact alpha (beta ∷ rest) positive =
    cong₂ _+_
      refl
      (headWeightedFluxTangentExact alpha rest
        (λ gamma member → positive gamma (R396.there member)))

  allWeightedFluxTangentExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R385.sumWeightedFluxTangent (Local.allR290Pairs items positive)
    ≡ R539.unorderedPairSum resolvedTangent items
  allWeightedFluxTangentExact [] Local.positiveNil = refl
  allWeightedFluxTangentExact
      (alpha ∷ rest) (Local.positiveCons headPositive tailPositive) =
    trans
      (sumWeightedFluxTangentAppend
        (Local.headR290Pairs alpha rest headPositive)
        (Local.allR290Pairs rest tailPositive))
      (cong₂ _+_
        (headWeightedFluxTangentExact alpha rest headPositive)
        (allWeightedFluxTangentExact rest tailPositive))

  orderedResolvedTangentIsTwoLiteralFluxTangent :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R539.orderedOffDiagonalSum resolvedTangent items
    ≡ R539.two *
      R385.sumWeightedFluxTangent (Local.allR290Pairs items positive)
  orderedResolvedTangentIsTwoLiteralFluxTangent items positive =
    trans
      (R539.orderedOffDiagonalIsTwoUnordered
        resolvedTangent resolvedTangentSymmetric items)
      (cong (R539.two *_) (sym (allWeightedFluxTangentExact items positive)))

  diagonalResolvedTangent :
    List Physical.PhysicalTriadIncidence → ℚ
  diagonalResolvedTangent items =
    R543.diagonalSum resolvedTangent items

  fullResolvedTangentSplit :
    (items : List Physical.PhysicalTriadIncidence) →
    R543.fullSquareSum resolvedTangent items
    ≡ diagonalResolvedTangent items
      + R539.orderedOffDiagonalSum resolvedTangent items
  fullResolvedTangentSplit =
    R543.fullSquareIsDiagonalPlusOrderedOffDiagonal resolvedTangent

  cauchyReducedResidualReconciles :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R539.orderedOffDiagonalSum pairGram items
      + R543.fullSquareSum resolvedTangent items
    ≡
    diagonalResolvedTangent items
      + R539.two *
          R385.sumWeightedRemainder (Local.allR290Pairs items positive)
  cauchyReducedResidualReconciles items positive =
    let
      pairs = Local.allR290Pairs items positive
      gramToPairs = orderedGramIsTwoLiteralSumGram items positive
      tangentSplit = fullResolvedTangentSplit items
      tangentToPairs =
        orderedResolvedTangentIsTwoLiteralFluxTangent items positive
      r385 =
        R385.finiteGramAsNegativeFluxDerivativePlusRemainder pairs
    in
    trans
      (cong₂ _+_ gramToPairs tangentSplit)
      (trans
        (cong
          (λ x →
            R539.two * R385.sumGram pairs
              + (diagonalResolvedTangent items + x))
          tangentToPairs)
        (trans
          (solve
            (R385.sumGram pairs
              ∷ R385.sumWeightedFluxTangent pairs
              ∷ diagonalResolvedTangent items
              ∷ []))
          (cong
            (λ x →
              diagonalResolvedTangent items + R539.two * x)
            (sumGramPlusFluxIsRemainder pairs r385))))
    where
    sumGramPlusFluxIsRemainder :
      (pairs : List R290.DampedGramPair) →
      R385.sumGram pairs
        ≡ (0ℚ - R385.sumWeightedFluxTangent pairs)
          + R385.sumWeightedRemainder pairs →
      R385.sumGram pairs + R385.sumWeightedFluxTangent pairs
        ≡ R385.sumWeightedRemainder pairs
    sumGramPlusFluxIsRemainder pairs identity
      rewrite identity =
      solve
        (R385.sumWeightedFluxTangent pairs
          ∷ R385.sumWeightedRemainder pairs ∷ [])

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

cauchyR397R406ReconciliationClosed : Bool
cauchyR397R406ReconciliationClosed = true

orderedGramCarrierReconciledWithR396 : Bool
orderedGramCarrierReconciledWithR396 = true

orderedResolvedTangentCarrierReconciledWithR396 : Bool
orderedResolvedTangentCarrierReconciledWithR396 = true

reconciliationIntroducesEstimate : Bool
reconciliationIntroducesEstimate = false

reconciliationIdentifiesR406WithA3 : Bool
reconciliationIdentifiesR406WithA3 = false

cauchyR397R406ReconciliationClosedIsTrue :
  cauchyR397R406ReconciliationClosed ≡ true
cauchyR397R406ReconciliationClosedIsTrue = refl

reconciliationIntroducesEstimateIsFalse :
  reconciliationIntroducesEstimate ≡ false
reconciliationIntroducesEstimateIsFalse = refl

reconciliationIdentifiesR406WithA3IsFalse :
  reconciliationIdentifiesR406WithA3 ≡ false
reconciliationIdentifiesR406WithA3IsFalse = refl
