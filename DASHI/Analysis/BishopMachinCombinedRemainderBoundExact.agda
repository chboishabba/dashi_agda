module DASHI.Analysis.BishopMachinCombinedRemainderBoundExact where

------------------------------------------------------------------------
-- K04b2: ACTUAL TWO-SERIES BISHOP MACHIN WEIGHTED ERROR ESTIMATES.
-- Original mathematics: Machin (1706), alternating-series remainder;
-- Bishop & Bridges (1985); Murray (2022), arXiv:2205.08354.
--
-- Independent DASHI step: reuse the original signed partial series,
-- original actual Bishop Machin pi, the source's alternating first
-- omitted theorem, and its REAL-order and setoid triangle inequalities.
-- No abstract epsilon oracle, postulated real, synthetic analytic pi.
--
-- The result bounds BOTH parities directly by the weighted first
-- omitted magnitudes. Conversion to 4/25^n is an exact rational-order
-- lemma to be supplied separately. Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as Bishop
import RealProperties as RP
import Sequence as Series

import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopMachinPiRationalWindowExact as W
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact as I
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as Tail
import DASHI.Analysis.BishopMachinSignedFiniteHistoryExact as S
import DASHI.Analysis.BishopMachinQuantitativeOmittedTailExact as O
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Q

sixteen four : Bishop.ℝ
sixteen = Bishop._⋆ M.sixteen
four = Bishop._⋆ M.four

atan5Partial atan239Partial : Nat → Bishop.ℝ
atan5Partial = Series.SeriesOf (M.atanSignedTerm M.bishopOneFifth)
atan239Partial =
  Series.SeriesOf (M.atanSignedTerm M.bishopOneTwoHundredThirtyNinth)

magnitude5 magnitude239 : Nat → Bishop.ℝ
magnitude5 = M.atanMagnitudeTerm M.bishopOneFifth
magnitude239 = M.atanMagnitudeTerm M.bishopOneTwoHundredThirtyNinth

-- This is the literal original source's two-series partial sum, not
-- a fresh object named "Machin approximation".
sourcePartialAgreement : ∀ n →
  Bishop._≃_
    (S.machinSignedPartialStage n)
    (Bishop._-_
      (Bishop._*_ sixteen (atan5Partial n))
      (Bishop._*_ four (atan239Partial n)))
sourcePartialAgreement n =
  RP.≃-trans
    (S.machinSignedPartialIsOriginalDifference n)
    (RP.+-cong
      (S.leftScaledPartial
        sixteen (M.atanSignedTerm M.bishopOneFifth) n)
      (RP.-‿cong
        (S.leftScaledPartial
          four (M.atanSignedTerm M.bishopOneTwoHundredThirtyNinth) n)))

-- Algebraic equality of the actual pi minus the actual partial stage
-- with the weighted errors in the two original arctangent partials.
weightedErrorIdentity : ∀ n →
  Bishop._≃_
    (Bishop._-_
      M.bishopMachinPi
      (S.machinSignedPartialStage n))
    (Bishop._-_
      (Bishop._*_ sixteen
        (Bishop._-_ M.bishopAtanOneFifth (atan5Partial n)))
      (Bishop._*_ four
        (Bishop._-_ M.bishopAtanOneTwoHundredThirtyNinth
          (atan239Partial n))))
weightedErrorIdentity n =
  RP.≃-trans
    (RP.+-cong
      RP.≃-refl
      (RP.-‿cong (sourcePartialAgreement n)))
    (let open RP.ℝ-Solver
     in solve 4
       (λ a b aN bN →
         ((Κ M.sixteen ⊗ a) ⊖ (Κ M.four ⊗ b))
           ⊖ ((Κ M.sixteen ⊗ aN) ⊖ (Κ M.four ⊗ bN))
         ⊜
         (Κ M.sixteen ⊗ (a ⊖ aN))
           ⊖ (Κ M.four ⊗ (b ⊖ bN)))
       RP.≃-refl
       M.bishopAtanOneFifth
       M.bishopAtanOneTwoHundredThirtyNinth
       (atan5Partial n)
       (atan239Partial n))

-- Exact first-omitted absolute error for ANY positive original
-- Bishop arctangent. The zero/nonzero and parity cases are handled
-- by the source's actual lower/upper signed-tail order certificates.
evenArctanAbsoluteError : ∀ {x} →
  (p : I.PositiveHalfBallPoint x) → ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        (M.bishopAtanHalfBall x (I.insideHalf p))
        (Series.SeriesOf (M.atanSignedTerm x)
          (Alternating.double k))))
    (M.atanMagnitudeTerm x (Alternating.double k))
evenArctanAbsoluteError p k =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x
        (RP.0≤x⇒nonNegx
          (Tail.lowerTailNonnegative (O.actualArctanTail p) k))))
    (O.actualArctanEvenRemainderBound p k)

oddArctanAbsoluteError : ∀ {x} →
  (p : I.PositiveHalfBallPoint x) → ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        (M.bishopAtanHalfBall x (I.insideHalf p))
        (Series.SeriesOf (M.atanSignedTerm x)
          (suc (Alternating.double k)))))
    (M.atanMagnitudeTerm x (suc (Alternating.double k)))
oddArctanAbsoluteError {x} p k =
  RP.≤-respˡ-≃
    (RP.≃-symm
      (RP.≃-trans
        (RP.∣x-y∣≃∣y-x∣
        (M.bishopAtanHalfBall x (I.insideHalf p))
        (Series.SeriesOf (M.atanSignedTerm x)
          (suc (Alternating.double k))))
      (RP.nonNegx⇒∣x∣≃x
        (RP.0≤x⇒nonNegx
          (Tail.upperTailNonnegative (O.actualArctanTail p) k)))))
    (O.actualArctanOddRemainderBound p k)

-- Two-factor absolute triangle bound with true 16/4 source constants.
weightedAbsoluteTriangle :
  ∀ (u v a d : Bishop.ℝ) →
  Bishop._≤_ (Bishop.∣_∣ u) a →
  Bishop._≤_ (Bishop.∣_∣ v) d →
  Bishop._≤_
    (Bishop.∣
      Bishop._-_
        (Bishop._*_ sixteen u)
        (Bishop._*_ four v)
    ∣)
    (Bishop._+_
      (Bishop._*_ sixteen a)
      (Bishop._*_ four d))
weightedAbsoluteTriangle u v a d uBound vBound =
  RP.≤-trans
    (RP.≤-respʳ-≃
      (RP.+-cong
        (RP.≃-trans
          (RP.∣x*y∣≃∣x∣*∣y∣ sixteen u)
          (RP.*-congʳ
            (RP.nonNegx⇒∣x∣≃x W.sixteenNN)))
        (RP.≃-trans
          RP.∣-x∣≃∣x∣
          (RP.≃-trans
            (RP.∣x*y∣≃∣x∣*∣y∣ four v)
            (RP.*-congʳ
              (RP.nonNegx⇒∣x∣≃x W.fourNN)))))
      (RP.∣x+y∣≤∣x∣+∣y∣
        (Bishop._*_ sixteen u)
        (Bishop.-_ (Bishop._*_ four v))))
    (RP.+-mono-≤
      (RP.*-monoˡ-≤-nonNeg uBound W.sixteenNN)
      (RP.*-monoˡ-≤-nonNeg vBound W.fourNN))

-- General exact bound on the ACTUAL source pi and source partial sums,
-- parametrised only by the two genuinely proved arctangent tail bounds.
combinedMachinAtIndex :
  ∀ n →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (S.machinSignedPartialStage n)))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 n))
      (Bishop._*_ four (magnitude239 n))) →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (Bishop._⋆ (Q.qMachinStage n))))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 n))
      (Bishop._*_ four (magnitude239 n)))
combinedMachinAtIndex n partialBound =
  RP.≤-respˡ-≃
    (RP.∣-∣-cong
      (RP.+-cong RP.≃-refl
        (RP.-‿cong
          (RP.≃-symm (Q.qMachinStageEmbedsAsOriginalBishopPartial n)))))
    partialBound

-- Actual strongest currently derived Bishop-order bounds for both parity
-- classes, with no conditional tail assumptions.
machinEvenPartialError :
  ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (S.machinSignedPartialStage (Alternating.double k))))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 (Alternating.double k)))
      (Bishop._*_ four (magnitude239 (Alternating.double k))))
machinEvenPartialError k =
  RP.≤-respˡ-≃
    (RP.≃-symm (RP.∣-∣-cong (weightedErrorIdentity (Alternating.double k))))
    (weightedAbsoluteTriangle
      (Bishop._-_
        M.bishopAtanOneFifth
        (atan5Partial (Alternating.double k)))
      (Bishop._-_
        M.bishopAtanOneTwoHundredThirtyNinth
        (atan239Partial (Alternating.double k)))
      (magnitude5 (Alternating.double k))
      (magnitude239 (Alternating.double k))
      (evenArctanAbsoluteError W.oneFifthPoint k)
      (evenArctanAbsoluteError W.oneTwoHundredThirtyNinthPoint k))

machinOddPartialError :
  ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (S.machinSignedPartialStage (suc (Alternating.double k)))))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 (suc (Alternating.double k))))
      (Bishop._*_ four (magnitude239 (suc (Alternating.double k)))))
machinOddPartialError k =
  RP.≤-respˡ-≃
    (RP.≃-symm (RP.∣-∣-cong (weightedErrorIdentity (suc (Alternating.double k)))))
    (weightedAbsoluteTriangle
      (Bishop._-_
        M.bishopAtanOneFifth
        (atan5Partial (suc (Alternating.double k))))
      (Bishop._-_
        M.bishopAtanOneTwoHundredThirtyNinth
        (atan239Partial (suc (Alternating.double k))))
      (magnitude5 (suc (Alternating.double k)))
      (magnitude239 (suc (Alternating.double k)))
      (oddArctanAbsoluteError W.oneFifthPoint k)
      (oddArctanAbsoluteError W.oneTwoHundredThirtyNinthPoint k))

machinEvenRationalError :
  ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (Bishop._⋆ (Q.qMachinStage (Alternating.double k)))))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 (Alternating.double k)))
      (Bishop._*_ four (magnitude239 (Alternating.double k))))
machinEvenRationalError k =
  combinedMachinAtIndex
    (Alternating.double k) (machinEvenPartialError k)

machinOddRationalError :
  ∀ k →
  Bishop._≤_
    (Bishop.∣_∣
      (Bishop._-_
        M.bishopMachinPi
        (Bishop._⋆ (Q.qMachinStage (suc (Alternating.double k))))))
    (Bishop._+_
      (Bishop._*_ sixteen (magnitude5 (suc (Alternating.double k))))
      (Bishop._*_ four (magnitude239 (suc (Alternating.double k)))))
machinOddRationalError k =
  combinedMachinAtIndex
    (suc (Alternating.double k)) (machinOddPartialError k)
