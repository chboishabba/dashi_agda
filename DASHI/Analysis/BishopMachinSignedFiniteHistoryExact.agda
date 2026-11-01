module DASHI.Analysis.BishopMachinSignedFiniteHistoryExact where

------------------------------------------------------------------------
-- K04a: CONCRETE FINITE BISHOP HISTORY FOR MACHIN'S SIGNED SERIES
--
-- Original analytic sources: John Machin (1706); Errett Bishop and
-- Douglas Bridges, Constructive Analysis (1985), DOI
-- 10.1007/978-3-642-61667-9; Zachary Murray, Constructive Analysis
-- in the Agda Proof Assistant (2022), arXiv:2205.08354.
--
-- SOURCE-REUSE / EXACT SCOPE
--   BishopMachinArctanConstructionExact owns the genuine convergent
--   Bishop atan signed terms and the constructed real bishopMachinPi.
--   BishopFiniteSeriesDifferenceExact owns finite SeriesOf subtraction.
-- This source derives the actual signed finite-stage series identity,
-- NOT a new Bishop carrier, a rational q_n embedding, an explicit
-- convergence modulus, trigonometric pi equality or analytic zeta.
-- Newly source-written; Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as Bishop
import RealProperties as BishopP
import Sequence as Series

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Difference

-- Preserve the original source terms and source-specific 16/4 factors,
-- including their true alternating sign. No new FRACTRAN term codec.
machinFifthWeightedTerm : Nat → Bishop.ℝ
machinFifthWeightedTerm n =
  Bishop._*_
    (Bishop._⋆ Machin.sixteen)
    (Machin.atanSignedTerm Machin.bishopOneFifth n)

machin239WeightedTerm : Nat → Bishop.ℝ
machin239WeightedTerm n =
  Bishop._*_
    (Bishop._⋆ Machin.four)
    (Machin.atanSignedTerm Machin.bishopOneTwoHundredThirtyNinth n)

machinSignedTerm : Nat → Bishop.ℝ
machinSignedTerm n =
  Bishop._-_ (machinFifthWeightedTerm n) (machin239WeightedTerm n)

-- This is the ACTUAL finite Bishop series on the source carrier.
machinSignedPartialStage : Nat → Bishop.ℝ
machinSignedPartialStage = Series.SeriesOf machinSignedTerm

machinFifthPartialStage : Nat → Bishop.ℝ
machinFifthPartialStage = Series.SeriesOf machinFifthWeightedTerm

machin239PartialStage : Nat → Bishop.ℝ
machin239PartialStage = Series.SeriesOf machin239WeightedTerm

-- Exact for every n, using the already proved finite-series
-- subtraction identity; no limit, continuity or numeric claim.
machinSignedPartialIsOriginalDifference :
  (n : Nat) →
  Bishop._≃_
    (machinSignedPartialStage n)
    (Bishop._-_
      (machinFifthPartialStage n)
      (machin239PartialStage n))
machinSignedPartialIsOriginalDifference n =
  BishopP.≃-symm
    (Difference.finiteSeriesDifference
      machinFifthWeightedTerm machin239WeightedTerm n)

------------------------------------------------------------------------
-- K04b: CONVERGENCE OF THIS SAME CONCRETE COMBINED SERIES.
--
-- The original Machin owner already proves each individual arctangent
-- convergence; only the scale/add/subtract transport was outstanding.
-- We use the original Bishop Sequence limit-arithmetic theorems.
-- No imported convergence postulate, no alternative real number.
------------------------------------------------------------------------

constantSequence : Bishop.ℝ → Nat → Bishop.ℝ
constantSequence value _ = value

constantSequenceConverges :
  ∀ value →
  Series._ConvergesTo_ (constantSequence value) value
constantSequenceConverges value =
  Series.xₙ≃c⇒xₙ→c
    (λ {(suc index) → BishopP.≃-refl})

-- The left-factor version of the existing finite common-factor identity.
-- The source terms are already defined with the factor on the left.
leftScaledPartial :
  (factor : Bishop.ℝ)
  (terms : Nat → Bishop.ℝ)
  (count : Nat) →
  Bishop._≃_
    (Series.SeriesOf (λ n → Bishop._*_ factor (terms n)) count)
    (Bishop._*_ factor (Series.SeriesOf terms count))
leftScaledPartial factor terms zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ f → Κ 0ℚᵘ ⊜ f ⊗ Κ 0ℚᵘ)
    BishopP.≃-refl factor
leftScaledPartial factor terms (suc count) =
  BishopP.≃-trans
    (BishopP.+-congˡ
      (Bishop._*_ factor (terms count))
      (leftScaledPartial factor terms count))
    (let open BishopP.ℝ-Solver
     in solve 3
       (λ f prefix term →
         ((f ⊗ prefix) ⊕ (f ⊗ term))
         ⊜ (f ⊗ (prefix ⊕ term)))
       BishopP.≃-refl
       factor
       (Series.SeriesOf terms count)
       (terms count))

leftScaledSeriesConverges :
  (factor : Bishop.ℝ)
  (terms : Nat → Bishop.ℝ)
  (limit : Bishop.ℝ) →
  Series._ConvergesTo_ (Series.SeriesOf terms) limit →
  Series._ConvergesTo_
    (Series.SeriesOf (λ n → Bishop._*_ factor (terms n)))
    (Bishop._*_ factor limit)
leftScaledSeriesConverges factor terms limit converges =
  Series.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      BishopP.≃-symm (leftScaledPartial factor terms (suc count))})
    ( Bishop._*_ factor limit
    , Series.xₙyₙ→x₀y₀
        (factor , constantSequenceConverges factor)
        (limit , converges)
    )

machinFifthPartialConverges :
  Series._ConvergesTo_
    machinFifthPartialStage
    (Bishop._*_
      (Bishop._⋆ Machin.sixteen)
      Machin.bishopAtanOneFifth)
machinFifthPartialConverges =
  leftScaledSeriesConverges
    (Bishop._⋆ Machin.sixteen)
    (Machin.atanSignedTerm Machin.bishopOneFifth)
    Machin.bishopAtanOneFifth
    (Machin.bishopAtanHalfBallConverges
      Machin.bishopOneFifth
      Machin.bishopOneFifthInsideHalf)

machin239PartialConverges :
  Series._ConvergesTo_
    machin239PartialStage
    (Bishop._*_
      (Bishop._⋆ Machin.four)
      Machin.bishopAtanOneTwoHundredThirtyNinth)
machin239PartialConverges =
  leftScaledSeriesConverges
    (Bishop._⋆ Machin.four)
    (Machin.atanSignedTerm Machin.bishopOneTwoHundredThirtyNinth)
    Machin.bishopAtanOneTwoHundredThirtyNinth
    (Machin.bishopAtanHalfBallConverges
      Machin.bishopOneTwoHundredThirtyNinth
      Machin.bishopOneTwoHundredThirtyNinthInsideHalf)

-- This identifies the genuine combined *source partial sums* with
-- the genuine original Bishop Machin real in the pinned limit relation.
-- It does not yet give the executable rational q_n embedding, a
-- geometric modulus, or a classical-trigonometric pi identification.
machinSignedPartialConvergesToOriginalMachinPi :
  Series._ConvergesTo_
    machinSignedPartialStage
    Machin.bishopMachinPi
machinSignedPartialConvergesToOriginalMachinPi =
  Series.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count) →
      BishopP.≃-symm
        (machinSignedPartialIsOriginalDifference (suc count))})
    ( Machin.bishopMachinPi
    , Series.xₙ+yₙ→x₀+y₀
        ( Bishop._*_
            (Bishop._⋆ Machin.sixteen)
            Machin.bishopAtanOneFifth
        , machinFifthPartialConverges )
        ( Bishop.-_
            (Bishop._*_
              (Bishop._⋆ Machin.four)
              Machin.bishopAtanOneTwoHundredThirtyNinth)
        , Series.-xₙ→-x₀
            ( Bishop._*_
                (Bishop._⋆ Machin.four)
                Machin.bishopAtanOneTwoHundredThirtyNinth
            , machin239PartialConverges ) )
    )
