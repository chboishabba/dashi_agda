module DASHI.Physics.Closure.NSTriadKNBlockGramCovarianceTelescopeRound201Exact where

------------------------------------------------------------------------
-- ROUND201 / LAW OF TOTAL GRAM FOR SIGNED PHYSICAL BLOCKS
--
-- Round180 gives the exact finite identity
--
--   ||sum cells||^2 = cellMass + GramDebt.
--
-- Round185 reduces Package A to three within-class payments, but each physical
-- class is itself naturally organised into Bony / dyadic / shell blocks.  This
-- module performs the next exact reopening BEFORE any estimate.
--
-- For a finite list of finite signed blocks B_a, let S_a = sum(B_a).  Then
--
--   ||sum_a S_a||^2
--     = sum_a cellMass(B_a)
--       + sum_a GramDebt(B_a)
--       + GramDebt([S_a]).
--
-- This is the finite Hilbert-space analogue of a law of total covariance:
-- the full interference debt splits EXACTLY into
--
--   within-block debt + between-block debt.
--
-- No absolute value, shell count, convolution-cardinality factor, or sign
-- hypothesis is introduced.  The next analytic theorem may therefore estimate
-- residual covariance between already-summed physical blocks instead of the
-- enormous raw cell Gram matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180

F = R179.F

SignedBlock : Set
SignedBlock = List (C3.Complex3 F)

blockSums : List SignedBlock → List (C3.Complex3 F)
blockSums [] = []
blockSums (block ∷ blocks) = R180.sumCells block ∷ blockSums blocks

groupedBlockSum : List SignedBlock → C3.Complex3 F
groupedBlockSum blocks = R180.sumCells (blockSums blocks)

cellMassAcrossBlocks : List SignedBlock → ℚ
cellMassAcrossBlocks [] = 0ℚ
cellMassAcrossBlocks (block ∷ blocks) =
  R180.cellMassSum block + cellMassAcrossBlocks blocks

withinBlockGramDebt : List SignedBlock → ℚ
withinBlockGramDebt [] = 0ℚ
withinBlockGramDebt (block ∷ blocks) =
  R180.gramDebt block + withinBlockGramDebt blocks

betweenBlockGramDebt : List SignedBlock → ℚ
betweenBlockGramDebt blocks = R180.gramDebt (blockSums blocks)

-- First telescope each block internally.  This is the exact statement that the
-- mass of the block-sum list already contains every within-block covariance.
blockSumMassTelescope :
  (blocks : List SignedBlock) →
  R180.cellMassSum (blockSums blocks)
  ≡ cellMassAcrossBlocks blocks + withinBlockGramDebt blocks
blockSumMassTelescope [] = solve []
blockSumMassTelescope (block ∷ blocks)
  rewrite R180.finiteFibreGramLedger block
        | blockSumMassTelescope blocks =
  solve
    ( R180.cellMassSum block
    ∷ R180.gramDebt block
    ∷ cellMassAcrossBlocks blocks
    ∷ withinBlockGramDebt blocks
    ∷ [])

-- LAW OF TOTAL GRAM.
-- Apply Round180 once more, now to the already-summed block vectors.  The
-- between-block debt is therefore kept signed and distinct from the internal
-- debt paid while forming each block.
blockGramCovarianceTelescope :
  (blocks : List SignedBlock) →
  L2.complex3NormSquared (groupedBlockSum blocks)
  ≡ cellMassAcrossBlocks blocks
    + withinBlockGramDebt blocks
    + betweenBlockGramDebt blocks
blockGramCovarianceTelescope blocks
  rewrite R180.finiteFibreGramLedger (blockSums blocks)
        | blockSumMassTelescope blocks =
  solve
    ( cellMassAcrossBlocks blocks
    ∷ withinBlockGramDebt blocks
    ∷ betweenBlockGramDebt blocks
    ∷ [])

-- A proof-bearing package for the exact decomposition only.  It deliberately
-- contains no positivity or decay assertion about either debt term.
record BlockGramLedger (blocks : List SignedBlock) : Set where
  constructor block-gram-ledger
  field
    exactTotalGram :
      L2.complex3NormSquared (groupedBlockSum blocks)
      ≡ cellMassAcrossBlocks blocks
        + withinBlockGramDebt blocks
        + betweenBlockGramDebt blocks

open BlockGramLedger public

canonicalBlockGramLedger :
  (blocks : List SignedBlock) → BlockGramLedger blocks
canonicalBlockGramLedger blocks =
  block-gram-ledger (blockGramCovarianceTelescope blocks)

round201LawOfTotalGramClosed : Bool
round201LawOfTotalGramClosed = true

round201WithinAndBetweenBlockDebtSeparatedExactly : Bool
round201WithinAndBetweenBlockDebtSeparatedExactly = true

round201AbsoluteValueIntroducedBeforeBlockTelescope : Bool
round201AbsoluteValueIntroducedBeforeBlockTelescope = false

round201ShellOrBonyBlockCountFactorIntroduced : Bool
round201ShellOrBonyBlockCountFactorIntroduced = false

round201ResidualBetweenBlockCovariancePaymentClosed : Bool
round201ResidualBetweenBlockCovariancePaymentClosed = false

round201CutoffUniformQuarticCompanionClosed : Bool
round201CutoffUniformQuarticCompanionClosed = false

round201PackageAClosed : Bool
round201PackageAClosed = false

round201ClayPromotion : Bool
round201ClayPromotion = false

round201LawOfTotalGramClosedIsTrue : round201LawOfTotalGramClosed ≡ true
round201LawOfTotalGramClosedIsTrue = refl

round201PackageAClosedIsFalse : round201PackageAClosed ≡ false
round201PackageAClosedIsFalse = refl
