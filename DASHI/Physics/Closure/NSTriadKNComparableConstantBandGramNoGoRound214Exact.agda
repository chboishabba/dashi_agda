module DASHI.Physics.Closure.NSTriadKNComparableConstantBandGramNoGoRound214Exact where

------------------------------------------------------------------------
-- ROUND214 / BIDI NO-GO: CONSTANT SHELL WIDTH DOES NOT PAY SAME-OUTPUT GRAM
--
-- Round213 proves that every physical fixed-output CC partner lies in a
-- cutoff-independent two-sided dyadic collar.  That is strong localization,
-- but localization alone cannot imply a coefficient-one or cutoff-uniform
-- between-partner covariance payment: coherent partners can still align.
--
-- Round183 already gives the exact aligned two-block witness
--
--   individual compressed mass sum = 2,
--   compressed sum mass            = 4,
--   between-partner debt           = 2.
--
-- Here we decorate that witness with *zero-width* shell data: both inputs and
-- the output are assigned the same shell index.  Thus the strongest possible
-- abstract constant-band hypothesis is compatible with strictly positive Gram
-- debt.
--
-- 2026 BIDI CORRECTION
-- --------------------
-- The AlmostOrthogonalGramSchur return makes the scope of this no-go sharper:
-- it refutes shell-localization-as-payment, not the whole resolvent route.
-- A truncation-uniform absolute Gram-Schur row bound, block/operator
-- Cotlar--Stein bound, or direct signed-resolvent estimate may still close the
-- same consumer.  Those are logically distinct physical producers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)

import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramPositiveWitnessRound183Exact as R183
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179

record ShellDecoratedPartnerBlock : Set where
  constructor shell-decorated-partner-block
  field
    outputShell pShell qShell : Nat
    block : R181.CellPair

open ShellDecoratedPartnerBlock public

sameShellAlignedBlock : Nat → ShellDecoratedPartnerBlock
sameShellAlignedBlock j = shell-decorated-partner-block j j j R183.alignedBlock

twoSameShellAlignedBlocks : Nat → List ShellDecoratedPartnerBlock
twoSameShellAlignedBlocks j = sameShellAlignedBlock j ∷ sameShellAlignedBlock j ∷ []

forgetShells : List ShellDecoratedPartnerBlock → List R181.CellPair
forgetShells [] = []
forgetShells (entry ∷ rest) = block entry ∷ forgetShells rest

zeroWidthDecorationForgetsToAlignedWitness :
  (j : Nat) →
  forgetShells (twoSameShellAlignedBlocks j) ≡ R183.twoAlignedBlocks
zeroWidthDecorationForgetsToAlignedWitness j = refl

zeroWidthBandStillHasPositiveBetweenDebt :
  (j : Nat) →
  R181.betweenPartnerDebt (forgetShells (twoSameShellAlignedBlocks j))
  ≡ R179.two * 1ℚ
zeroWidthBandStillHasPositiveBetweenDebt j = R183.betweenDebtOfTwoAlignedBlocksIsTwo

record ConstantBandDataInsufficientWitness : Set where
  constructor constant-band-data-insufficient-witness
  field
    shell : Nat
    decoratedBlocks : List ShellDecoratedPartnerBlock
    allThreeShellLabelsCoincide : decoratedBlocks ≡ twoSameShellAlignedBlocks shell
    positiveDebtExact :
      R181.betweenPartnerDebt (forgetShells decoratedBlocks)
      ≡ R179.two * 1ℚ

constantBandDataInsufficient : ConstantBandDataInsufficientWitness
constantBandDataInsufficient =
  constant-band-data-insufficient-witness
    0
    (twoSameShellAlignedBlocks 0)
    refl
    R183.betweenDebtOfTwoAlignedBlocksIsTwo

data PostLocalizationGramProducer : Set where
  absoluteDataSchur : PostLocalizationGramProducer
  blockOperatorCotlarStein : PostLocalizationGramProducer
  directSignedResolvent : PostLocalizationGramProducer

firstPostLocalizationProducer : PostLocalizationGramProducer
firstPostLocalizationProducer = absoluteDataSchur

round214ConstantShellBandAlonePaysGramDebt : Bool
round214ConstantShellBandAlonePaysGramDebt = false

round214PhysicalSignedStructureStillRequired : Bool
round214PhysicalSignedStructureStillRequired = true

round214NoGoRefutesAbsoluteSchur : Bool
round214NoGoRefutesAbsoluteSchur = false

round214NoGoRefutesBlockOperatorControl : Bool
round214NoGoRefutesBlockOperatorControl = false

round214NoGoRefutesDirectSignedResolvent : Bool
round214NoGoRefutesDirectSignedResolvent = false

round214CCResidualBudgetClosed : Bool
round214CCResidualBudgetClosed = false

round214PackageAClosed : Bool
round214PackageAClosed = false

round214ClayPromotion : Bool
round214ClayPromotion = false

round214ConstantShellBandAlonePaysGramDebtIsFalse :
  round214ConstantShellBandAlonePaysGramDebt ≡ false
round214ConstantShellBandAlonePaysGramDebtIsFalse = refl

round214PhysicalSignedStructureStillRequiredIsTrue :
  round214PhysicalSignedStructureStillRequired ≡ true
round214PhysicalSignedStructureStillRequiredIsTrue = refl

round214NoGoRefutesAbsoluteSchurIsFalse :
  round214NoGoRefutesAbsoluteSchur ≡ false
round214NoGoRefutesAbsoluteSchurIsFalse = refl

round214NoGoRefutesBlockOperatorControlIsFalse :
  round214NoGoRefutesBlockOperatorControl ≡ false
round214NoGoRefutesBlockOperatorControlIsFalse = refl

round214NoGoRefutesDirectSignedResolventIsFalse :
  round214NoGoRefutesDirectSignedResolvent ≡ false
round214NoGoRefutesDirectSignedResolventIsFalse = refl
