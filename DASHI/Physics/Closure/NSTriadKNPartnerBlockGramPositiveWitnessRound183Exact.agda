module DASHI.Physics.Closure.NSTriadKNPartnerBlockGramPositiveWitnessRound183Exact where

------------------------------------------------------------------------
-- ROUND183 / PARTNER COMPRESSION ALONE DOES NOT PAY THE GLOBAL GRAM DEBT
--
-- Round181 isolates the only remaining finite-fibre obstruction after exact
-- partner compression: the Gram debt BETWEEN compressed partner cells.
-- This file gives an exact positive witness.  Therefore no proof may silently
-- assume that partner compression itself makes the remaining debt nonpositive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181

F = R179.F

zeroCell : C3.Complex3 F
zeroCell = C3.complex3Zero F

alignedBlock : R181.CellPair
alignedBlock = R181.cell-pair R179.alignedCell zeroCell

twoAlignedBlocks : Agda.Builtin.List.List R181.CellPair
twoAlignedBlocks = alignedBlock ∷ alignedBlock ∷ []

alignedBlockCompressesToAlignedCell :
  R181.pairCell alignedBlock ≡ R179.alignedCell
alignedBlockCompressesToAlignedCell = refl

betweenDebtOfTwoAlignedBlocksIsTwo :
  R181.betweenPartnerDebt twoAlignedBlocks ≡ R179.two * 1ℚ
betweenDebtOfTwoAlignedBlocksIsTwo = solve []

compressedMassOfTwoAlignedBlocksIsFour :
  L2.complex3NormSquared
    (R180.sumCells (R181.pairCells twoAlignedBlocks))
  ≡ R179.two * (R179.two * 1ℚ)
compressedMassOfTwoAlignedBlocksIsFour = solve []

compressedIndividualMassSumIsTwo :
  R180.cellMassSum (R181.pairCells twoAlignedBlocks)
  ≡ R179.two * 1ℚ
compressedIndividualMassSumIsTwo = solve []

round183PartnerCompressionAutomaticallyMakesDebtNonpositive : Bool
round183PartnerCompressionAutomaticallyMakesDebtNonpositive = false

round183PhysicalPhaseOrTrajectoryStructureStillRequired : Bool
round183PhysicalPhaseOrTrajectoryStructureStillRequired = true

round183PackageAClosed : Bool
round183PackageAClosed = false

round183ClayPromotion : Bool
round183ClayPromotion = false
