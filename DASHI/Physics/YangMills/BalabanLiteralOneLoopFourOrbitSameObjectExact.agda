module DASHI.Physics.YangMills.BalabanLiteralOneLoopFourOrbitSameObjectExact where

------------------------------------------------------------------------
-- ROUND66: SAME-OBJECT LITERAL ONE-LOOP -> FOUR ORBIT SUMS
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- The four-orbit reduction previously accepted an arbitrary rational cell
-- contribution.  That was still one same-object seam away from the literal
-- Wilson + gauge + ghost + Haar recursive evaluator.
--
-- This file removes that seam: the contribution being orbit-folded is
-- definitionally the lower (or upper) certified box contribution stored in the
-- GeneratedRegularMomentumBox produced by ONE LiteralGeneratedBoxEvaluator.
-- Hence the exact identity
--
--   sum_regular lower_B = S1 + S2 + S3 + S4
--
-- and its upper analogue are now statements about the literal evaluator's own
-- boxes, not an observationally similar external function.  Physical interval
-- work remains only in constructing the evaluator/receipts themselves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralMomentumDiagramBoxDataExact as Momentum
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Literal
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact as OrbitSum
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

literalLowerContribution :
  ∀ {expressions ward scalarData} →
  Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Grid.GridCell4 → ℚ
literalLowerContribution evaluator cell =
  Momentum.lowerContribution (Literal.generatedBox evaluator cell)

literalUpperContribution :
  ∀ {expressions ward scalarData} →
  Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData →
  Grid.GridCell4 → ℚ
literalUpperContribution evaluator cell =
  Momentum.upperContribution (Literal.generatedBox evaluator cell)

literalRegularLowerSum :
  ∀ {expressions ward scalarData} →
  Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData → ℚ
literalRegularLowerSum evaluator =
  Sums.sumRational Grid.regularGridCells (literalLowerContribution evaluator)

literalRegularUpperSum :
  ∀ {expressions ward scalarData} →
  Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData → ℚ
literalRegularUpperSum evaluator =
  Sums.sumRational Grid.regularGridCells (literalUpperContribution evaluator)

literalLowerSumIsFourJointOrbits :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  literalRegularLowerSum evaluator
  ≡ OrbitSum.oneOuterOrbitSum (literalLowerContribution evaluator)
    + OrbitSum.twoOuterOrbitSum (literalLowerContribution evaluator)
    + OrbitSum.threeOuterOrbitSum (literalLowerContribution evaluator)
    + OrbitSum.fourOuterOrbitSum (literalLowerContribution evaluator)
literalLowerSumIsFourJointOrbits evaluator =
  OrbitSum.regularCellSumAsFourJointOrbitSums
    (literalLowerContribution evaluator)

literalUpperSumIsFourJointOrbits :
  ∀ {expressions ward scalarData}
    (evaluator : Literal.LiteralGeneratedBoxEvaluator expressions ward scalarData) →
  literalRegularUpperSum evaluator
  ≡ OrbitSum.oneOuterOrbitSum (literalUpperContribution evaluator)
    + OrbitSum.twoOuterOrbitSum (literalUpperContribution evaluator)
    + OrbitSum.threeOuterOrbitSum (literalUpperContribution evaluator)
    + OrbitSum.fourOuterOrbitSum (literalUpperContribution evaluator)
literalUpperSumIsFourJointOrbits evaluator =
  OrbitSum.regularCellSumAsFourJointOrbitSums
    (literalUpperContribution evaluator)

literalOneLoopSameObjectOrbitFoldLevel : ProofLevel
literalOneLoopSameObjectOrbitFoldLevel = machineChecked

-- Physical leaf L2/L3 is now exactly the construction of the literal Ward
-- scalar/evaluator and the four joint interval enclosures of THESE sums.
literalWardScalarEvaluatorConstructionLevel : ProofLevel
literalWardScalarEvaluatorConstructionLevel = conditional

literalFourJointOrbitEnclosureLevel : ProofLevel
literalFourJointOrbitEnclosureLevel = conditional
