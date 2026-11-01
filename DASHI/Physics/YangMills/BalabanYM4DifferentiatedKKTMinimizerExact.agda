module DASHI.Physics.YangMills.BalabanYM4DifferentiatedKKTMinimizerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numerique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- DASHI CONTRIBUTION
--
-- RG1d must differentiate the CONSTRAINED minimizer, not an unconstrained
-- action equation.  On the existing physical KKT carrier, if the literal
-- differentiated Euler--Lagrange/constraint pair is
--
--       [ H  L* ] [deltaA     ]   [ f ]
--       [ L   0 ] [deltaLambda] = [ g ],
--
-- then the already-constructed finite KKT Green solve is exactly that pair.
-- Coercivity on ker L and reduced multiplier injectivity make the KKT block
-- injective, so no independent response object can be chosen.
--
-- The remaining physical work after this module is sharply limited to:
--   (1) differentiating the literal selected-minimizer equations to produce
--       the f/g source pair on this same carrier;
--   (2) proving finite/remote support of that source pair;
--   (3) applying the existing Combes--Thomas response bounds and integrating
--       the uniform derivative estimate along an admissible background path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenAlgebraExact as Algebra
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact as Block
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockInverseExact as Inverse

record DifferentiatedKKTMinimizerData (Multiplier : Set) : Set₁ where
  field
    greenData : Algebra.ConstrainedGreenData Multiplier
    coercivity : Inverse.ReducedKKTCoercivity greenData

    differentiatedPair : Block.KKTBlockVector Multiplier
    stateSource : Block.KKTBlockVector Multiplier

    -- Literal differentiated KKT equation.  The source is kept as one block so
    -- the second component may carry the differentiated averaging constraint;
    -- setting it to zero is a later physical specialization, not assumed here.
    differentiatedKKTEquation :
      Block.PointwiseKKTBlockEquality
        (Block.applyKKTBlock greenData differentiatedPair)
        stateSource

open DifferentiatedKKTMinimizerData public

differentiatedPairIsKKTGreenSolve :
  ∀ {Multiplier}
    (dataSet : DifferentiatedKKTMinimizerData Multiplier) →
  Block.PointwiseKKTBlockEquality
    (differentiatedPair dataSet)
    (Block.solveKKTBlock (greenData dataSet) (stateSource dataSet))
differentiatedPairIsKKTGreenSolve dataSet =
  Inverse.finiteKKTBlockInjective
    (coercivity dataSet)
    record
      { Block.PointwiseKKTBlockEquality.stateEqual = λ coordinate →
          let
            literal = Block.stateEqual
              (differentiatedKKTEquation dataSet) coordinate
            solved = Block.stateEqual
              (Block.kktBlockRightInverseExact
                (greenData dataSet) (stateSource dataSet)) coordinate
          in
          trans literal (sym solved)
      ; Block.PointwiseKKTBlockEquality.multiplierEqual = λ row →
          let
            literal = Block.multiplierEqual
              (differentiatedKKTEquation dataSet) row
            solved = Block.multiplierEqual
              (Block.kktBlockRightInverseExact
                (greenData dataSet) (stateSource dataSet)) row
          in
          trans literal (sym solved)
      }
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)

differentiatedStateIsKKTGreenState :
  ∀ {Multiplier}
    (dataSet : DifferentiatedKKTMinimizerData Multiplier) coordinate →
  Block.statePart (differentiatedPair dataSet) coordinate
  ≡ Block.statePart
      (Block.solveKKTBlock (greenData dataSet) (stateSource dataSet)) coordinate
differentiatedStateIsKKTGreenState dataSet =
  Block.stateEqual (differentiatedPairIsKKTGreenSolve dataSet)

differentiatedMultiplierIsKKTGreenMultiplier :
  ∀ {Multiplier}
    (dataSet : DifferentiatedKKTMinimizerData Multiplier) row →
  Block.multiplierPart (differentiatedPair dataSet) row
  ≡ Block.multiplierPart
      (Block.solveKKTBlock (greenData dataSet) (stateSource dataSet)) row
differentiatedMultiplierIsKKTGreenMultiplier dataSet =
  Block.multiplierEqual (differentiatedPairIsKKTGreenSolve dataSet)

ym4DifferentiatedKKTMinimizerIdentificationLevel : ProofLevel
ym4DifferentiatedKKTMinimizerIdentificationLevel = machineChecked

ym4LiteralDifferentiatedKKTSourceProducerLevel : ProofLevel
ym4LiteralDifferentiatedKKTSourceProducerLevel = conditional

ym4DifferentiatedKKTSourceSupportLevel : ProofLevel
ym4DifferentiatedKKTSourceSupportLevel = conditional
