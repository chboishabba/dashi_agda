{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRowCSpatialFrontierRound261Exact where

------------------------------------------------------------------------
-- ROUND261 / ROW-C SPATIAL FRONTIER AFTER COMPACT-LIE GEOMETRY AUDIT
--
-- The older preferred spatial leaf
--
--   "literal Heat/Doob weighted generator row = CMP116 Hessian row"
--
-- is too coarse.  Current in-repo geometry already separates the differentiated
-- Langevin generator into:
--
--   symmetric nonlocal action-Hessian part
--     + onsite compact-Lie connection/ad part.
--
-- The second piece contributes exactly ZERO quadratic derivative-energy growth
-- once the physical connection is identified with the bi-invariant adjoint
-- action.  Therefore the preferred physical source cut is:
--
--   C4a  literal differentiated Langevin commutator has the standard
--        compact-group decomposition on the exact finite Yang--Mills carrier;
--
--   C4b  its symmetric nonlocal part is the SAME literal CMP109/CMP116 Hessian
--        row already controlled by the marked source estimate.
--
-- Connection/ad cancellation, weighted-row propagation, and all Dyson powers
-- are downstream theorem/compiler output.  This file intentionally does not
-- invent an opaque replacement theorem claiming C4a or C4b is solved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as GeneratorRow


data PreferredRowCSpatialLeaf261 : Set where
  literalDifferentiatedLangevinCommutator : PreferredRowCSpatialLeaf261
  literalSymmetricPartIsCMP109116HessianRow : PreferredRowCSpatialLeaf261


data LeafState261 : Set where
  open closed : LeafState261

preferredRowCSpatialLeafState261 : PreferredRowCSpatialLeaf261 → LeafState261
preferredRowCSpatialLeafState261 literalDifferentiatedLangevinCommutator = open
preferredRowCSpatialLeafState261 literalSymmetricPartIsCMP109116HessianRow = open

-- Exact existing authority for C4a.  The record also carries the physical
-- connection-is-ad identification; once that identification is paid, the
-- connection contribution is eliminated by the theorem below.
literalDifferentiatedLangevinCommutatorLevel : ProofLevel
literalDifferentiatedLangevinCommutatorLevel =
  Langevin.physicalLiteralLangevinCommutatorIdentificationLevel

-- C4b remains the genuinely Yang--Mills-specific same-object source weld.  The
-- older generator-row level is kept only as the nearest existing broad owner;
-- this frontier states the strictly smaller missing content explicitly rather
-- than claiming the broad row theorem has been constructed.
literalSymmetricPartCMP109116HessianRowLevel : ProofLevel
literalSymmetricPartCMP109116HessianRowLevel = conditional

-- Standard/compiler-closed geometry after C4a identifies the physical
-- connection with the compact-Lie adjoint term.
connectionQuadraticCancellationLevel : ProofLevel
connectionQuadraticCancellationLevel =
  Langevin.compactLieSkewQuadraticCancellationLevel

-- Once C4b gives the literal weighted Hessian row, all quantitative row and
-- Dyson-power estimates are already compiled by the historical spatial owner.
weightedGeneratorRowCompilerLevel : ProofLevel
weightedGeneratorRowCompilerLevel =
  GeneratorRow.sameObjectGeneratorRowToUniformWeightedBoundLevel

weightedAllDysonPowersCompilerLevel : ProofLevel
weightedAllDysonPowersCompilerLevel =
  GeneratorRow.sameObjectGeneratorRowToAllDysonPowerRowsLevel

round261SpatialPhysicalClosure : Bool
round261SpatialPhysicalClosure = false

round261SpatialPhysicalClosureIsFalse : round261SpatialPhysicalClosure ≡ false
round261SpatialPhysicalClosureIsFalse = refl
