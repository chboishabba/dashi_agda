{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPreferredRowCSpatialFrontierRound261Exact where

------------------------------------------------------------------------
-- ROUND261 / ROW-C SPATIAL FRONTIER AFTER COMPACT-LIE GEOMETRY AUDIT
--
-- R262 tightens this cut further: C4a and C4b must now be paid by ONE literal
-- Langevin/Hessian source object, whose spatial site type is definitionally the
-- site type of the differentiated Langevin frame.  That same Hessian object is
-- also projected to the temporal Heat/Doob curvature consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieLangevinSkewConnectionCancellationExact as Langevin
import DASHI.Physics.YangMills.BalabanSharedMarkedHessianGeneratorRowExact as GeneratorRow
import DASHI.Physics.YangMills.BalabanLangevinHessianBidirectionalWeldRound262Exact as Bidi


data PreferredRowCSpatialLeaf261 : Set where
  literalDifferentiatedLangevinCommutator : PreferredRowCSpatialLeaf261
  literalSymmetricPartIsCMP109116HessianRow : PreferredRowCSpatialLeaf261


data LeafState261 : Set where
  open closed : LeafState261

preferredRowCSpatialLeafState261 : PreferredRowCSpatialLeaf261 → LeafState261
preferredRowCSpatialLeafState261 literalDifferentiatedLangevinCommutator = open
preferredRowCSpatialLeafState261 literalSymmetricPartIsCMP109116HessianRow = open

-- Historical broad levels remain visible for audit continuity.
literalDifferentiatedLangevinCommutatorLevel : ProofLevel
literalDifferentiatedLangevinCommutatorLevel =
  Langevin.physicalLiteralLangevinCommutatorIdentificationLevel

literalSymmetricPartCMP109116HessianRowLevel : ProofLevel
literalSymmetricPartCMP109116HessianRowLevel = conditional

-- Preferred current source cut: do not pay C4a and C4b independently.  Supply
-- one R262 literal source realization, which binds the exact Langevin site
-- carrier to the CMP109/CMP116 marked Hessian and exports both spatial and
-- temporal consumers from that same object.
preferredUnifiedC4SourceRealizationLevel : ProofLevel
preferredUnifiedC4SourceRealizationLevel =
  Bidi.round262LiteralSourceRealizationLevel

connectionQuadraticCancellationLevel : ProofLevel
connectionQuadraticCancellationLevel =
  Langevin.compactLieSkewQuadraticCancellationLevel

weightedGeneratorRowCompilerLevel : ProofLevel
weightedGeneratorRowCompilerLevel =
  GeneratorRow.sameObjectGeneratorRowToUniformWeightedBoundLevel

weightedAllDysonPowersCompilerLevel : ProofLevel
weightedAllDysonPowersCompilerLevel =
  GeneratorRow.sameObjectGeneratorRowToAllDysonPowerRowsLevel

-- The bidirectional adapter itself is compiler-owned; only its literal source
-- inhabitant remains physical debt.
bidirectionalSameHessianCompilerLevel : ProofLevel
bidirectionalSameHessianCompilerLevel = Bidi.round262BidiCompilerLevel

round261SpatialPhysicalClosure : Bool
round261SpatialPhysicalClosure = false

round261SpatialPhysicalClosureIsFalse : round261SpatialPhysicalClosure ≡ false
round261SpatialPhysicalClosureIsFalse = refl
