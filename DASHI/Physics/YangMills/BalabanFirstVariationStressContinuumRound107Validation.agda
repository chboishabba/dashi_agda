{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFirstVariationStressContinuumRound107Validation where

import DASHI.Physics.YangMills.BalabanFirstVariationStressContinuumRound107Exact as R107
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.CompactLieProofLevel as Level

continuumStressCompiler :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    (receipt : R107.LiteralSectorStressContinuumReceipt Y group)
    perturbation →
  R107.AdmissibleMetricPerturbation receipt perturbation →
  R107.continuumFirstVariation receipt perturbation
  ≡ R107.stressMetricPairing receipt (Top.stressTensor Y group) perturbation
continuumStressCompiler = R107.continuumFirstVariationRepresentedByLiteralStress

continuumStressCompilerLevel : Level.ProofLevel
continuumStressCompilerLevel = R107.stressContinuumCompilerLevel
