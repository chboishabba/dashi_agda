{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13MinimalSemanticCalculusExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): MINIMAL SEMANTIC CALCULUS
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13DexpInversePairExact as DexpPair
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedAdjointExpFamilyExact as Adjoint
import DASHI.Physics.YangMills.BalabanCMP98Path13UniformCalculusDecompositionExact as Split
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record MinimalPath13SemanticCalculus : Set₁ where
  field
    dexpJminus : DexpPair.DexpJminusInversePair Lie.SU2LieAlgebra
    adjointExp : Adjoint.ReducedAdjointExpFamily
open MinimalPath13SemanticCalculus public

asSplitUniformCalculus :
  MinimalPath13SemanticCalculus →
  Split.SplitUniformAdjointDifferentialCalculus Lie.SU2LieAlgebra
asSplitUniformCalculus calculus = record
  { Split.SplitUniformAdjointDifferentialCalculus.differential =
      DexpPair.asExpLogDifferentialData (dexpJminus calculus)
  ; Split.SplitUniformAdjointDifferentialCalculus.adjoint =
      Adjoint.asAdjointExpRealization (adjointExp calculus)
  }

asUniformAdjointDifferentialCalculus :
  MinimalPath13SemanticCalculus →
  R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra
asUniformAdjointDifferentialCalculus calculus =
  Split.asUniformAdjointDifferentialCalculus (asSplitUniformCalculus calculus)

fromExistingFederbushConventionFamily :
  R177.ExistingFederbushConventionFamily →
  MinimalPath13SemanticCalculus
fromExistingFederbushConventionFamily family = record
  { MinimalPath13SemanticCalculus.dexpJminus =
      DexpPair.fromExpLogDifferentialData (R177.asExpLogDifferentialData family)
  ; MinimalPath13SemanticCalculus.adjointExp =
      Adjoint.fromExistingFederbushConventionFamily family
  }

cmp98Path13MinimalSemanticCalculusCompilerLevel : ProofLevel
cmp98Path13MinimalSemanticCalculusCompilerLevel = machineChecked

cmp98Path13HistoricalR177MinimalSemanticCompatibilityLevel : ProofLevel
cmp98Path13HistoricalR177MinimalSemanticCompatibilityLevel = machineChecked

literalCMP98Path13MinimalSemanticCalculusInputsLevel : ProofLevel
literalCMP98Path13MinimalSemanticCalculusInputsLevel = conditional
