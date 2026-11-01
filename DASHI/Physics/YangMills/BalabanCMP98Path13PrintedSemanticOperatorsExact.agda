{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13PrintedSemanticOperatorsExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): SOURCE-CORRECT PRINTED OPERATOR SEMANTICS
--
-- CMP98 prints
--   g(-i ad Y)          = dexpPlus,
--   g^{-1}(-i ad Y_x)  = Jplus,
--   R(e^{iY_x})         = Ad_exp.
--
-- Historical public field names such as `dexpMinusOuter` are compatibility
-- names only; Round148/153 pin the actual printed roles above.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record PrintedSemanticOperators : Set₁ where
  field
    dexpPlus : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra
    jPlus : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra
    adjointExp : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra

    RelevantY : Lie.SU2LieAlgebra → Set

    jPlusAfterDexpPlus : ∀ y → RelevantY y → ∀ vector →
      jPlus y (dexpPlus y vector) ≡ vector
open PrintedSemanticOperators public

fromR159UniformCalculus :
  R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra →
  PrintedSemanticOperators
fromR159UniformCalculus calculus = record
  { PrintedSemanticOperators.dexpPlus = R159.dexpPlusAt calculus
  ; PrintedSemanticOperators.jPlus = R159.jPlusAt calculus
  ; PrintedSemanticOperators.adjointExp = R159.adjointExp calculus
  ; PrintedSemanticOperators.RelevantY = λ _ → ⊤
  ; PrintedSemanticOperators.jPlusAfterDexpPlus =
      λ y _ → R159.jPlusAfterDexpPlus calculus y
  }

r159EveryYRelevant :
  ∀ calculus y → RelevantY (fromR159UniformCalculus calculus) y
r159EveryYRelevant calculus y = tt

asLeftRightAtY :
  R159.UniformAdjointDifferentialCalculus Lie.SU2LieAlgebra →
  Lie.SU2LieAlgebra → LR.LeftRightDexpCancellationData Lie.SU2LieAlgebra
asLeftRightAtY = R159.asLeftRightAtY

cmp98Path13PrintedSemanticOperatorsLevel : ProofLevel
cmp98Path13PrintedSemanticOperatorsLevel = machineChecked

cmp98Path13PrintedRoleCorrectionLevel : ProofLevel
cmp98Path13PrintedRoleCorrectionLevel = machineChecked

literalCMP98Path13PrintedSemanticInputsLevel : ProofLevel
literalCMP98Path13PrintedSemanticInputsLevel = conditional
