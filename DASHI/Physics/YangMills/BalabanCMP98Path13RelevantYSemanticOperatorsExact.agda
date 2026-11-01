{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13RelevantYSemanticOperatorsExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): RELEVANT-Y DIFFERENTIAL/ADJOINT SEMANTICS
--
-- The literal Eq.(119) source needs three operator families:
--   dExp_-(Y), J_-(Y), Ad_{exp Y}.
--
-- Only J_-(Y_x) needs to be certified as the inverse of dExp_-(Y_x), and the
-- physical Y_x values lie in a selected principal chart.  No global inverse
-- theorem for every Lie element is required, and no inverse for Ad_{exp Y} is
-- consumed by the equation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP98Path13MinimalSemanticCalculusExact as Minimal
import DASHI.Physics.YangMills.BalabanCMP98Path13DexpInversePairExact as Pair
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedAdjointExpFamilyExact as Adjoint
import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus as R
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record RelevantYSemanticOperators : Set₁ where
  field
    dexpMinus : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra
    jMinus : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra
    adjointExp : Lie.SU2LieAlgebra → Dexp.Endomorphism Lie.SU2LieAlgebra

    RelevantY : Lie.SU2LieAlgebra → Set

    dexpMinusAfterJminus : ∀ y → RelevantY y → ∀ vector →
      dexpMinus y (jMinus y vector) ≡ vector

    jMinusAfterDexpMinus : ∀ y → RelevantY y → ∀ vector →
      jMinus y (dexpMinus y vector) ≡ vector
open RelevantYSemanticOperators public

fromMinimalSemanticCalculus :
  Minimal.MinimalPath13SemanticCalculus → RelevantYSemanticOperators
fromMinimalSemanticCalculus calculus = record
  { RelevantYSemanticOperators.dexpMinus =
      Pair.dexpMinus (Minimal.dexpJminus calculus)
  ; RelevantYSemanticOperators.jMinus =
      Pair.jMinus (Minimal.dexpJminus calculus)
  ; RelevantYSemanticOperators.adjointExp =
      λ y vector → R.applyReducedAdjoint y
        (Adjoint.adjointOperator (Minimal.adjointExp calculus) y) vector
  ; RelevantYSemanticOperators.RelevantY = λ _ → ⊤
  ; RelevantYSemanticOperators.dexpMinusAfterJminus =
      λ y _ → Pair.dexpMinusAfterJminus (Minimal.dexpJminus calculus) y
  ; RelevantYSemanticOperators.jMinusAfterDexpMinus =
      λ y _ → Pair.jMinusAfterDexpMinus (Minimal.dexpJminus calculus) y
  }

minimalSemanticEveryYRelevant :
  ∀ calculus y →
  RelevantY (fromMinimalSemanticCalculus calculus) y
minimalSemanticEveryYRelevant calculus y = tt

cmp98Path13RelevantYSemanticOperatorsLevel : ProofLevel
cmp98Path13RelevantYSemanticOperatorsLevel = machineChecked

cmp98Path13GlobalAdjointInversePrunedLevel : ProofLevel
cmp98Path13GlobalAdjointInversePrunedLevel = machineChecked

literalCMP98Path13RelevantYSemanticInputsLevel : ProofLevel
literalCMP98Path13RelevantYSemanticInputsLevel = conditional
