{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13ReducedAdjointExpFamilyExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): MINIMAL REDUCED ADJOINT EXP REALIZATION
--
-- The real-Lie Eq.(119) consumer needs Ad_{exp Y} and one inverse law.  The
-- repository's native SU(2) operator algebra is the reduced span
-- {I, ad_Y, ad_Y^2}; keep the source coordinate there rather than accepting an
-- arbitrary endomorphism family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus as R
import DASHI.Physics.YangMills.BalabanCMP98Path13UniformCalculusDecompositionExact as Split
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushConventionCancellationExact as Federbush

record ReducedAdjointExpFamily : Set₁ where
  field
    adjointOperator : Lie.SU2LieAlgebra → R.ReducedAdjointOperator
    inverseAdjointOperator : Lie.SU2LieAlgebra → R.ReducedAdjointOperator

    inverseAfterAdjoint : ∀ y →
      R.composeReducedAdjoint y
        (inverseAdjointOperator y)
        (adjointOperator y)
      ≡ R.identityReducedAdjoint
open ReducedAdjointExpFamily public

asAdjointExpRealization :
  ReducedAdjointExpFamily →
  Split.AdjointExpRealization Lie.SU2LieAlgebra
asAdjointExpRealization family = record
  { Split.AdjointExpRealization.adjointExp =
      λ y vector → R.applyReducedAdjoint y (adjointOperator family y) vector
  ; Split.AdjointExpRealization.adjointExpInverse =
      λ y vector → R.applyReducedAdjoint y (inverseAdjointOperator family y) vector
  ; Split.AdjointExpRealization.adjointInverseAfterExp =
      λ y vector →
        trans
          (R.applyReducedComposition y
            (inverseAdjointOperator family y)
            (adjointOperator family y) vector)
          (trans
            (cong (λ operator → R.applyReducedAdjoint y operator vector)
              (inverseAfterAdjoint family y))
            (R.applyIdentityReducedAdjoint y vector))
  }

fromExistingFederbushConventionFamily :
  R177.ExistingFederbushConventionFamily →
  ReducedAdjointExpFamily
fromExistingFederbushConventionFamily family = record
  { ReducedAdjointExpFamily.adjointOperator =
      λ y → Federbush.adjointTransport (R177.atY family y)
  ; ReducedAdjointExpFamily.inverseAdjointOperator =
      λ y → R177.adjointInverseOperator y (R177.atY family y)
  ; ReducedAdjointExpFamily.inverseAfterAdjoint =
      λ y → R177.adjointInverseAfterAdjointIsIdentity y (R177.atY family y)
  }

cmp98Path13ReducedAdjointExpFamilyCompilerLevel : ProofLevel
cmp98Path13ReducedAdjointExpFamilyCompilerLevel = machineChecked

cmp98Path13HistoricalR177AdjointCompatibilityLevel : ProofLevel
cmp98Path13HistoricalR177AdjointCompatibilityLevel = machineChecked

literalCMP98Path13ReducedAdjointExpIdentificationLevel : ProofLevel
literalCMP98Path13ReducedAdjointExpIdentificationLevel = conditional
