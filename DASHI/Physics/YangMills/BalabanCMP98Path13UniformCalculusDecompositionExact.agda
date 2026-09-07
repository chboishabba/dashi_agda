{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13UniformCalculusDecompositionExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): DECOMPOSE THE UNIFORM DIFFERENTIAL CALCULUS PAYMENT
--
-- R159's `UniformAdjointDifferentialCalculus` bundles two logically distinct
-- source obligations:
--
--   * exp/log differential data (`SU2ExpLogDifferentialData`), and
--   * realization of Ad_{exp Y} together with one explicit inverse law.
--
-- This owner separates those coordinates and recompiles the historical R159
-- record mechanically.  It is an ownership/type decomposition, not an
-- inhabitance claim for either physical coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159

record AdjointExpRealization (Lie : Set) : Set₁ where
  field
    adjointExp : Lie → Dexp.Endomorphism Lie
    adjointExpInverse : Lie → Dexp.Endomorphism Lie
    adjointInverseAfterExp : ∀ y vector →
      adjointExpInverse y (adjointExp y vector) ≡ vector
open AdjointExpRealization public

record SplitUniformAdjointDifferentialCalculus (Lie : Set) : Set₁ where
  field
    differential : Dexp.SU2ExpLogDifferentialData Lie
    adjoint : AdjointExpRealization Lie
open SplitUniformAdjointDifferentialCalculus public

asUniformAdjointDifferentialCalculus :
  ∀ {Lie} →
  SplitUniformAdjointDifferentialCalculus Lie →
  R159.UniformAdjointDifferentialCalculus Lie
asUniformAdjointDifferentialCalculus split = record
  { R159.UniformAdjointDifferentialCalculus.differential =
      differential split
  ; R159.UniformAdjointDifferentialCalculus.adjointExp =
      adjointExp (adjoint split)
  ; R159.UniformAdjointDifferentialCalculus.adjointExpInverse =
      adjointExpInverse (adjoint split)
  ; R159.UniformAdjointDifferentialCalculus.adjointInverseAfterExp =
      adjointInverseAfterExp (adjoint split)
  }

fromUniformAdjointDifferentialCalculus :
  ∀ {Lie} →
  R159.UniformAdjointDifferentialCalculus Lie →
  SplitUniformAdjointDifferentialCalculus Lie
fromUniformAdjointDifferentialCalculus calculus = record
  { SplitUniformAdjointDifferentialCalculus.differential =
      R159.differential calculus
  ; SplitUniformAdjointDifferentialCalculus.adjoint = record
      { AdjointExpRealization.adjointExp = R159.adjointExp calculus
      ; AdjointExpRealization.adjointExpInverse = R159.adjointExpInverse calculus
      ; AdjointExpRealization.adjointInverseAfterExp =
          R159.adjointInverseAfterExp calculus
      }
  }

splitRoundTrip :
  ∀ {Lie} (calculus : R159.UniformAdjointDifferentialCalculus Lie) →
  asUniformAdjointDifferentialCalculus
    (fromUniformAdjointDifferentialCalculus calculus)
  ≡ calculus
splitRoundTrip calculus = refl

cmp98Path13UniformCalculusDecompositionLevel : ProofLevel
cmp98Path13UniformCalculusDecompositionLevel = machineChecked

cmp98Path13ExpLogDifferentialCoordinateLevel : ProofLevel
cmp98Path13ExpLogDifferentialCoordinateLevel = conditional

cmp98Path13AdjointExpRealizationCoordinateLevel : ProofLevel
cmp98Path13AdjointExpRealizationCoordinateLevel = conditional
