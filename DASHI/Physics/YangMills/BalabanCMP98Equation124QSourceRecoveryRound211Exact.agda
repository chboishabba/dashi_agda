{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation124QSourceRecoveryRound211Exact where

------------------------------------------------------------------------
-- ROUND211 BIDI CORRECTION: RECOVER THE ACTUAL ONE-STEP Q(V0) LINEAR FORM
-- FROM CMP98 EQS. (122)--(125), NOT FROM THE EARLIER PRINTED Q'(V0) OPERATOR.
--
-- The repository already owns two complementary objects:
--
--   * BalabanSU2CMP98Equation124: an independent five-term transcription of
--     the printed Eq. (124) linear form, together with a source-exactness
--     equality for any inhabited transcription;
--
--   * BalabanSU2CMP98LiteralLinearization: the executable real-SU(2)
--     implementation of the linearized one-step average.
--
-- This owner makes their BIDI relationship explicit.  The qSource producer is
-- the Eq. (124) implementation itself.  Eq. (119)'s primed operator is kept
-- separate: no derivative or reconstruction interpretation is needed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanSU2CMP98Equation124 as Eq124
import DASHI.Physics.YangMills.BalabanSU2CMP98LinearizedAverage as Linear

------------------------------------------------------------------------
-- Source-exact qSource producer.
------------------------------------------------------------------------

qSourceFromEquation124 :
  ∀ {Input : Set} →
  Eq124.CMP98Equation124Transcription Input →
  Input → Lie.SU2LieAlgebra
qSourceFromEquation124 transcription = Eq124.implementation transcription

qSourceFromEquation124IsPrintedLinearForm :
  ∀ {Input : Set}
    (transcription : Eq124.CMP98Equation124Transcription Input)
    input →
  qSourceFromEquation124 transcription input
  ≡ Eq124.cmp98Equation124 (Eq124.terms transcription input)
qSourceFromEquation124IsPrintedLinearForm transcription =
  Eq124.cmp98LinearizationSourceExact transcription

------------------------------------------------------------------------
-- Same-object weld to an existing executable linear-average owner.
--
-- `executableAverage` is not a parallel qSource.  The equality below says that
-- its implementation is literally the Eq. (124) implementation on the same
-- input.  Once that equality is supplied, both source formula and executable
-- route identify the same qSource value.
------------------------------------------------------------------------

record Equation124ExecutableWeld
    (Input Support : Set) : Set₁ where
  field
    transcription : Eq124.CMP98Equation124Transcription Input
    executableAverage :
      Linear.CMP98LinearizedAverage Input Lie.SU2LieAlgebra Support

    sameImplementation : ∀ input →
      Linear.implementation executableAverage input
      ≡ Eq124.implementation transcription input

open Equation124ExecutableWeld public

recoveredQSource :
  ∀ {Input Support : Set} →
  Equation124ExecutableWeld Input Support →
  Input → Lie.SU2LieAlgebra
recoveredQSource weld = Linear.implementation (executableAverage weld)

recoveredQSourceIsEquation124Implementation :
  ∀ {Input Support : Set}
    (weld : Equation124ExecutableWeld Input Support)
    input →
  recoveredQSource weld input
  ≡ qSourceFromEquation124 (transcription weld) input
recoveredQSourceIsEquation124Implementation weld = sameImplementation weld

recoveredQSourceIsPrintedLinearForm :
  ∀ {Input Support : Set}
    (weld : Equation124ExecutableWeld Input Support)
    input →
  recoveredQSource weld input
  ≡ Eq124.cmp98Equation124 (Eq124.terms (transcription weld) input)
recoveredQSourceIsPrintedLinearForm weld input =
  trans
    (sameImplementation weld input)
    (Eq124.cmp98LinearizationSourceExact (transcription weld) input)

sourceFormulaIsRecoveredQSource :
  ∀ {Input Support : Set}
    (weld : Equation124ExecutableWeld Input Support)
    input →
  Linear.sourceFormula (executableAverage weld) input
  ≡ recoveredQSource weld input
sourceFormulaIsRecoveredQSource weld input =
  sym (Linear.linearizedAverageSourceEquality (executableAverage weld) input)

cmp98Equation124QSourceRecoveryRound211Level : ProofLevel
cmp98Equation124QSourceRecoveryRound211Level = machineChecked

cmp98Equation124ExecutableSameObjectCompilerRound211Level : ProofLevel
cmp98Equation124ExecutableSameObjectCompilerRound211Level = machineChecked

-- The source-exact five-term transcription owner and executable linearized
-- average are both already present in-repo.  The remaining physical payment is
-- the actual same-input inhabitant of `Equation124ExecutableWeld` at the chosen
-- Path13/background scale, not a theorem identifying Eq. (119) with qSource.
literalCMP98Equation124ExecutableWeldRound211Level : ProofLevel
literalCMP98Equation124ExecutableWeldRound211Level = conditional

-- Historical warning: the earlier R126/R146 route typed the printed primed
-- Eq. (119) operator as a derivative of qSource.  R211 does not use that typing.
-- Any future multiscale derivative theorem must be justified from the actual
-- source composition/linear-part semantics independently.
literalCMP98Equation119PrimeIsDerivativeOfQSourceRound211Level : ProofLevel
literalCMP98Equation119PrimeIsDerivativeOfQSourceRound211Level = conditional
