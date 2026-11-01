{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralBCompletionRound425Exact where

------------------------------------------------------------------------
-- B / ROUND425: ONE LITERAL R406 -> PREFERRED R415 COMPLETION OBJECT
--
-- R421 owns the exact scalar compiler and asks only for the four-stage
-- operator/factor replay.  R423 owns representative choice from nonempty
-- selected fibres.  R422 transports the source (1.26)--(1.29) coordinates.
-- R419 then constructs the preferred selected source decay.
--
-- This owner makes those remaining literal source facts one object.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406ExactR410ReplayRound421Exact as R421
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116Round406NonemptySelectedFibreRound423Exact as R423
import DASHI.Physics.YangMills.BalabanCMP116Round406SupportGraphPreferredR415Round419Exact as R419
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred

record LiteralCMP116BCompletion
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    operatorReplay :
      R421.LiteralRound406R410OperatorReplay application

    selectedSource :
      R423.Equation126129SelectedR406NonemptyAttachment application

open LiteralCMP116BCompletion public

fromCanonicalFourStage :
  ∀ {Measure TestObservable dataSet extension base}
    (data :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  R423.Equation126129SelectedR406NonemptyAttachment
    (R429.canonicalApplication data) →
  LiteralCMP116BCompletion (R429.canonicalApplication data)
fromCanonicalFourStage data selected = record
  { operatorReplay = R429.canonicalOperatorReplay data
  ; selectedSource = selected
  }

asRound419Source :
  ∀ {Measure TestObservable dataSet extension base application} →
  LiteralCMP116BCompletion
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R419.LiteralRound406SupportGraphBSource application
asRound419Source {application = application} completion =
  R419.fromOperatorReplayAndPublished126129Nonempty
    (operatorReplay completion)
    (selectedSource completion)

preferredR415 :
  ∀ {Measure TestObservable dataSet extension base application} →
  LiteralCMP116BCompletion
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  Preferred.PreferredR415Source
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
preferredR415 completion =
  R419.compilePreferredR415 (asRound419Source completion)

round425LiteralBCompilerLevel : ProofLevel
round425LiteralBCompilerLevel = machineChecked

-- On the preferred R429 constructor the R406/R410 factor-layout payment is gone.
-- The remaining literal source attachments are:
-- * retained common-Y fibres are nonempty and selected membership survives;
-- * survivors carry the two-mark support graph/source metrics;
-- * CMP116 source domains/tree/shell are the literal R406 coordinates.
literalRound425BSourceAttachmentLevel : ProofLevel
literalRound425BSourceAttachmentLevel = conditional
