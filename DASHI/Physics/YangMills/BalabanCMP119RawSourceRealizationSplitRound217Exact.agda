{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RawSourceRealizationSplitRound217Exact where

------------------------------------------------------------------------
-- ROUND217 / SPLIT THE LAST BUNDLED CMP119 SOURCE LEAF
--
-- The older frontier named one conditional leaf:
--
--   literal raw objects + literal Sect.-2 predicate instantiation.
--
-- Those are different source-realization coordinates.  The predicate vocabulary
-- must also be indexed by the raw state constructed from the exact objects, so
-- it cannot float independently or be reused on a neighboring density family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Theorem1
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact as Active
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as Existing

record LiteralCMP119RawSourceRealization
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData)
    (Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    objects : Existing.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum

    predicates : Raw.CMP119Section2PredicateFamily
      (Existing.rawStateFromFiniteBetaHistory objects)

open LiteralCMP119RawSourceRealization public

rawState :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum} →
  LiteralCMP119RawSourceRealization
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
    history Density Background Fluctuation Action WilsonTerm SmallFieldTerm
    RTerm BoundaryTerm Vacuum →
  Raw.CMP119SourceNativeRawState
    Density Background Fluctuation Action WilsonTerm SmallFieldTerm
    RTerm BoundaryTerm Vacuum
rawState realization = Existing.rawStateFromFiniteBetaHistory (objects realization)

runningCouplingIsFiniteBetaHistory :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum}
    (realization : LiteralCMP119RawSourceRealization
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
      history Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum) →
  ∀ scale →
  Raw.runningCoupling (rawState realization) scale
  ≡ History.couplingAt history scale
runningCouplingIsFiniteBetaHistory realization =
  Existing.runningCouplingIsFiniteHistoryCoupling (objects realization)

activeSection2FromPublishedTheorem :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum}
    (realization : LiteralCMP119RawSourceRealization
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
      history Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum) →
  Theorem1.ActiveBalaban1989Theorem1Witness
    (Active.asActiveEffectiveDensityFlow
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      (predicates realization)) →
  Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = rawState realization}
    (predicates realization)
activeSection2FromPublishedTheorem realization theorem1 =
  Existing.activeRawWitnessFromFiniteHistoryAndTheorem1
    (objects realization) theorem1

cmp119RawSourceSplitCompilerLevel : ProofLevel
cmp119RawSourceSplitCompilerLevel = machineChecked

cmp119RawCouplingSameObjectLevel : ProofLevel
cmp119RawCouplingSameObjectLevel = machineChecked

cmp122ActiveSection2FromSplitLevel : ProofLevel
cmp122ActiveSection2FromSplitLevel = machineChecked

-- Independent source-realization coordinates after the split.
literalCMP119RawObjectsOverHistoryLevel : ProofLevel
literalCMP119RawObjectsOverHistoryLevel = conditional

literalCMP119Section2PredicateVocabularyLevel : ProofLevel
literalCMP119Section2PredicateVocabularyLevel = conditional
