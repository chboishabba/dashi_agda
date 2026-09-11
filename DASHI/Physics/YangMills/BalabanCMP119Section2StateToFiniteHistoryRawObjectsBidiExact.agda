{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119Section2StateToFiniteHistoryRawObjectsBidiExact where

------------------------------------------------------------------------
-- BURIED-DONOR REUSE / CMP119 SECTION-2 STATE -> FINITE-HISTORY RAW OBJECTS
--
-- Archaeology found that the older source-native Section-2 state already owns
-- exactly the non-coupling objects later requested by
-- `CMP119RawObjectsOverHistory`:
--
--   density, background, fluctuations,
--   Wilson/E/R/B/vacuum pieces, effective action, and Eq. (2.23).
--
-- It also already owns the five predicate *vocabularies* later requested by
-- `CMP119Section2PredicateFamily`.
--
-- Therefore those two Round217 coordinates are representation/compiler output
-- once one literal source-native CMP119 state has been instantiated.  The
-- finite-history constructor remains authoritative for the running coupling;
-- this module does NOT silently assert that an arbitrary older state's coupling
-- equals the selected finite beta history.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Old
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as Existing
import DASHI.Physics.YangMills.BalabanCMP119RawSourceRealizationSplitRound217Exact as R217

------------------------------------------------------------------------
-- The two action-algebra records are the same operation with different owners.
------------------------------------------------------------------------

oldActionAlgebraToRaw :
  ∀ {Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  Old.CMP119ActionAlgebra
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum →
  Raw.CMP119RawActionAlgebra
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
oldActionAlgebraToRaw algebra = record
  { Raw.CMP119RawActionAlgebra.assemble = Old.assemble algebra }

------------------------------------------------------------------------
-- Non-coupling source objects -> finite-history raw object package.
------------------------------------------------------------------------

sourceStateToRawObjectsOverHistory :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set} →
  Old.CMP119Section2SourceNativeState
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum →
  Existing.CMP119RawObjectsOverHistory history
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
sourceStateToRawObjectsOverHistory source = record
  { Existing.CMP119RawObjectsOverHistory.terminalScale = Old.terminalScale source
  ; Existing.CMP119RawObjectsOverHistory.effectiveDensity = Old.effectiveDensity source
  ; Existing.CMP119RawObjectsOverHistory.backgroundField = Old.backgroundField source
  ; Existing.CMP119RawObjectsOverHistory.fluctuationFields = Old.fluctuationFields source
  ; Existing.CMP119RawObjectsOverHistory.wilsonActionTerm = Old.wilsonActionTerm source
  ; Existing.CMP119RawObjectsOverHistory.regularSmallFieldTerm = Old.regularSmallFieldTerm source
  ; Existing.CMP119RawObjectsOverHistory.rOperationTerm = Old.rOperationTerm source
  ; Existing.CMP119RawObjectsOverHistory.boundaryTerm = Old.boundaryTerm source
  ; Existing.CMP119RawObjectsOverHistory.vacuumEnergy = Old.vacuumEnergy source
  ; Existing.CMP119RawObjectsOverHistory.effectiveAction = Old.effectiveAction source
  ; Existing.CMP119RawObjectsOverHistory.actionAlgebra =
      oldActionAlgebraToRaw (Old.actionAlgebra source)
  ; Existing.CMP119RawObjectsOverHistory.wilsonCoefficient = Old.wilsonCoefficient source
  ; Existing.CMP119RawObjectsOverHistory.equation223 = Old.equation223 source
  }

------------------------------------------------------------------------
-- The predicate vocabulary is already carried by the older source-native state.
-- No Sect.-2 *proof* is imported here; only the predicate families themselves.
------------------------------------------------------------------------

sourceStatePredicateVocabulary :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (source : Old.CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) →
  Raw.CMP119Section2PredicateFamily
    (Existing.rawStateFromFiniteBetaHistory
      (sourceStateToRawObjectsOverHistory {history = history} source))
sourceStatePredicateVocabulary source = record
  { Raw.CMP119Section2PredicateFamily.ELocalizedAnalytic = Old.ELocalizedAnalytic source
  ; Raw.CMP119Section2PredicateFamily.RLocalizedAnalytic = Old.RLocalizedAnalytic source
  ; Raw.CMP119Section2PredicateFamily.BLocalizedAnalytic = Old.BLocalizedAnalytic source
  ; Raw.CMP119Section2PredicateFamily.RegularBackground = Old.RegularBackground source
  ; Raw.CMP119Section2PredicateFamily.CompleteDensityForm = Old.CompleteDensityForm source
  }

------------------------------------------------------------------------
-- Direct Round217 realization compiler.
------------------------------------------------------------------------

sourceStateBuildsRound217Realization :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set} →
  (source : Old.CMP119Section2SourceNativeState
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) →
  R217.LiteralCMP119RawSourceRealization
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
    history Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
sourceStateBuildsRound217Realization {history = history} source = record
  { R217.LiteralCMP119RawSourceRealization.objects =
      sourceStateToRawObjectsOverHistory {history = history} source
  ; R217.LiteralCMP119RawSourceRealization.predicates =
      sourceStatePredicateVocabulary {history = history} source
  }

------------------------------------------------------------------------
-- Boundary / proof-search correction.
------------------------------------------------------------------------

record BuriedCMP119DonorBoundary : Set where
  constructor buried-cmp119-donor-boundary
  field
    rawObjectsOverHistoryIndependentConstructionLeaf : Bool
    rawObjectsOverHistoryIndependentConstructionLeafIsFalse :
      rawObjectsOverHistoryIndependentConstructionLeaf ≡ false

    section2PredicateVocabularyIndependentConstructionLeaf : Bool
    section2PredicateVocabularyIndependentConstructionLeafIsFalse :
      section2PredicateVocabularyIndependentConstructionLeaf ≡ false

    olderSourceNativeStateIsBuriedDonor : Bool
    olderSourceNativeStateIsBuriedDonorIsTrue :
      olderSourceNativeStateIsBuriedDonor ≡ true

    finiteHistoryRunningCouplingRemainsAuthoritative : Bool
    finiteHistoryRunningCouplingRemainsAuthoritativeIsTrue :
      finiteHistoryRunningCouplingRemainsAuthoritative ≡ true

    arbitraryOldCouplingEqualsFiniteHistoryCoupling : Bool
    arbitraryOldCouplingEqualsFiniteHistoryCouplingIsFalse :
      arbitraryOldCouplingEqualsFiniteHistoryCoupling ≡ false

    literalSourceNativeStateInstantiationStillPhysical : Bool
    literalSourceNativeStateInstantiationStillPhysicalIsTrue :
      literalSourceNativeStateInstantiationStillPhysical ≡ true

canonicalBuriedCMP119DonorBoundary : BuriedCMP119DonorBoundary
canonicalBuriedCMP119DonorBoundary =
  buried-cmp119-donor-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl

buriedCMP119ReuseCompilerLevel : ProofLevel
buriedCMP119ReuseCompilerLevel = machineChecked

literalCMP119SourceNativeStateInstantiationLevel : ProofLevel
literalCMP119SourceNativeStateInstantiationLevel = Old.cmp119LiteralCompleteDensityInstantiationLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
