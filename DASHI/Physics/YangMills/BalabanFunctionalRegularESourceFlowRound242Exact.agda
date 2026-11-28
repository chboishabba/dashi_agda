module DASHI.Physics.YangMills.BalabanFunctionalRegularESourceFlowRound242Exact where

------------------------------------------------------------------------
-- ROUND242 / REPRESENT THE CMP119 REGULAR E_k AS THE FUNCTION IT IS
--
-- CMP119's regular small-field term is an effective-action function of the
-- background.  Earlier source dictionaries kept `RegularTerm` abstract and then
-- paid a later pointwise-semantics weld.  The preferred source representation
-- instead chooses
--
--     RegularTerm = Background -> ℝ
--
-- at source construction time.  Hence regular-E extraction and pointwise
-- evaluation are projections/application, not independent physical theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Published
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Native
import DASHI.Physics.YangMills.BalabanBetaDrivenSourceNativePublishedFlowRound218Exact as R218

record FunctionalRegularESourceFlowInputs
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₂ where
  field
    Background Operation Action : Set
    RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    theorem1 :
      Published.Balaban1989Theorem1Witness
        (Beta.betaDrivenCompleteDensityFlow inputs)

    completeDensityAt : Nat →
      CMP119.CMP119Section2CompleteDensity
        ℚ (Beta.Density inputs) Operation Action Background
        (Background → ℝ) RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay

    densityIsBetaDensity : ∀ scale →
      CMP119.rho (completeDensityAt scale)
      ≡ Beta.densityAt inputs scale

    couplingIsBetaHistory : ∀ scale →
      CMP119.g (completeDensityAt scale)
      ≡ History.couplingAt (Beta.betaHistory inputs) scale

    -- Retained only because R218's compatibility carrier stores it.  The
    -- preferred BC1 source extraction below does not consume this coordinate.
    differentiatedAt : Nat → Native.CMP109DifferentiatedCoordinate (Background → ℝ)

open FunctionalRegularESourceFlowInputs public

asR218SourceNativeFlow :
  ∀ {trajectory split inputs} →
  FunctionalRegularESourceFlowInputs
    {trajectory = trajectory} {split = split} inputs →
  R218.BetaDrivenSourceNativePublishedFlowInputs inputs
asR218SourceNativeFlow dataSet = record
  { Operation = Operation dataSet
  ; Action = Action dataSet
  ; Field = Background dataSet
  ; RegularTerm = Background dataSet → ℝ
  ; RTerm = RTerm dataSet
  ; BoundaryTerm = BoundaryTerm dataSet
  ; VacuumTerm = VacuumTerm dataSet
  ; SmallFieldScale = SmallFieldScale dataSet
  ; BlockRadius = BlockRadius dataSet
  ; AnalyticRadius = AnalyticRadius dataSet
  ; Decay = Decay dataSet
  ; theorem1 = theorem1 dataSet
  ; completeDensityAt = completeDensityAt dataSet
  ; densityIsBetaDensity = densityIsBetaDensity dataSet
  ; couplingIsBetaHistory = couplingIsBetaHistory dataSet
  ; differentiatedAt = differentiatedAt dataSet
  }

selectedRegularEFunction :
  ∀ {trajectory split inputs}
    (dataSet : FunctionalRegularESourceFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  Nat → Background dataSet → ℝ
selectedRegularEFunction dataSet scale =
  CMP119.regularE (completeDensityAt dataSet scale)

functionalRegularESourceFlowCompilerLevel : ProofLevel
functionalRegularESourceFlowCompilerLevel = machineChecked

-- This is now the faithful source-realization leaf for the preferred BC1 entry:
-- instantiate the literal CMP119 complete-density family with its regular E_k
-- represented directly as a background-dependent real function.
literalFunctionalCMP119PublishedFlowLevel : ProofLevel
literalFunctionalCMP119PublishedFlowLevel = conditional
