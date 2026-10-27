{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact where

------------------------------------------------------------------------
-- ROUND559 / CURRENT-MASTER GOAL-1 MAX-CUT + PARETO TOE NORMALIZATION
--
-- O. Objective.
-- Expose the existing R485 Goal-1 maximum cut and the R546/R558 scheduling
-- quotients through one theorem-owner normalization surface.
--
-- R. Reuse.
-- R485 remains the representation-safe Goal-1 theorem owner.
-- R546 remains the fourteen-family irreducible source owner.
-- R558 remains the seven-family critical-path owner.
-- This module copies no source proof and defines no duplicate family enum.
--
-- C. Composition.
-- R485 + R546 + R558 -> R559 -> TOE facades.
--
-- S. Safety invariants.
-- Conditional source facts remain conditional.
-- Compiler closure remains distinct from physical source closure.
-- Finite and represented statements do not promote continuum Yang-Mills.
-- Family counts are scheduling quotients, not theorem counts.
-- Clay completion remains false.
-- ESD and digital_esd implementation surfaces are not imported or edited.
--
-- L. Lane.
-- This lane owns only current-master Goal-1/Pareto normalization.
-- The merged Balaban RG normalization stays in DASHI.Unified.BalabanRGTOERegression.
--
-- P. Postcondition.
-- The TOE graph can reach every normalized R485 coordinate and the canonical
-- R546/R558 family dispatch without a parallel ontology.
--
-- G. Governance.
-- Original mathematical and repository theorem owners retain attribution.
-- Meta-introspector repositories retain separate authority.
-- ITIL, ISO 9000, ISO/IEC 42001/27001/27701/23894, ISO 9241,
-- NIST AI RMF, Six Sigma, and C4/PlantUML are process lenses only.
-- No certification claim is made.
--
-- F. Verification target.
-- The focused regression checks alias identity, false firewalls, family counts,
-- import reachability, trust escapes, and ESD path isolation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1MaximumCutRound485Exact as R485
import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound546Exact as R546
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Exact as R558

------------------------------------------------------------------------
-- Explicit O/R/C/S/L/P/G/F frame with preconditions, invariants, postconditions.
------------------------------------------------------------------------

record Goal1ParetoTOEZKPFrame : Set where
  field
    O R C S L P G F : String
    preconditions invariants postconditions : List String

open Goal1ParetoTOEZKPFrame public

canonicalGoal1ParetoTOEZKPFrame : Goal1ParetoTOEZKPFrame
canonicalGoal1ParetoTOEZKPFrame = record
  { O = "Normalize R485/R546/R558 into the existing DASHI TOE graph."
  ; R = "Reuse canonical theorem owners before adding aliases."
  ; C = "R485 + R546 + R558 -> R559 -> TOE facades."
  ; S = "Keep conditional facts conditional and all promotion gates fail-closed."
  ; L = "One disjoint Goal-1/Pareto normalization lane."
  ; P = "Expose the canonical maximum cut and scheduling quotients through TOE."
  ; G = "Preserve source attribution and repository authority boundaries."
  ; F = "Verify alias identity, firewalls, graph reachability, and path isolation."
  ; preconditions =
      "R485 is the authoritative representation-safe Goal-1 maximum cut."
      ∷ "R546 is the authoritative fourteen-family irreducible source frontier."
      ∷ "R558 is the authoritative seven-family critical path."
      ∷ []
  ; invariants =
      "R485/R546/R558 remain proof owners."
      ∷ "R559 is normalization only."
      ∷ "Unifier and TOE roots remain consumers."
      ∷ "No ESD or digital_esd mutation occurs."
      ∷ "No theorem authority is imported from meta-introspector repositories."
      ∷ "Continuum and Clay promotion remain fail-closed."
      ∷ []
  ; postconditions =
      "All normalized R485 coordinates are reachable through R559."
      ∷ "Canonical R546/R558 family types and dispatch remain reusable."
      ∷ "No duplicate family ontology is created."
      ∷ "Clay completion remains unclaimed."
      ∷ []
  }

------------------------------------------------------------------------
-- Current Goal-1 Clay maximum cut.
--
-- R485 is the representation-safe least-privilege Goal-1 route.
-- It consumes the historical R474 frontier and the R476--R506 specialization
-- tranche.  Re-export source mathematics and compiler closures separately.
------------------------------------------------------------------------

toeGoal1FiniteSymmetryAndRPSourceLevel : ProofLevel
toeGoal1FiniteSymmetryAndRPSourceLevel =
  R485.aFiniteSymmetryAndRPSourceLevel

toeGoal1A1CurrentStepBetaSourceLevel : ProofLevel
toeGoal1A1CurrentStepBetaSourceLevel =
  R485.a1CurrentStepBetaSourceLevel

toeGoal1A2GeneratedHistoryShellLevel : ProofLevel
toeGoal1A2GeneratedHistoryShellLevel =
  R485.a2GeneratedHistoryShellIsCMP116BetaMarkLevel

toeGoal1A3SourceNativeContinuumOSLevel : ProofLevel
toeGoal1A3SourceNativeContinuumOSLevel =
  R485.a3SourceNativeSameFamilyContinuumOSLevel

toeGoal1A3CountablyAdditiveRepresentationLevel : ProofLevel
toeGoal1A3CountablyAdditiveRepresentationLevel =
  R485.a3CountablyAdditiveRepresentationLevel

toeGoal1A3CylinderEventIndicatorSemanticsLevel : ProofLevel
toeGoal1A3CylinderEventIndicatorSemanticsLevel =
  R485.a3CylinderEventIndicatorSemanticsLevel

toeGoal1A3ProjectiveExpectationConsistencyLevel : ProofLevel
toeGoal1A3ProjectiveExpectationConsistencyLevel =
  R485.a3ProjectiveEventExpectationConsistencyLevel

toeGoal1A3ContinuityAtEmptyLevel : ProofLevel
toeGoal1A3ContinuityAtEmptyLevel =
  R485.a3ContinuityAtEmptyLevel

toeGoal1A3CaratheodoryExtensionLevel : ProofLevel
toeGoal1A3CaratheodoryExtensionLevel =
  R485.a3CaratheodoryExtensionLevel

toeGoal1A3CylinderExpectationIntegralLevel : ProofLevel
toeGoal1A3CylinderExpectationIntegralLevel =
  R485.a3CylinderExpectationIntegralIdentificationLevel

toeGoal1A45QuantitativeMomentToFiniteOS05Level : ProofLevel
toeGoal1A45QuantitativeMomentToFiniteOS05Level =
  R485.a45QuantitativeMomentToFiniteOS05Level

toeGoal1A4FiniteRegularityLevel : ProofLevel
toeGoal1A4FiniteRegularityLevel =
  R485.a4FiniteRegularityFromQuantitativeBoundsLevel

toeGoal1A5FiniteGrowthLevel : ProofLevel
toeGoal1A5FiniteGrowthLevel =
  R485.a5FiniteGrowthFromQuantitativeBoundsLevel

toeGoal1FiniteEuclideanSameObjectAttachmentLevel : ProofLevel
toeGoal1FiniteEuclideanSameObjectAttachmentLevel =
  R485.aFiniteEuclideanSameObjectAttachmentLevel

toeGoal1FiniteBosonicSameObjectAttachmentLevel : ProofLevel
toeGoal1FiniteBosonicSameObjectAttachmentLevel =
  R485.aFiniteBosonicSameObjectAttachmentLevel

toeGoal1FiniteWilsonRPSameObjectAttachmentLevel : ProofLevel
toeGoal1FiniteWilsonRPSameObjectAttachmentLevel =
  R485.aFiniteWilsonRPSameObjectAttachmentLevel

toeGoal1A3StressDensityIsLiteralFiniteMeasureLevel : ProofLevel
toeGoal1A3StressDensityIsLiteralFiniteMeasureLevel =
  R485.a3StressDensityIsLiteralFiniteMeasureLevel

toeGoal1A3FiniteFamilyContinuumLimitLevel : ProofLevel
toeGoal1A3FiniteFamilyContinuumLimitLevel =
  R485.a3FiniteFamilyContinuumLimitLevel

toeGoal1A3LiteralSchwingerBelongsLevel : ProofLevel
toeGoal1A3LiteralSchwingerBelongsLevel =
  R485.a3LiteralSchwingerBelongsLevel

toeGoal1A3SourceOSIsLiteralSchwingerLevel : ProofLevel
toeGoal1A3SourceOSIsLiteralSchwingerLevel =
  R485.a3SourceOSIsLiteralSchwingerLevel

toeGoal1A3FiniteProjectiveCylinderPremeasureLevel : ProofLevel
toeGoal1A3FiniteProjectiveCylinderPremeasureLevel =
  R485.a3FiniteProjectiveCylinderPremeasureLevel

toeGoal1A3RepresentedLiteralSemanticsLevel : ProofLevel
toeGoal1A3RepresentedLiteralSemanticsLevel =
  R485.a3RepresentedLiteralSemanticsLevel

toeGoal1A45QuantitativeFiniteExpectationAttachmentLevel : ProofLevel
toeGoal1A45QuantitativeFiniteExpectationAttachmentLevel =
  R485.a45QuantitativeFiniteExpectationAttachmentLevel

toeGoal1A45RepresentedOSPredicateExtensionalityLevel : ProofLevel
toeGoal1A45RepresentedOSPredicateExtensionalityLevel =
  R485.a45RepresentedOSPredicateExtensionalityLevel

toeGoal1A4RepresentedRegularityExtensionalityLevel : ProofLevel
toeGoal1A4RepresentedRegularityExtensionalityLevel =
  R485.a4RepresentedRegularityExtensionalityLevel

toeGoal1A5RepresentedGrowthExtensionalityLevel : ProofLevel
toeGoal1A5RepresentedGrowthExtensionalityLevel =
  R485.a5RepresentedGrowthExtensionalityLevel

toeGoal1BWilsonTwoInsertionConnectedShellLevel : ProofLevel
toeGoal1BWilsonTwoInsertionConnectedShellLevel =
  R485.bWilsonTwoInsertionConnectedShellLevel

toeGoal1BWilsonTwoMarkExpansionLevel : ProofLevel
toeGoal1BWilsonTwoMarkExpansionLevel =
  R485.bWilsonTwoMarkExpansionLevel

toeGoal1BWilsonConnectingWeightTailLevel : ProofLevel
toeGoal1BWilsonConnectingWeightTailLevel =
  R485.bWilsonConnectingWeightTailLevel

toeGoal1BWEXTAssemblyCompilerLevel : ProofLevel
toeGoal1BWEXTAssemblyCompilerLevel =
  R485.bWilsonWEXTAssemblyCompilerLevel

toeGoal1BSameHamiltonianTransferCoordinateLevel : ProofLevel
toeGoal1BSameHamiltonianTransferCoordinateLevel =
  R485.bSameHamiltonianTransferCoordinateLevel

toeGoal1BGeometricDecayCompilerLevel : ProofLevel
toeGoal1BGeometricDecayCompilerLevel =
  R485.bGeometricDecayCompilerLevel

toeGoal1BStandardSpectralTransferLevel : ProofLevel
toeGoal1BStandardSpectralTransferLevel =
  R485.bStandardSpectralTransferLevel

toeGoal1BLiteralHamiltonianGapSemanticsLevel : ProofLevel
toeGoal1BLiteralHamiltonianGapSemanticsLevel =
  R485.bLiteralHamiltonianGapSemanticsLevel

toeGoal1CSameFamilySourceInstantiationLevel : ProofLevel
toeGoal1CSameFamilySourceInstantiationLevel =
  R485.cSameFamilySourceInstantiationLevel

toeGoal1G1ArbitraryCompactSimpleSourceMapLevel : ProofLevel
toeGoal1G1ArbitraryCompactSimpleSourceMapLevel =
  R485.gArbitraryCompactSimpleSourceMapLevel

toeGoal1G2SameSystemNontrivialitySemanticsLevel : ProofLevel
toeGoal1G2SameSystemNontrivialitySemanticsLevel =
  R485.gSameSystemNontrivialitySemanticsLevel

toeGoal1RepresentedTerminalCompilerLevel : ProofLevel
toeGoal1RepresentedTerminalCompilerLevel =
  R485.round485RepresentedTerminalCompilerLevel

toeGoal1TerminalContractSemanticInventoryLevel : ProofLevel
toeGoal1TerminalContractSemanticInventoryLevel =
  R485.terminalContractSemanticInventoryLevel

toeGoal1MaximumCutCompilerLevel : ProofLevel
toeGoal1MaximumCutCompilerLevel =
  R485.round485MaximumCutCompilerLevel

toeGoal1ProjectiveProkhorovMandatory : Bool
toeGoal1ProjectiveProkhorovMandatory =
  R485.projectiveProkhorovMandatory

toeGoal1GlobalCoerciveCompactnessMandatory : Bool
toeGoal1GlobalCoerciveCompactnessMandatory =
  R485.globalCoerciveCompactnessRouteMandatory

toeGoal1PostHocContinuumMeasureWeldMandatory : Bool
toeGoal1PostHocContinuumMeasureWeldMandatory =
  R485.postHocContinuumMeasureFunctionalWeldMandatory

toeGoal1PostHocSchwingerEqualityMandatory : Bool
toeGoal1PostHocSchwingerEqualityMandatory =
  R485.postHocSchwingerEqualityMandatory

toeGoal1HistoricalSelectedJMinCutMandatory : Bool
toeGoal1HistoricalSelectedJMinCutMandatory =
  R485.historicalSelectedJMinCutMandatory

toeGoal1CompatibilityBRouteMandatory : Bool
toeGoal1CompatibilityBRouteMandatory =
  R485.r454R455CompatibilityBRouteMandatory

toeGoal1ArbitraryPositiveGapTokenMandatory : Bool
toeGoal1ArbitraryPositiveGapTokenMandatory =
  R485.arbitraryPositiveGapTokenMandatory

toeGoal1CMP109PolarizationDetourMandatory : Bool
toeGoal1CMP109PolarizationDetourMandatory =
  R485.cmp109PolarizationDetourMandatory

toeGoal1PrintedBalabanJEqualsWilsonObservableMandatory : Bool
toeGoal1PrintedBalabanJEqualsWilsonObservableMandatory =
  R485.printedBalabanJEqualsWilsonObservableMandatory

toeGoal1SU2ValidationMandatoryForGenericG : Bool
toeGoal1SU2ValidationMandatoryForGenericG =
  R485.su2ValidationMandatoryForGenericG

toeGoal1UniformConstantsAcrossAllGroupsMandatory : Bool
toeGoal1UniformConstantsAcrossAllGroupsMandatory =
  R485.uniformConstantsAcrossAllCompactSimpleGroupsMandatory

toeGoal1FreshContinuumStressLimitMandatory : Bool
toeGoal1FreshContinuumStressLimitMandatory =
  R485.freshContinuumStressLimitMandatory

toeGoal1IndependentFourthCumulantMandatory : Bool
toeGoal1IndependentFourthCumulantMandatory =
  R485.independentFourthCumulantMandatory

toeGoal1ClayCompletionClaimed : Bool
toeGoal1ClayCompletionClaimed =
  R485.clayCompletionClaimed

round559Goal1MaximumCutNormalizationCompilerLevel : ProofLevel
round559Goal1MaximumCutNormalizationCompilerLevel = machineChecked

------------------------------------------------------------------------
-- Current normalized source frontier.
------------------------------------------------------------------------

toeIrreducibleSourceFamilyCount : Nat
toeIrreducibleSourceFamilyCount =
  R546.preferredSourceFamilyCount

toeIrreducibleSourceFamilyCountIsFourteen :
  toeIrreducibleSourceFamilyCount ≡ 14
toeIrreducibleSourceFamilyCountIsFourteen = refl

toeCriticalFamilyCount : Nat
toeCriticalFamilyCount =
  R558.criticalFamilyCount

toeCriticalFamilyCountIsSeven :
  toeCriticalFamilyCount ≡ 7
toeCriticalFamilyCountIsSeven = refl

toeOpaqueEndpointPredicatesRemaining : Bool
toeOpaqueEndpointPredicatesRemaining =
  R546.opaqueEndpointPredicatesRemaining

toeOpaqueEndpointPredicatesRemainingIsFalse :
  toeOpaqueEndpointPredicatesRemaining ≡ false
toeOpaqueEndpointPredicatesRemainingIsFalse = refl

toeConstructorChoiceEqualitiesRemaining : Bool
toeConstructorChoiceEqualitiesRemaining =
  R546.constructorChoiceEqualitiesRemaining

toeConstructorChoiceEqualitiesRemainingIsFalse :
  toeConstructorChoiceEqualitiesRemaining ≡ false
toeConstructorChoiceEqualitiesRemainingIsFalse = refl

toeAllRemainingFamiliesAlreadyProved : Bool
toeAllRemainingFamiliesAlreadyProved =
  R546.allRemainingFamiliesAreAlreadyProved

toeAllRemainingFamiliesAlreadyProvedIsFalse :
  toeAllRemainingFamiliesAlreadyProved ≡ false
toeAllRemainingFamiliesAlreadyProvedIsFalse = refl

------------------------------------------------------------------------
-- Canonical R546 and R558 scheduling quotients.
--
-- Re-export the owner enums.
-- Do not define duplicate family types.
------------------------------------------------------------------------

open R546 public using
  ( SourceFamily
  ; a1CurrentStepVariation
  ; a2HistoryCoordinate
  ; a3ProjectiveRepresentation
  ; finiteT1AndPublishedOS
  ; quantitativeT5CMP119Alignment
  ; bWilsonWEXT
  ; bSameHamiltonianEnergyDecay
  ; actualGroupCompleteSource
  ; densityToNormalizedFiniteMeasure
  ; c0WilsonLocalObservable
  ; c1MarkedCurvature
  ; c2PhysicalRemainderTail
  ; c3AFRecurrence
  ; c4DensityAnchoredStress
  )

toeIrreducibleFamilyLevel : SourceFamily → ProofLevel
toeIrreducibleFamilyLevel =
  R546.familyLevel

open R558 public using
  ( CriticalFamily
  ; a3SelectedRepresentation
  ; t1FiniteOSSameFamily
  ; t5QuantitativeSameFamily
  ; b1SourceFirstWilsonWEXT
  ; b2SameHamiltonian
  ; g1ActualCompactSimple
  ; h6MinimalWardNontriviality
  )

toeCriticalFamilyLevel : CriticalFamily → ProofLevel
toeCriticalFamilyLevel =
  R558.criticalLevel

------------------------------------------------------------------------
-- R546 irreducible source-family subcuts.
------------------------------------------------------------------------

toeIrreducibleA3PositiveEventSemanticsLevel : ProofLevel
toeIrreducibleA3PositiveEventSemanticsLevel =
  R546.a3PositiveEventSemanticsLevel

toeIrreducibleA3EventBooleanAlgebraLevel : ProofLevel
toeIrreducibleA3EventBooleanAlgebraLevel =
  R546.a3EventBooleanAlgebraLevel

toeIrreducibleA3ProjectiveConsistencyLevel : ProofLevel
toeIrreducibleA3ProjectiveConsistencyLevel =
  R546.a3ProjectiveConsistencyLevel

toeIrreducibleA3ContinuityAtEmptyLevel : ProofLevel
toeIrreducibleA3ContinuityAtEmptyLevel =
  R546.a3ContinuityAtEmptyLevel

toeIrreducibleA3ExpectationIntegralIdentificationLevel : ProofLevel
toeIrreducibleA3ExpectationIntegralIdentificationLevel =
  R546.a3ExpectationIntegralIdentificationLevel

toeIrreducibleFiniteOSBosonicAttachmentLevel : ProofLevel
toeIrreducibleFiniteOSBosonicAttachmentLevel =
  R546.finiteOSBosonicAttachmentLevel

toeIrreducibleFiniteT1SourceBundleLevel : ProofLevel
toeIrreducibleFiniteT1SourceBundleLevel =
  R546.finiteT1SourceBundleLevel

toeIrreducibleAllGroupStructuralWitnessLevel : ProofLevel
toeIrreducibleAllGroupStructuralWitnessLevel =
  R546.allGroupStructuralWitnessLevel

toeIrreducibleAllGroupActualAlignmentLevel : ProofLevel
toeIrreducibleAllGroupActualAlignmentLevel =
  R546.allGroupActualAlignmentLevel

toeIrreducibleAllGroupFiveBlockSourceLevel : ProofLevel
toeIrreducibleAllGroupFiveBlockSourceLevel =
  R546.allGroupFiveBlockSourceLevel

toeIrreducibleWEXTTwoMarkExpansionLevel : ProofLevel
toeIrreducibleWEXTTwoMarkExpansionLevel =
  R546.wextTwoMarkExpansionLevel

toeIrreducibleWEXTConnectingWeightTailLevel : ProofLevel
toeIrreducibleWEXTConnectingWeightTailLevel =
  R546.wextConnectingWeightTailLevel

toeIrreducibleWholeMeasureRecordEqualitiesRemaining : Bool
toeIrreducibleWholeMeasureRecordEqualitiesRemaining =
  R546.wholeMeasureRecordEqualitiesRemaining

toeIrreducibleIndependentGroupSelectionsRemaining : Bool
toeIrreducibleIndependentGroupSelectionsRemaining =
  R546.independentStructuralAndQuantitativeGroupSelectionsRemaining

toeIrreducibleSU2PromotionRemaining : Bool
toeIrreducibleSU2PromotionRemaining =
  R546.su2PromotionRemaining

toeIrreducibleSingleCutoffMeasureExtensionRemaining : Bool
toeIrreducibleSingleCutoffMeasureExtensionRemaining =
  R546.singleCutoffMeasureExtensionRemaining

toeIrreducibleSourceFamilyCutCompilerLevel : ProofLevel
toeIrreducibleSourceFamilyCutCompilerLevel =
  R546.round546IrreducibleSourceFamilyCutCompilerLevel

------------------------------------------------------------------------
-- R558 critical-path subcuts.
------------------------------------------------------------------------

toeCriticalA3PositiveEventSemanticsLevel : ProofLevel
toeCriticalA3PositiveEventSemanticsLevel =
  R558.a3PositiveEventSemanticsLevel

toeCriticalA3BooleanAlgebraLevel : ProofLevel
toeCriticalA3BooleanAlgebraLevel =
  R558.a3BooleanAlgebraLevel

toeCriticalA3ProjectiveConsistencyLevel : ProofLevel
toeCriticalA3ProjectiveConsistencyLevel =
  R558.a3ProjectiveConsistencyLevel

toeCriticalA3ContinuityAtEmptyLevel : ProofLevel
toeCriticalA3ContinuityAtEmptyLevel =
  R558.a3ContinuityAtEmptyLevel

toeCriticalA3CylinderGeneratorRepresentationLevel : ProofLevel
toeCriticalA3CylinderGeneratorRepresentationLevel =
  R558.a3CylinderGeneratorRepresentationLevel

toeCriticalWEXTTwoMarkExpansionLevel : ProofLevel
toeCriticalWEXTTwoMarkExpansionLevel =
  R558.wextTwoMarkExpansionLevel

toeCriticalWEXTConnectingWeightTailLevel : ProofLevel
toeCriticalWEXTConnectingWeightTailLevel =
  R558.wextConnectingWeightTailLevel

toeCriticalFiniteToContinuumWilsonCovarianceLevel : ProofLevel
toeCriticalFiniteToContinuumWilsonCovarianceLevel =
  R558.finiteToContinuumWilsonCovarianceLevel

toeCriticalMassGapCompilerLevel : ProofLevel
toeCriticalMassGapCompilerLevel =
  R558.massGapCompilerLevel

toeCriticalMinimalH6CompilerLevel : ProofLevel
toeCriticalMinimalH6CompilerLevel =
  R558.minimalH6CompilerLevel

toeCriticalSeparateContinuumWilsonConvergenceFamilyRequired : Bool
toeCriticalSeparateContinuumWilsonConvergenceFamilyRequired =
  R558.separateContinuumWilsonConvergenceFamilyRequired

toeCriticalFiniteHamiltonianMoscoRouteRequired : Bool
toeCriticalFiniteHamiltonianMoscoRouteRequired =
  R558.finiteHamiltonianMoscoRouteRequired

toeCriticalPrintedJRouteRequired : Bool
toeCriticalPrintedJRouteRequired =
  R558.printedJRouteRequired

toeCriticalFullCLayerRequiredForMassGap : Bool
toeCriticalFullCLayerRequiredForMassGap =
  R558.fullCLayerRequiredForMassGap

toeCriticalFullCLayerRequiredForMinimalH6 : Bool
toeCriticalFullCLayerRequiredForMinimalH6 =
  R558.fullCLayerRequiredForMinimalH6

toeCriticalFullCLayerRetainedForConservativeClayExistence : Bool
toeCriticalFullCLayerRetainedForConservativeClayExistence =
  R558.fullCLayerRetainedForConservativeClayExistence

toeCriticalPathCompilerLevel : ProofLevel
toeCriticalPathCompilerLevel =
  R558.round558CriticalPathCompilerLevel

------------------------------------------------------------------------
