{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound544Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND544: PREFERRED IRREDUCIBLE SOURCE-FAMILY FRONTIER
--
-- This is the post-R542/R543 theorem-family cut.
--
-- Every historical constructor/equality/opaque-endpoint debt has already been
-- compiled away on the preferred source-first + represented route.  The
-- remaining work is organized into FIFTEEN proof-bearing source families.
--
-- This is a scheduling quotient, NOT a claim that each family is one atomic
-- lemma.  Each family keeps its internal logical subclaims visible through the
-- imported owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact as A1
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as A2
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as A3
import DASHI.Physics.YangMills.YangMillsFiniteOSFromConcreteT1Round532Exact as FiniteOS
import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as Quantitative
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Exact as B
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as AllG
import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as T1
import DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact as Density
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFromStructuralRound530Exact as C0
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C
import DASHI.Physics.YangMills.YangMillsCylinderEventBooleanAlgebraRound539Exact as EventAlgebra

data SourceFamily : Set where
  a1CurrentStepVariation : SourceFamily
  a2HistoryCoordinate : SourceFamily
  a3ProjectiveRepresentation : SourceFamily
  finiteT1AndPublishedOS : SourceFamily
  quantitativeT5CMP119Alignment : SourceFamily
  bWilsonWEXT : SourceFamily
  bSameHamiltonianEnergyDecay : SourceFamily
  actualGroupCompleteSource : SourceFamily
  densityToNormalizedFiniteMeasure : SourceFamily
  c0WilsonLocalObservable : SourceFamily
  c1MarkedCurvature : SourceFamily
  c2PhysicalRemainderTail : SourceFamily
  c3AFRecurrence : SourceFamily
  c4DensityAnchoredStress : SourceFamily
  cylinderEventBooleanRealization : SourceFamily

familyLevel : SourceFamily → ProofLevel
familyLevel a1CurrentStepVariation =
  A1.literalRound473A1SourceInstantiationLevel
familyLevel a2HistoryCoordinate =
  A2.literalCMP116BetaMarkIsGeneratedHistoryShellLevel
familyLevel a3ProjectiveRepresentation =
  conditional
familyLevel finiteT1AndPublishedOS =
  conditional
familyLevel quantitativeT5CMP119Alignment =
  Quantitative.literalRound514SameFiniteExpectationAttachmentLevel
familyLevel bWilsonWEXT =
  conditional
familyLevel bSameHamiltonianEnergyDecay =
  B.bSameHamiltonianLevel
familyLevel actualGroupCompleteSource =
  AllG.literalRound543ActualGroupCompleteSourceLevel
familyLevel densityToNormalizedFiniteMeasure =
  Density.literalRound525DensityToFiniteMeasureMapLevel
familyLevel c0WilsonLocalObservable =
  C0.literalRound530StructuralWilsonLocalDataLevel
familyLevel c1MarkedCurvature =
  C.c1MarkedCurvatureFamilyLevel
familyLevel c2PhysicalRemainderTail =
  C.c2PhysicalRemainderSharedTailLevel
familyLevel c3AFRecurrence =
  C.c3OneStepAFRecurrenceIdentificationLevel
familyLevel c4DensityAnchoredStress =
  C.c4DensityAnchoredStressLaneLevel
familyLevel cylinderEventBooleanRealization =
  EventAlgebra.literalRound539CylinderEventBooleanAlgebraLevel

------------------------------------------------------------------------
-- Internal subcuts that MUST remain visible.
------------------------------------------------------------------------

-- A3 representation subclaims.
a3PositiveEventSemanticsLevel : ProofLevel
a3PositiveEventSemanticsLevel =
  A3.literalRound535CylinderEventIndicatorSemanticsLevel

a3ProjectiveConsistencyLevel : ProofLevel
a3ProjectiveConsistencyLevel =
  A3.literalRound535ProjectiveEventExpectationConsistencyLevel

a3ContinuityAtEmptyLevel : ProofLevel
a3ContinuityAtEmptyLevel =
  A3.literalRound535ProjectiveContinuityAtEmptyLevel

a3ExpectationIntegralIdentificationLevel : ProofLevel
a3ExpectationIntegralIdentificationLevel =
  A3.literalRound535CylinderExpectationIntegralIdentificationLevel

-- Finite OS: T1 owns Euclidean + Wilson RP, bosonic applicability remains the
-- only independent same-family finite-OS source seam.
finiteOSBosonicAttachmentLevel : ProofLevel
finiteOSBosonicAttachmentLevel =
  FiniteOS.literalRound532BosonicSameFamilyAttachmentLevel

-- WEXT remains two genuine Wilson source statements.
wextTwoMarkExpansionLevel : ProofLevel
wextTwoMarkExpansionLevel =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel

wextConnectingWeightTailLevel : ProofLevel
wextConnectingWeightTailLevel =
  WEXT.literalRound494WilsonConnectingWeightTailLevel

------------------------------------------------------------------------
-- Firewalls: the preferred frontier contains theorem content only.
------------------------------------------------------------------------

preferredSourceFamilyCount : Nat
preferredSourceFamilyCount = 15

opaqueEndpointPredicatesRemaining : Bool
opaqueEndpointPredicatesRemaining = false

constructorChoiceEqualitiesRemaining : Bool
constructorChoiceEqualitiesRemaining = false

wholeMeasureRecordEqualitiesRemaining : Bool
wholeMeasureRecordEqualitiesRemaining = false

independentStructuralAndQuantitativeGroupSelectionsRemaining : Bool
independentStructuralAndQuantitativeGroupSelectionsRemaining = false

su2PromotionRemaining : Bool
su2PromotionRemaining = false

singleCutoffMeasureExtensionRemaining : Bool
singleCutoffMeasureExtensionRemaining = false

allRemainingFamiliesAreAlreadyProved : Bool
allRemainingFamiliesAreAlreadyProved = false

round544IrreducibleSourceFamilyCutCompilerLevel : ProofLevel
round544IrreducibleSourceFamilyCutCompilerLevel = machineChecked
