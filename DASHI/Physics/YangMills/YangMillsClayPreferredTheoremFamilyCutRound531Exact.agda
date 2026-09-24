{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredTheoremFamilyCutRound531Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND531: PREFERRED THEOREM-FAMILY MAX-CUT
--
-- R528 intentionally keeps 28 logical/source obligations visible.  They are
-- not 28 independent research projects.  This file groups them by the smallest
-- proof-bearing source object that can discharge them without laundering any
-- subclaim.
--
-- Preferred theorem/source families:
--
--   F1  A1 current-step variation package                  (7 subclaims)
--   F2  A2 beta-history/source-coordinate attachment       (1)
--   F3  A3 cylinder representation package                (4)
--   F4  published finite OS applicability package          (3)
--   F5  quantitative T5/CMP119 same-family attachment      (1)
--   F6  Wilson WEXT package                                (2)
--   F7  same-H energy/decay coordinate                     (1)
--   F8  arbitrary-G quantitative source map                (1)
--   F9  all-G actual compact-simple structural bundle      (1)
--   F10 literal CMP119/CMP122 Section-2 T1 source bundle   (1)
--   F11 beta-density -> normalized finite-measure map      (1)
--   F12 Wilson local-observable realization                (C0)
--   F13 marked-curvature family                            (C1)
--   F14 physical OPE remainder shared tail                 (C2)
--   F15 one-step AF/OPE recurrence identification          (C3)
--   F16 density-anchored canonical stress lane             (C4)
--
-- This is a scheduling quotient ONLY.  The underlying subclaims remain live
-- and explicit in R528/R496.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayGoal1A1SourceCutRound473Exact as A1
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as A2
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as A3
import DASHI.Physics.YangMills.YangMillsClayPublishedFiniteOSSourceRound462Exact as FiniteOS
import DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact as Quantitative
import DASHI.Physics.YangMills.BalabanWilsonWEXTMaxCutRound494Exact as WEXT
import DASHI.Physics.YangMills.BalabanClayCanonicalBMaxCutRound493Exact as B
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G1
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as T1
import DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact as Density
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFromStructuralRound530Exact as C0
import DASHI.Physics.YangMills.YangMillsClayCPhysicalPackageMaxCutRound527Exact as C

data TheoremFamily : Set where
  a1CurrentStepVariationPackage : TheoremFamily
  a2HistoryCoordinateAttachment : TheoremFamily
  a3CylinderRepresentationPackage : TheoremFamily
  finiteOSApplicabilityPackage : TheoremFamily
  quantitativeSameFamilyAttachment : TheoremFamily
  wilsonWEXTPackage : TheoremFamily
  sameHamiltonianEnergyDecayCoordinate : TheoremFamily
  arbitraryGroupQuantitativeSourceMap : TheoremFamily
  allGroupCompactSimpleStructuralBundle : TheoremFamily
  literalSection2T1SourceBundle : TheoremFamily
  densityToNormalizedFiniteMeasureMap : TheoremFamily
  c0WilsonLocalObservableRealization : TheoremFamily
  c1MarkedCurvatureFamily : TheoremFamily
  c2PhysicalRemainderSharedTail : TheoremFamily
  c3OneStepAFRecurrenceIdentification : TheoremFamily
  c4DensityAnchoredStressLane : TheoremFamily

familyLevel : TheoremFamily → ProofLevel
familyLevel a1CurrentStepVariationPackage =
  A1.literalRound473A1SourceInstantiationLevel
familyLevel a2HistoryCoordinateAttachment =
  A2.literalCMP116BetaMarkIsGeneratedHistoryShellLevel
familyLevel a3CylinderRepresentationPackage =
  conditional
familyLevel finiteOSApplicabilityPackage =
  FiniteOS.literalRound462PublishedFiniteOSApplicationLevel
familyLevel quantitativeSameFamilyAttachment =
  Quantitative.literalRound514SameFiniteExpectationAttachmentLevel
familyLevel wilsonWEXTPackage =
  conditional
familyLevel sameHamiltonianEnergyDecayCoordinate =
  B.bSameHamiltonianLevel
familyLevel arbitraryGroupQuantitativeSourceMap =
  G1.physicalGroupParametricFiveBlockSourceMapLevel
familyLevel allGroupCompactSimpleStructuralBundle =
  Structural.literalRound517AllGroupCompactSimpleSourceLevel
familyLevel literalSection2T1SourceBundle =
  T1.literalRound516ConcreteT1SourceBundleLevel
familyLevel densityToNormalizedFiniteMeasureMap =
  Density.literalRound525DensityToFiniteMeasureMapLevel
familyLevel c0WilsonLocalObservableRealization =
  C0.literalRound530StructuralWilsonLocalDataLevel
familyLevel c1MarkedCurvatureFamily =
  C.c1MarkedCurvatureFamilyLevel
familyLevel c2PhysicalRemainderSharedTail =
  C.c2PhysicalRemainderSharedTailLevel
familyLevel c3OneStepAFRecurrenceIdentification =
  C.c3OneStepAFRecurrenceIdentificationLevel
familyLevel c4DensityAnchoredStressLane =
  C.c4DensityAnchoredStressLaneLevel

------------------------------------------------------------------------
-- A3 and WEXT keep their internal honest subcuts visible.
------------------------------------------------------------------------

a3EventIndicatorLevel : ProofLevel
a3EventIndicatorLevel =
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

wextTwoMarkExpansionLevel : ProofLevel
wextTwoMarkExpansionLevel =
  WEXT.literalRound494WilsonTwoMarkExpansionLevel

wextConnectingWeightTailLevel : ProofLevel
wextConnectingWeightTailLevel =
  WEXT.literalRound494WilsonConnectingWeightTailLevel

------------------------------------------------------------------------
-- The family count is a project scheduler count, not an atomic theorem count.
------------------------------------------------------------------------

preferredTheoremFamilyCount : Nat
preferredTheoremFamilyCount = 16

allLogicalSubclaimsRemainVisible : Bool
allLogicalSubclaimsRemainVisible = true

familyGroupingDischargesSubclaimsByItself : Bool
familyGroupingDischargesSubclaimsByItself = false

opaqueEndpointPredicatesInPreferredRoute : Bool
opaqueEndpointPredicatesInPreferredRoute = false

constructorChoiceEqualitiesInPreferredRoute : Bool
constructorChoiceEqualitiesInPreferredRoute = false

round531PreferredTheoremFamilyCutCompilerLevel : ProofLevel
round531PreferredTheoremFamilyCutCompilerLevel = machineChecked
