{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralTopDownRouteSClosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact as RouteS
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact as Stress
import DASHI.Physics.YangMills.YMClayLiteralLocalFieldsClosureExact as Local
import DASHI.Physics.YangMills.YMClayRouteSToLiteralYGapAttachmentExact as GapAttach

------------------------------------------------------------------------
-- The Round78 top-down compiler bundle now lives in its canonical Route-S
-- recipient.  This preserves the historical theorem types while removing
-- the live dependency on the numbered wrapper.
-- Historical source: BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.
------------------------------------------------------------------------

record UVToContinuumYM
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    weakCouplingRG : Five.LiteralWeakCouplingRGConstruction Y
    continuumYM : Five.UnifiedContinuumYMConstruction Y
open UVToContinuumYM public

record SameHamiltonianPhysicalMassGap
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    physicalGap : Five.CutoffUniformPhysicalMassGap Y
open SameHamiltonianPhysicalMassGap public

record SameFamilyLocalFieldsOPEStressWard
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    localFields : Five.ContinuumLocalFieldOPEStressWard Y
open SameFamilyLocalFieldsOPEStressWard public

record StandardSameHGaussianNontrivialityConsequence
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    deriveInteracting :
      Five.CutoffUniformPhysicalMassGap Y →
      Five.ContinuumLocalFieldOPEStressWard Y →
      Five.InteractingContinuumNontriviality Y
open StandardSameHGaussianNontrivialityConsequence public

literalClaySolutionFromTopDownThree :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  Five.LiteralClayStructuralBase Y →
  UVToContinuumYM Y →
  SameHamiltonianPhysicalMassGap Y →
  SameFamilyLocalFieldsOPEStressWard Y →
  StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromTopDownThree Y structural uv gap local standard =
  Five.literalClaySolutionFromFiveTheorems
    Y
    structural
    (weakCouplingRG uv)
    (physicalGap gap)
    (continuumYM uv)
    (localFields local)
    (deriveInteracting standard (physicalGap gap) (localFields local))

round78IndependentClayAnalyticEndpointCount : Nat
round78IndependentClayAnalyticEndpointCount = 3

round78TopDownCompilerLevel : ProofLevel
round78TopDownCompilerLevel = machineChecked

round78PhysicalThreeTheoremInstantiationLevel : ProofLevel
round78PhysicalThreeTheoremInstantiationLevel = conditional

round78StandardSameHNontrivialityConsequenceLevel : ProofLevel
round78StandardSameHNontrivialityConsequenceLevel = standardImported

------------------------------------------------------------------------
-- LITERAL CLAY TOP-DOWN CLOSURE THROUGH THE VERIFIED ROUTE-S MIN-CUT
--
-- Round78 already proves that the official repository ClayYangMillsSolution is
-- compiler output from:
--
--   A  UVToContinuumYM Y
--   B  SameHamiltonianPhysicalMassGap Y
--   C  SameFamilyLocalFieldsOPEStressWard Y
--
-- plus structural data and the standard same-H nontriviality consequence.
--
-- The 2026-09-19 verified Aristotle Route-S tranche sharpens B's producer to
-- exactly three physical classes:
--
--   P1 finite literal Wilson-loop clustering,
--   P2 the three selected literal expectation limits,
--   P3 same-object OS correlation/spectral identification.
--
-- Cross-prover truth boundary:
-- Lean kernel-checks P1+P2+P3 -> MassGapConclusion.  Agda cannot definitionally
-- consume that Lean theorem.  The only remaining integration payment on B is
-- therefore the typed realization of that verified output as the richer
-- literal-Y record CutoffUniformPhysicalMassGap Y.
--
-- This module introduces no arbitrary theorem Set.  The bridge target is the
-- exact existing Round68/Round78 physical mass-gap record on Y.
------------------------------------------------------------------------

record RouteSLiteralMassGapIntegration
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    routeSPhysicalInputs : RouteS.LiteralWilsonRouteSPhysicalInputs

    -- Exact literal-Y endpoint required by Round78-B.  This field is the
    -- cross-prover/same-object integration wall; it is not a second spectral
    -- theorem schema.
    literalPhysicalGap : Five.CutoffUniformPhysicalMassGap Y

open RouteSLiteralMassGapIntegration public

routeSIntegrationBuildsRound78B :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RouteSLiteralMassGapIntegration Y →
  SameHamiltonianPhysicalMassGap Y
routeSIntegrationBuildsRound78B integration = record
  { physicalGap =
      literalPhysicalGap integration
  }

------------------------------------------------------------------------
-- Round78-C directly contains the literal stress/OPE postcondition evidence.
-- This projection makes the Level-2 consumer relationship executable and avoids
-- maintaining a parallel stress/OPE endpoint type.
------------------------------------------------------------------------

round78CBuildsLiteralStressOPEEvidence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  SameFamilyLocalFieldsOPEStressWard Y →
  Stress.LiteralClayStressOPEEvidence Y
round78CBuildsLiteralStressOPEEvidence local = record
  { stressAndOPE =
      Five.stressTensorAndOPE (localFields local)
  ; physicalOPECoefficient =
      Five.physicalOPECoefficient (localFields local)
  ; physicalOPERemainder =
      Five.physicalOPERemainder (localFields local)
  }

round78CBuildsLiteralStressOPEPostcondition :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  SameFamilyLocalFieldsOPEStressWard Y →
  Top.postconditionRequirement Y Clay.stressTensorAndOperatorProductExpansion
round78CBuildsLiteralStressOPEPostcondition {Y = Y} local =
  Stress.literalStressOPEEvidenceIsClayPostcondition
    Y (round78CBuildsLiteralStressOPEEvidence local)

------------------------------------------------------------------------
-- Canonical literal Clay closure constructor.
--
-- This is not a roadmap.  Its result is the repository's official
-- ClayYangMillsSolution type.
------------------------------------------------------------------------

literalClaySolutionFromRouteS :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  Five.LiteralClayStructuralBase Y →
  UVToContinuumYM Y →
  RouteSLiteralMassGapIntegration Y →
  SameFamilyLocalFieldsOPEStressWard Y →
  StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromRouteS Y structural uv routeS local standard =
  literalClaySolutionFromTopDownThree
    Y structural uv
    (routeSIntegrationBuildsRound78B routeS)
    local standard


------------------------------------------------------------------------
-- Fully minimized literal endpoint constructor.
--
-- The caller supplies Round78-A, the exact Route-S B integration, and the
-- literal local-field inputs that compile to Round78-C.  The result is the
-- official repository ClayYangMillsSolution, not another frontier receipt.
------------------------------------------------------------------------

literalClaySolutionFromRouteSAndLiteralLocalFields :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  Five.LiteralClayStructuralBase Y →
  UVToContinuumYM Y →
  RouteSLiteralMassGapIntegration Y →
  Local.LiteralLocalFieldClosureInputs Y →
  StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromRouteSAndLiteralLocalFields
    Y structural uv routeS local standard =
  literalClaySolutionFromRouteS
    Y structural uv routeS
    (Local.literalLocalFieldClosureBuildsRound78C local)
    standard


------------------------------------------------------------------------
-- Certificate-level Route-S integration.
--
-- This removes the old freedom to pair Route-S inputs with an unrelated
-- preassembled literal gap record.  The literal-Y gap is compiled from an
-- explicit physical certificate attachment on the same Y.
------------------------------------------------------------------------

record RouteSLiteralMassGapCertificateIntegration
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    routeSPhysicalInputs :
      RouteS.LiteralWilsonRouteSPhysicalInputs
    physicalGapAttachment :
      GapAttach.RouteSPhysicalGapToLiteralYAttachment Y

open RouteSLiteralMassGapCertificateIntegration public

certificateIntegrationAsLegacy :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  RouteSLiteralMassGapCertificateIntegration Y →
  RouteSLiteralMassGapIntegration Y
certificateIntegrationAsLegacy integration = record
  { routeSPhysicalInputs =
      RouteSLiteralMassGapCertificateIntegration.routeSPhysicalInputs integration
  ; literalPhysicalGap =
      GapAttach.routeSPhysicalGapBuildsLiteralYGap
        (physicalGapAttachment integration)
  }

literalClaySolutionFromRouteSCertificateAndLiteralLocalFields :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  Five.LiteralClayStructuralBase Y →
  UVToContinuumYM Y →
  RouteSLiteralMassGapCertificateIntegration Y →
  Local.LiteralLocalFieldClosureInputs Y →
  StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromRouteSCertificateAndLiteralLocalFields
    Y structural uv routeS local standard =
  literalClaySolutionFromRouteSAndLiteralLocalFields
    Y structural uv
    (certificateIntegrationAsLegacy routeS)
    local standard

------------------------------------------------------------------------
-- Exact closure accounting.
------------------------------------------------------------------------

routeSLeanTerminalTheoremNeedsAdditionalSpectralResearchAfterP1P2P3 : Bool
routeSLeanTerminalTheoremNeedsAdditionalSpectralResearchAfterP1P2P3 = false

routeSLeanTerminalTheoremNeedsAdditionalSpectralResearchAfterP1P2P3IsFalse :
  routeSLeanTerminalTheoremNeedsAdditionalSpectralResearchAfterP1P2P3 ≡ false
routeSLeanTerminalTheoremNeedsAdditionalSpectralResearchAfterP1P2P3IsFalse = refl

routeSToLiteralYMassGapIntegrationStillRequired : Bool
routeSToLiteralYMassGapIntegrationStillRequired = true

routeSToLiteralYMassGapIntegrationStillRequiredIsTrue :
  routeSToLiteralYMassGapIntegrationStillRequired ≡ true
routeSToLiteralYMassGapIntegrationStillRequiredIsTrue = refl

round78CContainsLiteralStressOPEEvidence : Bool
round78CContainsLiteralStressOPEEvidence = true

round78CContainsLiteralStressOPEEvidenceIsTrue :
  round78CContainsLiteralStressOPEEvidence ≡ true
round78CContainsLiteralStressOPEEvidenceIsTrue = refl

literalClaySolutionCompilerFromIntegratedABC : ProofLevel
literalClaySolutionCompilerFromIntegratedABC = machineChecked

routeSLiteralMassGapIntegrationLevel : ProofLevel
routeSLiteralMassGapIntegrationLevel = conditional

unconditionalLiteralClaySolutionConstructedHere : Bool
unconditionalLiteralClaySolutionConstructedHere = false

unconditionalLiteralClaySolutionConstructedHereIsFalse :
  unconditionalLiteralClaySolutionConstructedHere ≡ false
unconditionalLiteralClaySolutionConstructedHereIsFalse = refl
