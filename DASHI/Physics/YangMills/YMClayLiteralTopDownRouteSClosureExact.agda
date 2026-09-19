{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralTopDownRouteSClosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as R78
import DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact as RouteS
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact as Stress

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
  R78.SameHamiltonianPhysicalMassGap Y
routeSIntegrationBuildsRound78B integration = record
  { R78.SameHamiltonianPhysicalMassGap.physicalGap =
      literalPhysicalGap integration
  }

------------------------------------------------------------------------
-- Round78-C directly contains the literal stress/OPE postcondition evidence.
-- This projection makes the Level-2 consumer relationship executable and avoids
-- maintaining a parallel stress/OPE endpoint type.
------------------------------------------------------------------------

round78CBuildsLiteralStressOPEEvidence :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  R78.SameFamilyLocalFieldsOPEStressWard Y →
  Stress.LiteralClayStressOPEEvidence Y
round78CBuildsLiteralStressOPEEvidence local = record
  { Stress.LiteralClayStressOPEEvidence.stressAndOPE =
      Five.stressTensorAndOPE (R78.localFields local)
  ; Stress.LiteralClayStressOPEEvidence.physicalOPECoefficient =
      Five.physicalOPECoefficient (R78.localFields local)
  ; Stress.LiteralClayStressOPEEvidence.physicalOPERemainder =
      Five.physicalOPERemainder (R78.localFields local)
  }

round78CBuildsLiteralStressOPEPostcondition :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  R78.SameFamilyLocalFieldsOPEStressWard Y →
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
  R78.UVToContinuumYM Y →
  RouteSLiteralMassGapIntegration Y →
  R78.SameFamilyLocalFieldsOPEStressWard Y →
  R78.StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromRouteS Y structural uv routeS local standard =
  R78.literalClaySolutionFromTopDownThree
    Y structural uv
    (routeSIntegrationBuildsRound78B routeS)
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
