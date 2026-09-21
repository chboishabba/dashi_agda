{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayGoal1PresentCutRound472Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND472: PRESENT FINITE-RG CUT AFTER DIRECT CMP116 MASS GAP.
--
-- Historical Round121 exposed four source rows:
--
--   A1  CMP109 Eq.(5.1) mixed jet / current-step beta
--   A2  generated-history response
--   BC1 literal CMP109/CMP116 differentiated carrier + physical chain rule
--   BC2 same-density Heat/Doob Hessian/covariance
--
-- BC2 was a producer for the old heat/Langevin clustering route.  Goal-1 now
-- uses the direct selected CMP116 localization -> R454 -> R455 route, so BC2 is
-- not a prerequisite of the submission mass-gap theorem.
--
-- The current preferred finite RG/source cut is therefore A1 + A2 only.
-- BC1 is retained below only as an audit/fallback for historical Hessian/Heat
-- routes; no preferred Goal-1 consumer observes it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayPresentCutRound121Exact as R121
import DASHI.Physics.YangMills.BalabanA2BetaMarkSourceCoordinateRound250Exact as R250

------------------------------------------------------------------------
-- A1: literal current-step source / one-loop beta.
------------------------------------------------------------------------

a1LiteralWQRSourceLevel : ProofLevel
a1LiteralWQRSourceLevel = R121.a1LiteralWQRSourceLevel

a1LiteralPhysicalJetSplitLevel : ProofLevel
a1LiteralPhysicalJetSplitLevel = R121.a1LiteralPhysicalJetSplitLevel

a1Equation542CompilerLevel : ProofLevel
a1Equation542CompilerLevel = R121.a1Equation542CompilerLevel

------------------------------------------------------------------------
-- A2: generated-history response.
--
-- Preferred source-facing endpoint is shell-level same-object identification
-- (R250).  The explicit Ward-response producer remains a fallback.
------------------------------------------------------------------------

a2LiteralBetaMarkShellIdentificationLevel : ProofLevel
a2LiteralBetaMarkShellIdentificationLevel =
  R250.literalCMP116BetaMarkIsGeneratedHistoryShellLevel

a2ShellToPartialSumCompilerLevel : ProofLevel
a2ShellToPartialSumCompilerLevel =
  R250.a2ShellIdentityToPartialSumCompilerLevel

a2LiteralResponseProducerFallbackLevel : ProofLevel
a2LiteralResponseProducerFallbackLevel =
  R121.a2LiteralResponseProducerLevel

a2LiteralBetaDifferenceSplitFallbackLevel : ProofLevel
a2LiteralBetaDifferenceSplitFallbackLevel =
  R121.a2LiteralBetaDifferenceSplitLevel

a2FullPrefixSubunitCompilerLevel : ProofLevel
a2FullPrefixSubunitCompilerLevel =
  R121.a2FullPrefixSubunitCompilerLevel

------------------------------------------------------------------------
-- Historical BC1 audit/fallback only.
------------------------------------------------------------------------

bc1LiteralSourceAndDemandFallbackLevel : ProofLevel
bc1LiteralSourceAndDemandFallbackLevel =
  R121.bc1LiteralSourceAndDemandInputsLevel

bc1PhysicalCompositeComponentFallbackLevel : ProofLevel
bc1PhysicalCompositeComponentFallbackLevel =
  R121.bc1LiteralPhysicalCompositeComponentLevel

------------------------------------------------------------------------
-- Goal-1 pruning.
------------------------------------------------------------------------

bc1DifferentiatedHessianCarrierRequiredByPreferredGoal1 : Bool
bc1DifferentiatedHessianCarrierRequiredByPreferredGoal1 = false

bc2HeatDoobRequiredForDirectCMP116Goal1MassGap : Bool
bc2HeatDoobRequiredForDirectCMP116Goal1MassGap = false

heatLangevinClusteringRouteMandatory : Bool
heatLangevinClusteringRouteMandatory = false

round472PresentCutCompilerLevel : ProofLevel
round472PresentCutCompilerLevel = machineChecked

-- The remaining preferred finite-RG source wall is exactly A1/A2 above.
-- Neither the historical BC1 differentiated-Hessian carrier nor BC2 finite
-- Heat/Doob covariance is consumed by the direct Goal-1 B/C routes.
literalRound472PresentCutInstantiationLevel : ProofLevel
literalRound472PresentCutInstantiationLevel = conditional
