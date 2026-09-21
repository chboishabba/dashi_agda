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
-- The current finite RG/source cut is therefore A1 + A2 + BC1 only.
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
-- BC1: literal differentiated carrier / full physical A=A(B) chain rule.
------------------------------------------------------------------------

bc1LiteralSourceAndDemandInputsLevel : ProofLevel
bc1LiteralSourceAndDemandInputsLevel =
  R121.bc1LiteralSourceAndDemandInputsLevel

bc1LiteralPhysicalCompositeComponentLevel : ProofLevel
bc1LiteralPhysicalCompositeComponentLevel =
  R121.bc1LiteralPhysicalCompositeComponentLevel

bc1CanonicalCarrierCompilerLevel : ProofLevel
bc1CanonicalCarrierCompilerLevel =
  R121.bc1CanonicalCarrierCompilerLevel

bc1PhysicalCompositeChainRuleCompilerLevel : ProofLevel
bc1PhysicalCompositeChainRuleCompilerLevel =
  R121.bc1PhysicalCompositeChainRuleLevel

------------------------------------------------------------------------
-- Goal-1 pruning.
------------------------------------------------------------------------

bc2HeatDoobRequiredForDirectCMP116Goal1MassGap : Bool
bc2HeatDoobRequiredForDirectCMP116Goal1MassGap = false

heatLangevinClusteringRouteMandatory : Bool
heatLangevinClusteringRouteMandatory = false

round472PresentCutCompilerLevel : ProofLevel
round472PresentCutCompilerLevel = machineChecked

-- The remaining physical source wall is exactly A1/A2/BC1 above.  No BC2
-- finite-heat-semigroup or gradient-covariance inhabitant is needed by the
-- preferred Goal-1 mass-gap route.
literalRound472PresentCutInstantiationLevel : ProofLevel
literalRound472PresentCutInstantiationLevel = conditional
