{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanAbsoluteTwoJSourceMinCutRound299Exact where

------------------------------------------------------------------------
-- ROUND299 / LEAST-PRIVILEGE F1 SOURCE CUT
--
-- Do not charge canonical B for reconstruction of all of CMP116.  The repo
-- already separates three facts:
--
--   (1) finite declared U/J/A derivatives preserve the source localization
--       majorant (published CMP116/Cauchy authority);
--   (2) finite normalized source demands construct one positive common radius;
--   (3) the direct T5 carrier needs only the absolute mixed-J shell inequality.
--
-- Consequently common-radius existence and generic finite differentiation are
-- not independent F1 research leaves.  The surviving physical/source payment is
-- the SAME-OBJECT specialization: the selected gauge-invariant T5 observables
-- are literal CMP116/CMP119 J directions on the active density, and the published
-- differentiated localization theorem is instantiated on those two directions
-- with their actual support/root geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Radius104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as Radius114
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296


data F1SearchObject299 : Set where
  literalSelectedJSameObjectLocalization : F1SearchObject299
  finiteSourceDerivativeLocalizationMechanism : F1SearchObject299
  positiveCommonRadiusExistence : F1SearchObject299
  firstSecondDerivativeRadiusReuse : F1SearchObject299
  sourceCovarianceT5CovarianceIdentity : F1SearchObject299
  signedToMagnitudeRepair : F1SearchObject299

searchRole299 : F1SearchObject299 → Introspective.ProofSearchTargetRole
searchRole299 literalSelectedJSameObjectLocalization =
  Introspective.canonicalConsumerResidual
searchRole299 finiteSourceDerivativeLocalizationMechanism =
  Introspective.compilerConsequence
searchRole299 positiveCommonRadiusExistence =
  Introspective.compilerConsequence
searchRole299 firstSecondDerivativeRadiusReuse =
  Introspective.compilerConsequence
searchRole299 sourceCovarianceT5CovarianceIdentity =
  Introspective.compilerConsequence
searchRole299 signedToMagnitudeRepair =
  Introspective.compilerConsequence

record Round299Boundary : Set where
  constructor round299-boundary
  field
    reconstructWholeCMP116ForTwoJ : Bool
    reconstructWholeCMP116ForTwoJIsFalse : reconstructWholeCMP116ForTwoJ ≡ false

    genericCauchyDerivativeNewYMAnalysis : Bool
    genericCauchyDerivativeNewYMAnalysisIsFalse :
      genericCauchyDerivativeNewYMAnalysis ≡ false

    commonRadiusExistenceIndependentLeaf : Bool
    commonRadiusExistenceIndependentLeafIsFalse :
      commonRadiusExistenceIndependentLeaf ≡ false

    exactSelectedJSourceSpecializationStillRequired : Bool
    exactSelectedJSourceSpecializationStillRequiredIsTrue :
      exactSelectedJSourceSpecializationStillRequired ≡ true

canonicalRound299Boundary : Round299Boundary
canonicalRound299Boundary =
  round299-boundary false refl false refl false refl true refl

round299FiniteDerivativeLocalizationAuthorityLevel : ProofLevel
round299FiniteDerivativeLocalizationAuthorityLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

round299FinitePolydiscCompilerAuthorityLevel : ProofLevel
round299FinitePolydiscCompilerAuthorityLevel =
  Source.finitePolydiscCauchyDerivativePreservesExternalMajorantLevel

round299FiniteDemandsToCommonRadiusCompilerLevel : ProofLevel
round299FiniteDemandsToCommonRadiusCompilerLevel =
  Radius114.cmp116FiniteDemandsToCommonRadiusObjectLevel

round299FirstSecondDerivativeSameRadiusCompilerLevel : ProofLevel
round299FirstSecondDerivativeSameRadiusCompilerLevel =
  Radius114.cmp116FirstSecondDerivativeShareCanonicalRadiusLevel

-- A stronger constructive producer for the common domain remains available:
-- extract the four finite normalized source demands.  The radius itself is then
-- constructed and must not be counted as a second theorem.
round299LiteralFiniteDemandExtractionLevel : ProofLevel
round299LiteralFiniteDemandExtractionLevel =
  Radius104.literalCMP116FiniteNormalizedDemandExtractionLevel

-- Canonical F1 payment after the recut.  This is exactly the absolute two-J
-- source specialization consumed by the direct T5 shell; it is not enlarged to
-- all source coordinates or all observables.
round299LiteralSelectedJSameObjectLocalizationLevel : ProofLevel
round299LiteralSelectedJSameObjectLocalizationLevel =
  R296.round296LiteralAbsoluteTwoJLocalizationLevel

round299DirectB1ShellCompilerLevel : ProofLevel
round299DirectB1ShellCompilerLevel = R296.round296DirectB1ShellCompilerLevel
