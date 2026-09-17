{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayF1CanonicalSourceApplicationExact where

------------------------------------------------------------------------
-- F1 / canonical CMP116 selected-source application compiler
--
-- ATTRIBUTION / AUTHORITY
--
-- External source authority remains Tadeusz Bałaban, CMP 116 (1988),
-- DOI 10.1007/BF01239022, as recorded by
-- `BalabanCMP116DifferentiatedLocalizationSourceExact`.
--
-- R338 is the DASHI reconstruction of the published differentiated-localization
-- statement on the canonical common CMP116 source domain.  R339 is the DASHI
-- selected-T5 same-object/application ABI: source response magnitude is the
-- selected literal mixed-log magnitude, and the source envelope is bounded by
-- the selected rooted shell.  This file contributes only the DASHI compiler
-- composition of those existing owners into the exact R295 carrier.
--
-- In particular:
--
--   external CMP116 theorem
--   != R338 formal source ABI
--   != R339 physical same-object/calibration payment
--   != this compiler theorem.
--
-- No citation is coerced into an Agda proof and no fresh Yang--Mills decay
-- estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedT5ApplicationRound339Exact as R339

------------------------------------------------------------------------
-- The actual compiler.
--
-- R339 already compiles the canonical source theorem + selected-T5 application
-- into R320's one-field direct selected-shell payment.  R320 already compiles
-- that payment into R295.  Compose those two machine-owned maps directly.
------------------------------------------------------------------------

canonicalSourceApplicationLocalizesBaseAsR295 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands} →
  R339.CanonicalSelectedT5CMP116Application base demands source →
  R295.DirectT5StateFamilyJPresentation dataSet extension
canonicalSourceApplicationLocalizesBaseAsR295 base application =
  R320.localizeBaseDirectlyAsR295 base
    (R339.canonicalApplicationBuildsR320Payment application)

------------------------------------------------------------------------
-- Validation / proof-search surface.
------------------------------------------------------------------------

data F1CanonicalSourceApplicationCompilerPresent : Set where
  f1CanonicalSourceApplicationCompilerPresent :
    F1CanonicalSourceApplicationCompilerPresent

sourceTheoremManufacturedByCompiler : Bool
sourceTheoremManufacturedByCompiler = false

sourceTheoremManufacturedByCompilerIsFalse :
  sourceTheoremManufacturedByCompiler ≡ false
sourceTheoremManufacturedByCompilerIsFalse = refl

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

freshYMDecayEstimateIntroducedIsFalse :
  freshYMDecayEstimateIntroduced ≡ false
freshYMDecayEstimateIntroducedIsFalse = refl

canonicalR338R339CutCompilesToR295 : Bool
canonicalR338R339CutCompilesToR295 = true

canonicalR338R339CutCompilesToR295IsTrue :
  canonicalR338R339CutCompilesToR295 ≡ true
canonicalR338R339CutCompilesToR295IsTrue = refl

-- R318 remains a valid GENERAL adapter for an externally presented theorem
-- whose magnitude/root/distance coordinates differ from the selected T5 ones.
-- It is not, however, the least-privilege proof-search cut once the canonical
-- R338/R339 source/application normalization is available.
r318ExternalPresentationPairIsPrimitiveCut : Bool
r318ExternalPresentationPairIsPrimitiveCut = false

r318ExternalPresentationPairIsPrimitiveCutIsFalse :
  r318ExternalPresentationPairIsPrimitiveCut ≡ false
r318ExternalPresentationPairIsPrimitiveCutIsFalse = refl

f1ExternalSourceAuthorityLevel : ProofLevel
f1ExternalSourceAuthorityLevel =
  Source.cmp116DifferentiatedLocalizationAuthorityLevel

f1CanonicalSourceAlignmentLevel : ProofLevel
f1CanonicalSourceAlignmentLevel =
  R338.round338LocalCanonicalSourceAlignmentLevel

f1SelectedT5ApplicationLevel : ProofLevel
f1SelectedT5ApplicationLevel =
  R339.round339SourceMagnitudeSameObjectLevel

f1EnvelopeCalibrationLevel : ProofLevel
f1EnvelopeCalibrationLevel =
  R339.round339SourceEnvelopeCalibrationLevel

f1CanonicalCompilerLevel : ProofLevel
f1CanonicalCompilerLevel = machineChecked
