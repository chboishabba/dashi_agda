{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact where

------------------------------------------------------------------------
-- ROUND342 / ISOLATE THE CURRENT T78-B SAME-OBJECT RESPONSE PAYMENT
--
-- R341 reduced the preferred source-native T78-B route to two physical/source
-- coordinates plus standard one-sided order closure:
--
--   B1. CMP116 differentiated J-response magnitude
--       = selected literal mixed-log magnitude;
--   B2. CMP116 source envelope <= selected spectral clustering envelope.
--
-- This owner isolates B1 from B2.  The DIRECT CMP116 J-response equality is the
-- preferred B1 payment.  It is exactly the same coordinate already exposed by
-- R339/R341 and does not require a CMP109 polarization detour.
--
-- ARCHAEOLOGY CORRECTION (2026-09-15): R322 explicitly records that CMP109's
-- vacuum-polarization tensor is NOT definitionally the selected two-J connected
-- cumulant, and identifies CMP116's declared analytic J directions as the
-- correct source family for this selected-T5 route.  Hence the older R321
-- E^(2)/Pi same-object result may be reused only as an OPTIONAL stronger donor:
-- if one independently proves that R338's CMP116 J-response magnitude equals
-- R321's CMP109 E^(2)/Pi source magnitude, then R321 compiles to B1.  That extra
-- source-source identity is not part of the preferred Pareto cut.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322
import DASHI.Physics.YangMills.BalabanCMP109SelectedT5SameObjectRound321Exact as R321
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonDomainSourceRound338Exact as R338
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341

------------------------------------------------------------------------
-- Preferred B1: direct same-object CMP116 J-response payment.
------------------------------------------------------------------------

record SourceResponseSameObjectPayment
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests)
    : Set₁ where
  field
    sourceMagnitudeIsSelectedMixedLogMagnitude :
      ∀ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      R338.differentiatedMagnitude source
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        leftJ rightJ
      ≡
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)

open SourceResponseSameObjectPayment public

------------------------------------------------------------------------
-- Optional donor: CMP109 E^(2)/Pi route.
--
-- This is deliberately NOT the preferred source family.  It proves only that,
-- after an additional CMP109<->CMP116 source-magnitude identity is supplied,
-- R321's already-owned selected-response weld can inhabit the preferred B1.
------------------------------------------------------------------------

record CMP109CMP116SourceResponseIdentity
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (cmp109Source : R321.PublishedCMP109SelectedShellPayment base)
    : Set₁ where
  field
    canonicalCMP116MagnitudeIsCMP109E2PiMagnitude :
      ∀ cutoff left right →
      R338.differentiatedMagnitude source
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)
      ≡
      R321.sourceE2PiMagnitude cmp109Source cutoff left right

open CMP109CMP116SourceResponseIdentity public

r321SameObjectBuildsB1AfterSourceIdentity :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests}
    {cmp109Source : R321.PublishedCMP109SelectedShellPayment base} →
  CMP109CMP116SourceResponseIdentity base demands source cmp109Source →
  R321.SelectedT5CMP109SameObject base cmp109Source →
  SourceResponseSameObjectPayment base demands source tests spectrumSource
r321SameObjectBuildsB1AfterSourceIdentity
    {extension = extension} {base = base} {tests = tests}
    {spectrumSource = spectrumSource} {cmp109Source = cmp109Source}
    sourceIdentity oldWeld = record
  { sourceMagnitudeIsSelectedMixedLogMagnitude = λ cutoff observable time →
      let
        index = R281.indexFor spectrumSource observable time
        left = R278.left tests index
        right = R278.right tests index
        sourceToOld =
          canonicalCMP116MagnitudeIsCMP109E2PiMagnitude
            sourceIdentity cutoff left right
        oldToSelected =
          sym (R321.selectedMixedDerivativeMagnitudeIsSourceE2Pi
            oldWeld cutoff left right)
        literalToSelected =
          cong
            (λ response → R278.magnitude extension (response cutoff))
            (Cumulant.logSecondDirectionAgrees (R318.meaning base) left right)
      in
      trans sourceToOld (trans oldToSelected (sym literalToSelected))
  }

r321SameObjectCanFeedB1AfterSourceIdentity : Bool
r321SameObjectCanFeedB1AfterSourceIdentity = true

r321CMP109DonorIsPreferredB1Route : Bool
r321CMP109DonorIsPreferredB1Route = false

directCMP116JResponseIsPreferredB1Route : Bool
directCMP116JResponseIsPreferredB1Route = true

cmp109PiIdentificationRequiredByPreferredB1 : Bool
cmp109PiIdentificationRequiredByPreferredB1 = false

cmp109PiIsDefinitionallyTwoJConnectedCumulant : Bool
cmp109PiIsDefinitionallyTwoJConnectedCumulant =
  R322.cmp109PolarizationTensorIsDefinitionallyTwoJConnectedCumulant

------------------------------------------------------------------------
-- Keep B2 independent.
------------------------------------------------------------------------

SourceEnvelopeCalibration :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (source : R338.CanonicalCommonDomainCMP116Source base demands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests) →
  Set
SourceEnvelopeCalibration base demands source tests spectrumSource =
  ∀ cutoff observable time →
  let
    index = R281.indexFor spectrumSource observable time
    left = R278.left tests index
    right = R278.right tests index
    leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
    rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
  in
  R338.sourceEnvelope source
    (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
    (R338.sourceRoot source
      (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
      leftJ rightJ)
    (R338.sourceDistance source leftJ rightJ)
  ≤
  R281.clusteringEnvelope spectrumSource observable time

SelectedLimitUpperClosure :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ} →
  Set
SelectedLimitUpperClosure {dataSet = dataSet} =
  (sequence : Nat → ℚ) (target upper : ℚ) →
  Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
  (∀ cutoff → sequence cutoff ≤ upper) →
  target ≤ upper

------------------------------------------------------------------------
-- Compiler back into the existing R341 application.
------------------------------------------------------------------------

asRound341Application :
  ∀ {Measure TestObservable SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {source : R338.CanonicalCommonDomainCMP116Source base demands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData dataSet extension tests} →
  SourceResponseSameObjectPayment base demands source tests spectrumSource →
  SourceEnvelopeCalibration base demands source tests spectrumSource →
  SelectedLimitUpperClosure {dataSet = dataSet} →
  R341.CanonicalCMP116R281ModeSelectedApplication
    base demands source tests spectrumSource
asRound341Application b1 b2 limitClosure = record
  { R341.CanonicalCMP116R281ModeSelectedApplication.sourceMagnitudeIsSelectedMixedLogMagnitude =
      sourceMagnitudeIsSelectedMixedLogMagnitude b1
  ; R341.CanonicalCMP116R281ModeSelectedApplication.sourceEnvelopeBelowSpectrumEnvelope =
      b2
  ; R341.CanonicalCMP116R281ModeSelectedApplication.rationalUpperClosedUnderSelectedLimit =
      limitClosure
  }

round342CompilerLevel : ProofLevel
round342CompilerLevel = machineChecked

-- Preferred physical B1: direct CMP116 J-response magnitude = selected literal
-- mixed-log magnitude on the exact R318/R281 selected pair.
round342SourceResponseSameObjectLevel : ProofLevel
round342SourceResponseSameObjectLevel = conditional

-- Optional stronger donor route only.  The preferred B1 does not require this
-- CMP109/CMP116 source-source identity.
round342CMP109CMP116SourceIdentityLevel : ProofLevel
round342CMP109CMP116SourceIdentityLevel = conditional

-- B2 remains an independent quantitative calibration payment.
round342EnvelopeCalibrationLevel : ProofLevel
round342EnvelopeCalibrationLevel = conditional

-- Generic ordered-limit closure remains source-independent standard analysis.
round342SelectedLimitUpperClosureLevel : ProofLevel
round342SelectedLimitUpperClosureLevel =
  R341.round341OneSidedOrderClosureLevel

freshYMDecayEstimateIntroduced : Bool
freshYMDecayEstimateIntroduced = false

clayPromotion : Bool
clayPromotion = false
