{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectR295ToR296MagnitudeCompilerRound313Exact where

------------------------------------------------------------------------
-- ROUND313 / R295 -> R296 DIRECT MAGNITUDE COMPILER
--
-- R295's exact T5 source presentation already stores the only physical/source
-- localization payment needed downstream:
--
--   magnitude (D^2_J log Z) <= rooted connecting shell.
--
-- R296 additionally asks that the selected magnitude realization is ordinary
-- rational absolute value and then stores the same localization theorem again
-- with `|.|` written explicitly.  Once the magnitude interpretation is fixed,
-- that second field is compiler output by equality transport.
--
-- Therefore R309's published-source/applicability decomposition remains a valid
-- OPTIONAL producer for constructing the R295 payment, but it is not an extra
-- mandatory B-facing layer after an exact R295 presentation is available.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

absoluteLocalizationFromR295Magnitude :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension) →
  (magnitudeIsAbsolute : ∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
  ∀ cutoff left right →
  ∣ Cumulant.literalMixedSecondLogDerivative
      (R295.meaning presentation)
      (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
      (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
      cutoff ∣
  ≤ Shell.rootedShell (R295.shellData presentation)
      (R295.scaleOf presentation cutoff)
      (R295.volumeOf presentation cutoff)
      (R295.connectingRoot presentation cutoff left right)
      (R295.physicalDistance presentation left right)
absoluteLocalizationFromR295Magnitude {extension = extension}
    presentation magnitudeIsAbsolute cutoff left right =
  let
    value =
      Cumulant.literalMixedSecondLogDerivative
        (R295.meaning presentation)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) left)
        (Cumulant.sourceDirectionOf (R295.meaning presentation) right)
        cutoff
  in
  subst
    (λ lower → lower ≤ Shell.rootedShell (R295.shellData presentation)
      (R295.scaleOf presentation cutoff)
      (R295.volumeOf presentation cutoff)
      (R295.connectingRoot presentation cutoff left right)
      (R295.physicalDistance presentation left right))
    (magnitudeIsAbsolute value)
    (R295.differentiatedSourceMagnitudeBoundOnSelectedDirections
      presentation cutoff left right)

exactT5JMagnitudeFromR295 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet} →
  (presentation : R295.DirectT5StateFamilyJPresentation dataSet extension) →
  (magnitudeIsAbsolute : ∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
  R296.ExactT5JMagnitudePresentation dataSet extension
exactT5JMagnitudeFromR295 presentation magnitudeIsAbsolute = record
  { R296.ExactT5JMagnitudePresentation.source = presentation
  ; R296.ExactT5JMagnitudePresentation.t5MagnitudeIsRationalAbsolute =
      magnitudeIsAbsolute
  ; R296.ExactT5JMagnitudePresentation.literalTwoJMagnitudeBelowConnectingShell =
      absoluteLocalizationFromR295Magnitude presentation magnitudeIsAbsolute
  }

------------------------------------------------------------------------
-- Boundary / proof-search correction.
------------------------------------------------------------------------

r296AbsoluteLocalizationIndependentAfterR295MagnitudeBound : Bool
r296AbsoluteLocalizationIndependentAfterR295MagnitudeBound = false

r309ApplicabilityMandatoryAfterExactR295Presentation : Bool
r309ApplicabilityMandatoryAfterExactR295Presentation = false

r295SelectedTwoJMagnitudeLocalizationStillPhysical : Bool
r295SelectedTwoJMagnitudeLocalizationStillPhysical = true

round313R295ToR296CompilerLevel : ProofLevel
round313R295ToR296CompilerLevel = machineChecked

round313SelectedTwoJMagnitudeLocalizationLevel : ProofLevel
round313SelectedTwoJMagnitudeLocalizationLevel =
  R295.round295LiteralT5JDirectionLocalizationLevel

r296AbsoluteLocalizationIndependentAfterR295MagnitudeBoundIsFalse :
  r296AbsoluteLocalizationIndependentAfterR295MagnitudeBound ≡ false
r296AbsoluteLocalizationIndependentAfterR295MagnitudeBoundIsFalse = refl

r309ApplicabilityMandatoryAfterExactR295PresentationIsFalse :
  r309ApplicabilityMandatoryAfterExactR295Presentation ≡ false
r309ApplicabilityMandatoryAfterExactR295PresentationIsFalse = refl

r295SelectedTwoJMagnitudeLocalizationStillPhysicalIsTrue :
  r295SelectedTwoJMagnitudeLocalizationStillPhysical ≡ true
r295SelectedTwoJMagnitudeLocalizationStillPhysicalIsTrue = refl
