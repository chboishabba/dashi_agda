{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalR406MixedLogRound420Exact where

------------------------------------------------------------------------
-- ROUND420 / CANONICAL R406 BOUNDARY = LITERAL SELECTED MIXED-J RESPONSE
--
-- R419 removes B-shell as a post-hoc equality by choosing the R406 terminal
-- shell definitionally to be the embedded shared hessian-mark shell.
--
-- The remaining scalar seam is therefore same-object only:
--
--   |R406 selected boundary|
--     = embed( magnitude( literal mixed second log derivative ) ).
--
-- R341 already proves the rational mixed-log magnitude is exactly the finite
-- selected covariance magnitude.  Hence this owner does not add a covariance
-- theorem or a localization theorem; it exposes only the literal source
-- scalarization needed to connect the R406 source replay to the selected
-- physical two-J coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSharedShellR406Round419Exact as R419
import DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Exact as R418
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record CanonicalR406MixedLogAttachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {application : R406.SelectedCMP116TermwiseLocalization base}
    {Scale Volume Root : Set}
    (shell :
      R419.CanonicalSharedShellR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application Scale Volume Root)
    (cutoff : Nat)
    (left right : TestObservable) : Set₁ where
  field
    selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude :
      absℝ
        (R406.selectedBoundaryIntegrand
          (R419.asCanonicalR406 shell))
      ≡
      R418.embedQ (R419.embedding shell)
        (R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative
            (R318.meaning base)
            (Cumulant.sourceDirectionOf (R318.meaning base) left)
            (Cumulant.sourceDirectionOf (R318.meaning base) right)
            cutoff))

open CanonicalR406MixedLogAttachment public

literalMixedLogMagnitudeBelowSharedMarkedGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application
      Scale Volume Root shell cutoff left right} →
  CanonicalR406MixedLogAttachment
    {dataSet = dataSet} {extension = extension} {base = base}
    {application = application} {Scale = Scale} {Volume = Volume} {Root = Root}
    shell cutoff left right →
  R418.embedQ (R419.embedding shell)
    (R278.magnitude extension
      (Cumulant.literalMixedSecondLogDerivative
        (R318.meaning base)
        (Cumulant.sourceDirectionOf (R318.meaning base) left)
        (Cumulant.sourceDirectionOf (R318.meaning base) right)
        cutoff))
  ≤ℝ
  R418.embedQ (R419.embedding shell)
    (Geometric.markedBaseEnergy (R419.shared shell) Shared.hessianMark)
  *ℝ
  R418.embedQ (R419.embedding shell)
    (Geo.halfPower (R419.selectedDistance shell))
literalMixedLogMagnitudeBelowSharedMarkedGeometricHalf
    {shell = shell} attachment =
  subst
    (λ lower →
      lower ≤ℝ
      R418.embedQ (R419.embedding shell)
        (Geometric.markedBaseEnergy (R419.shared shell) Shared.hessianMark)
      *ℝ
      R418.embedQ (R419.embedding shell)
        (Geo.halfPower (R419.selectedDistance shell)))
    (selectedBoundaryMagnitudeIsLiteralMixedLogMagnitude attachment)
    (R419.canonicalR406BoundaryBelowSharedMarkedGeometricHalf shell)

finiteSelectedCovarianceMagnitudeBelowSharedMarkedGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application
      Scale Volume Root shell cutoff left right} →
  CanonicalR406MixedLogAttachment
    {dataSet = dataSet} {extension = extension} {base = base}
    {application = application} {Scale = Scale} {Volume = Volume} {Root = Root}
    shell cutoff left right →
  R418.embedQ (R419.embedding shell)
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      left right)
  ≤ℝ
  R418.embedQ (R419.embedding shell)
    (Geometric.markedBaseEnergy (R419.shared shell) Shared.hessianMark)
  *ℝ
  R418.embedQ (R419.embedding shell)
    (Geo.halfPower (R419.selectedDistance shell))
finiteSelectedCovarianceMagnitudeBelowSharedMarkedGeometricHalf
    {dataSet = dataSet} {extension = extension} {base = base}
    {shell = shell} {cutoff = cutoff}
    {left = left} {right = right} attachment =
  let
    mixedBound =
      literalMixedLogMagnitudeBelowSharedMarkedGeometricHalf attachment

    mixedEqualsCovariance =
      R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right

    embeddedEquality :
      R418.embedQ (R419.embedding shell)
        (R278.magnitude extension
          (Cumulant.literalMixedSecondLogDerivative
            (R318.meaning base)
            (Cumulant.sourceDirectionOf (R318.meaning base) left)
            (Cumulant.sourceDirectionOf (R318.meaning base) right)
            cutoff))
      ≡
      R418.embedQ (R419.embedding shell)
        (R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff) left right)
    embeddedEquality =
      cong (R418.embedQ (R419.embedding shell)) mixedEqualsCovariance
  in
  subst
    (λ lower →
      lower ≤ℝ
      R418.embedQ (R419.embedding shell)
        (Geometric.markedBaseEnergy (R419.shared shell) Shared.hessianMark)
      *ℝ
      R418.embedQ (R419.embedding shell)
        (Geo.halfPower (R419.selectedDistance shell)))
    embeddedEquality
    mixedBound

round420R406MixedLogCompilerLevel : ProofLevel
round420R406MixedLogCompilerLevel = machineChecked

-- This is the remaining same-object scalar weld on the shortest R406 lane.
round420SelectedBoundaryMixedLogIdentificationLevel : ProofLevel
round420SelectedBoundaryMixedLogIdentificationLevel = conditional

-- R341 owns the mixed-log -> finite covariance identity.
round420AdditionalCovarianceTheoremRequired : Bool
round420AdditionalCovarianceTheoremRequired = false
