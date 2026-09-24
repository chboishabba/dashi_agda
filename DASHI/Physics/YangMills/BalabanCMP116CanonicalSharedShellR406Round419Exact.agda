{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSharedShellR406Round419Exact where

------------------------------------------------------------------------
-- ROUND419 / CANONICALIZE R406 ON THE SHARED MARKED HESSIAN SHELL
--
-- R406 deliberately leaves its terminal selectedConnectingShell abstract.
-- R418 showed that a post-hoc equality
--
--   selectedConnectingShell = embed(shared hessian shell)
--
-- is enough for the shortest Clay consumer, but carrying an arbitrary shell
-- and later proving equality is stronger than necessary.
--
-- This owner removes that degree of freedom at construction time:
--
--   * reuse every literal R406 source/term/operator/sum coordinate;
--   * discard only its old arbitrary terminal shell;
--   * choose the terminal shell definitionally to be the embedded shared
--     hessian-mark shell at the selected scale/volume/root/distance;
--   * require only the actual source summability statement into that concrete
--     shell.
--
-- Hence B-shell is not a separate equality theorem on this canonical route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP116R406SharedMarkedGeometricRound418Exact as R418

record CanonicalSharedShellR406Inputs
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    (Scale Volume Root : Set) : Set₂ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    embedding : R208.RationalRealRingEmbedding

    selectedScale : Scale
    selectedVolume : Volume
    selectedRoot : Root
    selectedDistance : Nat

    -- This is the only new quantitative/source-facing payment here.  It is
    -- exactly the outer R406 common-Y summability theorem with the consumer
    -- shell chosen to be the already-controlled shared hessian shell.
    commonYShellsBelowSharedMarkedShell :
      Resum.sumℝ
        (R406.commonYShell application)
        (R406.localizedDomains application)
      ≤ℝ
      R418.embedQ embedding
        (Shared.markedAnalyticShell shared Shared.hessianMark
          selectedScale selectedVolume selectedRoot selectedDistance)

open CanonicalSharedShellR406Inputs public

asCanonicalR406 :
  ∀ {Measure TestObservable dataSet extension base application Scale Volume Root} →
  CanonicalSharedShellR406Inputs
    {dataSet = dataSet} {extension = extension} {base = base}
    application Scale Volume Root →
  R406.SelectedCMP116TermwiseLocalization base
asCanonicalR406 {application = application} inputs = record
  { R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensity =
      R406.selectedT5RGDensity application
  ; R406.SelectedCMP116TermwiseLocalization.selectedT5RGDensityIsBase =
      R406.selectedT5RGDensityIsBase application
  ; R406.SelectedCMP116TermwiseLocalization.leftObservable =
      R406.leftObservable application
  ; R406.SelectedCMP116TermwiseLocalization.rightObservable =
      R406.rightObservable application
  ; R406.SelectedCMP116TermwiseLocalization.leftJ =
      R406.leftJ application
  ; R406.SelectedCMP116TermwiseLocalization.rightJ =
      R406.rightJ application
  ; R406.SelectedCMP116TermwiseLocalization.leftJIsObservableIndexed =
      R406.leftJIsObservableIndexed application
  ; R406.SelectedCMP116TermwiseLocalization.rightJIsObservableIndexed =
      R406.rightJIsObservableIndexed application
  ; R406.SelectedCMP116TermwiseLocalization.DecouplingBoundaryAssignment =
      R406.DecouplingBoundaryAssignment application
  ; R406.SelectedCMP116TermwiseLocalization.selectedDecouplingBoundary =
      R406.selectedDecouplingBoundary application
  ; R406.SelectedCMP116TermwiseLocalization.Term =
      R406.Term application
  ; R406.SelectedCMP116TermwiseLocalization.Domain =
      R406.Domain application
  ; R406.SelectedCMP116TermwiseLocalization.Factor =
      R406.Factor application
  ; R406.SelectedCMP116TermwiseLocalization.Operator =
      R406.Operator application
  ; R406.SelectedCMP116TermwiseLocalization.localizedDomains =
      R406.localizedDomains application
  ; R406.SelectedCMP116TermwiseLocalization.termsWithCommonY =
      R406.termsWithCommonY application
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTerm =
      R406.differentiatedTerm application
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorant =
      R406.differentiatedTermMajorant application
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIntegrand =
      R406.commonYBoundaryIntegrand application
  ; R406.SelectedCMP116TermwiseLocalization.commonYShell =
      R406.commonYShell application
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIntegrand =
      R406.selectedBoundaryIntegrand application
  ; R406.SelectedCMP116TermwiseLocalization.selectedConnectingShell =
      R418.embedQ (embedding inputs)
        (Shared.markedAnalyticShell (shared inputs) Shared.hessianMark
          (selectedScale inputs)
          (selectedVolume inputs)
          (selectedRoot inputs)
          (selectedDistance inputs))
  ; R406.SelectedCMP116TermwiseLocalization.operatorAlgebra =
      R406.operatorAlgebra application
  ; R406.SelectedCMP116TermwiseLocalization.operatorOrderToReal =
      R406.operatorOrderToReal application
  ; R406.SelectedCMP116TermwiseLocalization.termFactors =
      R406.termFactors application
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperator =
      R406.beforeOperator application
  ; R406.SelectedCMP116TermwiseLocalization.afterOperator =
      R406.afterOperator application
  ; R406.SelectedCMP116TermwiseLocalization.ordinaryFactorMajorant =
      R406.ordinaryFactorMajorant application
  ; R406.SelectedCMP116TermwiseLocalization.markedFactorMajorant =
      R406.markedFactorMajorant application
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermAbsoluteIsOperatorDifferenceNorm =
      R406.differentiatedTermAbsoluteIsOperatorDifferenceNorm application
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedTermMajorantIsOperatorMarkedProduct =
      R406.differentiatedTermMajorantIsOperatorMarkedProduct application
  ; R406.SelectedCMP116TermwiseLocalization.beforeOperatorBelowOrdinary =
      R406.beforeOperatorBelowOrdinary application
  ; R406.SelectedCMP116TermwiseLocalization.afterOperatorBelowOrdinary =
      R406.afterOperatorBelowOrdinary application
  ; R406.SelectedCMP116TermwiseLocalization.markedOperatorDifferenceBelow =
      R406.markedOperatorDifferenceBelow application
  ; R406.SelectedCMP116TermwiseLocalization.selectedBoundaryIsCommonYSum =
      R406.selectedBoundaryIsCommonYSum application
  ; R406.SelectedCMP116TermwiseLocalization.commonYBoundaryIsTermSum =
      R406.commonYBoundaryIsTermSum application
  ; R406.SelectedCMP116TermwiseLocalization.differentiatedMajorantsBelowCommonYShell =
      R406.differentiatedMajorantsBelowCommonYShell application
  ; R406.SelectedCMP116TermwiseLocalization.commonYShellsBelowSelectedConnectingShell =
      commonYShellsBelowSharedMarkedShell inputs
  }

canonicalR406Attachment :
  ∀ {Measure TestObservable dataSet extension base application Scale Volume Root}
    (inputs :
      CanonicalSharedShellR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application Scale Volume Root) →
  R418.R406SharedMarkedGeometricAttachment
    (asCanonicalR406 inputs) Scale Volume Root
canonicalR406Attachment inputs = record
  { R418.R406SharedMarkedGeometricAttachment.shared =
      shared inputs
  ; R418.R406SharedMarkedGeometricAttachment.embedding =
      embedding inputs
  ; R418.R406SharedMarkedGeometricAttachment.selectedScale =
      selectedScale inputs
  ; R418.R406SharedMarkedGeometricAttachment.selectedVolume =
      selectedVolume inputs
  ; R418.R406SharedMarkedGeometricAttachment.selectedRoot =
      selectedRoot inputs
  ; R418.R406SharedMarkedGeometricAttachment.selectedDistance =
      selectedDistance inputs
  ; R418.R406SharedMarkedGeometricAttachment.selectedConnectingShellIsSharedMarkedShell =
      refl
  }

canonicalR406BoundaryBelowSharedMarkedGeometricHalf :
  ∀ {Measure TestObservable dataSet extension base application Scale Volume Root}
    (inputs :
      CanonicalSharedShellR406Inputs
        {dataSet = dataSet} {extension = extension} {base = base}
        application Scale Volume Root) →
  absℝ
    (R406.selectedBoundaryIntegrand (asCanonicalR406 inputs))
  ≤ℝ
  R418.embedQ (embedding inputs)
    (Geometric.markedBaseEnergy
      (shared inputs) Shared.hessianMark)
  *ℝ
  R418.embedQ (embedding inputs)
    (Geo.halfPower
      (selectedDistance inputs))
canonicalR406BoundaryBelowSharedMarkedGeometricHalf inputs =
  R418.selectedBoundaryBelowSharedMarkedGeometricHalf
    (canonicalR406Attachment inputs)

round419CanonicalSharedShellR406CompilerLevel : ProofLevel
round419CanonicalSharedShellR406CompilerLevel = machineChecked

-- The post-hoc B-shell equality has disappeared on this constructor.
round419PostHocBShellEqualityRequired : Bool
round419PostHocBShellEqualityRequired = false
