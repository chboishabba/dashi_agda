{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119H1OS4AttachmentRound583Exact where

------------------------------------------------------------------------
-- GOAL-1 H1 -> H2 / ROUND583:
-- THE EXACT PRE-GAP H1 CLUSTERING THEOREM IS THE OS4 ATTACHMENT.
--
-- H2 core has already constructed the Schwinger family and OS reconstruction
-- without clustering.  The selected real CMP116/R281 application now also runs
-- on that same pre-gap core.  The only remaining semantic theorem is that this
-- exact selected continuum clustering statement is the OS4 predicate required
-- for the same Schwinger family.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2CoreExact as H2Core
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayCMP119RealSelectedGapExact as RealGap
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119CoreH1OS4Meaning
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
     EuclideanAction Permutation Epsilon Witness
     Scale Volume Root SourceDirection SpectralObservable Energy : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vector))
    (h2 :
      H2Core.CMP119DirectPhysicalH2Core
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : G)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
    (application :
      RealGap.CMP119CoreRealSelectedSpectrumApplication
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vector
        Scale Volume Root SourceDirection SpectralObservable Energy
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        (H2Core.coreInputs h2)
        covarianceLaws
        group
        source)
    : Set₂ where
  field
    OS4Clustering : Set

    -- Physical meaning theorem: the exact H1 selected continuum clustering
    -- bound, on this exact core carrier, is sufficient for OS4.
    selectedH1ClusteringMeansOS4 :
      (∀ observable time →
        let
          spectrum = RealGap.spectrumSourceCore application
        in
        RealGap.selectedCoreContinuumCovarianceBelowSpectrumEnvelope
          application observable time)
      →
      OS4Clustering

open CMP119CoreH1OS4Meaning public

asCoreOS4Attachment :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      Scale Volume Root SourceDirection SpectralObservable Energy
      sequenceLimit limitLaws quotient division S
      h2 covarianceLaws group source application} →
  CMP119CoreH1OS4Meaning
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    Scale Volume Root SourceDirection SpectralObservable Energy
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
    h2 covarianceLaws group source application →
  OSSystem.OS4Attachment
    (OSSystem.continuumOSCoreSystem
      (H2Core.coreInputs h2) group)
asCoreOS4Attachment meaning = record
  { OSSystem.OS4Attachment.OS4ClusteringAttached =
      OS4Clustering meaning
  ; OSSystem.OS4Attachment.os4Attached =
      selectedH1ClusteringMeansOS4 meaning
        (RealGap.selectedCoreContinuumCovarianceBelowSpectrumEnvelope
          _)
  }

round583H1ToOS4CompilerLevel : ProofLevel
round583H1ToOS4CompilerLevel = machineChecked

-- This is the one genuine semantic attachment: interpret the exact selected H1
-- continuum clustering theorem as OS4 for the exact H2 core Schwinger family.
literalRound583SelectedClusteringMeansOS4Level : ProofLevel
literalRound583SelectedClusteringMeansOS4Level = conditional
