{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DomainSpecificSharedHessianRound449Exact where

------------------------------------------------------------------------
-- B / ROUND449: DOMAIN-SPECIFIC FIXED-Y CMP116 SHELL -> SHARED HESSIAN DECAY.
--
-- This is the preferred replacement for R441's global-tree-depth convenience
-- route.  CMP116 (1.29) uses the varying d_k(Y), represented here literally by
--
--   Source.sourceTreeDistance (R444.source data) domain.
--
-- Once the literal fixed-Y R429 shell is dominated by the existing shared
-- physical Hessian shell at THAT SAME depth, geometric half-decay is already
-- compiler-owned.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record DomainSpecificSharedHessianIdentification
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (Scale Volume Root : Set)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    shared :
      Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    scaleOf : R444.Domain data → Scale
    volumeOf : R444.Domain data → Volume
    rootOf : R444.Domain data → Root

    -- Genuine B3 physical/source payment.  No depth equality is requested:
    -- both sides use the source-native d_k(Y) directly.
    commonYShellBelowEmbeddedHessianShell :
      ∀ domain →
      R444.commonYShell data domain
      ≤ℝ
      Embed.embed embedding
        (Shared.hessianInfluenceShell shared
          (scaleOf domain)
          (volumeOf domain)
          (rootOf domain)
          (Source.sourceTreeDistance (R444.source data) domain))

open DomainSpecificSharedHessianIdentification public

fixedYGeometricHalfReal :
  ∀ {Measure TestObservable dataSet extension base data}
    {Scale Volume Root}
    {embedding : Embed.OrderedRationalRealEmbedding}
    (identification :
      DomainSpecificSharedHessianIdentification
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data Scale Volume Root embedding)
    domain →
  R444.commonYShell data domain
  ≤ℝ
  Embed.embed embedding
    (Geom.markedBaseEnergy
      (shared identification) Shared.hessianMark
      * Geo.halfPower
          (Source.sourceTreeDistance (R444.source data) domain))
fixedYGeometricHalfReal {data = data} {embedding = embedding} identification domain =
  ≤ℝ-trans
    (commonYShellBelowEmbeddedHessianShell identification domain)
    (Embed.orderPreserving embedding
      (Geom.hessianInfluenceGeometricHalf
        (shared identification)
        (scaleOf identification domain)
        (volumeOf identification domain)
        (rootOf identification domain)
        (Source.sourceTreeDistance (R444.source data) domain)))

round449SharedHessianGeometricCompilerLevel : ProofLevel
round449SharedHessianGeometricCompilerLevel =
  Geom.sharedHessianGeometricShellLevel

round449DomainSpecificTransportLevel : ProofLevel
round449DomainSpecificTransportLevel = machineChecked

-- B3 is now exactly the literal domination of commonYShell(Y) by the existing
-- physical/shared CMP116 Hessian shell at the SAME source d_k(Y).
literalRound449FixedYSharedHessianDominationLevel : ProofLevel
literalRound449FixedYSharedHessianDominationLevel = conditional
