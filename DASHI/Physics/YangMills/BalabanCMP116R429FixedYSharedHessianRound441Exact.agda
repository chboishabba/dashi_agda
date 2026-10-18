{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429FixedYSharedHessianRound441Exact where

------------------------------------------------------------------------
-- B / ROUND441: LITERAL R429 FIXED-Y SHELL REUSES THE EXISTING CMP116
-- SHARED-HESSIAN GEOMETRIC ESTIMATE.
--
-- The repository already proves, for the physical CMP116 hessian mark,
--
--   hessianInfluenceShell(s,v,r,d)
--     <= markedBaseEnergy(hessianMark) * (1/2)^d.
--
-- Therefore B3 does not need a second geometric-decay proof.  On the Goal-1
-- path the remaining physical/source theorem is the literal per-domain
-- domination of R429.commonYShell by that hessian shell at the selected
-- scale/volume/root.  Equality is neither needed nor asserted.  Ordered
-- rational-to-real transport then gives the real R429 fixed-Y estimate directly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph

import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record R429FixedYSharedHessianIdentification
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (Scale Volume Root : Set)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    shared :
      Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    scaleOf : R429.Domain fourStage → Scale
    volumeOf : R429.Domain fourStage → Volume
    rootOf : R429.Domain fourStage → Root

    -- The genuine B3 source/physics seam:
    -- each literal R429 fixed-Y majorant is dominated by the physical
    -- two-source CMP116 hessian shell at its own source coordinates.
    commonYShellBelowEmbeddedHessianShell :
      ∀ domain →
      R429.commonYShell fourStage domain
      ≤ℝ
      Embed.embed embedding
        (Shared.hessianInfluenceShell shared
          (scaleOf domain)
          (volumeOf domain)
          (rootOf domain)
          Graph.ymTreeEdgeCount)

open R429FixedYSharedHessianIdentification public

r429FixedYGeometricHalfReal :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    {Scale Volume Root}
    {embedding : Embed.OrderedRationalRealEmbedding}
    (identification :
      R429FixedYSharedHessianIdentification
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage Scale Volume Root embedding)
    domain →
  R429.commonYShell fourStage domain
  ≤ℝ
  Embed.embed embedding
    (Geom.markedBaseEnergy
      (shared identification) Shared.hessianMark
      * Geo.halfPower Graph.ymTreeEdgeCount)
r429FixedYGeometricHalfReal identification domain =
  ≤ℝ-trans
    (commonYShellBelowEmbeddedHessianShell identification domain)
    (Embed.orderPreserving embedding
      (Geom.hessianInfluenceGeometricHalf
        (shared identification)
        (scaleOf identification domain)
        (volumeOf identification domain)
        (rootOf identification domain)
        Graph.ymTreeEdgeCount))

round441SharedHessianGeometricDecayReuseLevel : ProofLevel
round441SharedHessianGeometricDecayReuseLevel =
  Geom.sharedHessianGeometricShellLevel

round441RationalToRealOrderTransportLevel : ProofLevel
round441RationalToRealOrderTransportLevel = machineChecked

-- B3 has therefore been reduced to one literal source theorem:
-- each R429.commonYShell(Y) is below the physical/shared CMP116 hessian shell
-- at the corresponding source coordinates.  The geometric fixed-Y decay after
-- that domination is compiler-owned.
literalRound441R429CommonYShellDominationLevel : ProofLevel
literalRound441R429CommonYShellDominationLevel = conditional
