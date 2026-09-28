{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstNormalizedJetExact where

------------------------------------------------------------------------
-- H1 SOURCE-FIRST NORMALIZED-JET FRONTIER
--
-- R576 already shows that a normalized Wilson marked-log jet expansion plus
-- pointwise localization and one rooted-shell sum is enough for WEXT.
--
-- The remaining provenance issue is that an arbitrary jet family could be an
-- independently selected surrogate.  This owner pins every jet to the ACTUAL
-- source-first KP cluster functional.
--
-- For a cluster term Phi_Y(s,t), its bidegree-(1,1) germ j_Y is certified by
--
--   Phi_Y(s,t)
--     = eval(j_Y,s,t)
--       + s^2 R_L(Y,s,t)
--       + t^2 R_R(Y,s,t)
--
-- on the declared literal source polydisc.  Thus all omitted terms have degree
-- >=2 in at least one source variable; in particular no hidden st coefficient
-- can be moved into the remainder.
--
-- The cluster list is definitionally the source-first KP common enumeration.
-- The only remaining total-response same-object theorem is then that the sum
-- of these ACTUAL cluster germs is the normalized finite-moment log jet.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonAffineSourceBoundExact as Radius
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalKoteckyPreissExact as PhysicalKP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstKPDataExact as SourceFirst
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterJetExact as Jet
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
open import DASHI.Physics.YangMills.CompactLieProofLevel

literalKPClusterTerm :
  ∀ {Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    (family :
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily
        Observable ℚ Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    cutoff left right cluster →
  ℚ → ℚ → ℚ
literalKPClusterTerm family cutoff left right cluster sourceLeft sourceRight =
  KP.clusterFunctional
    (SourceFirst.literalTerminalKPData
      (PhysicalKP.sourceAt family
        cutoff left right sourceLeft sourceRight)
      (PhysicalKP.meaningAt family
        cutoff left right sourceLeft sourceRight))
    cluster

record LiteralKPClusterBidegree11Germ
    {Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    (family :
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily
        Observable ℚ Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    (cutoff : Nat)
    (left right : Observable)
    (cluster : Cluster)
    (jet : Jet.TwoSourceJet)
    : Set₁ where
  field
    leftQuadraticRemainder rightQuadraticRemainder : ℚ → ℚ → ℚ

    literalClusterGermFactorization :
      ∀ sourceLeft sourceRight →
      Radius.SourceInsideRadius sourceLeft →
      Radius.SourceInsideRadius sourceRight →
      literalKPClusterTerm family cutoff left right cluster
        sourceLeft sourceRight
      ≡
      Jet.evaluateJet jet sourceLeft sourceRight
      +
      (sourceLeft * sourceLeft)
        * leftQuadraticRemainder sourceLeft sourceRight
      +
      (sourceRight * sourceRight)
        * rightQuadraticRemainder sourceLeft sourceRight

open LiteralKPClusterBidegree11Germ public

record SourceFirstNormalizedWilsonJetExpansion
    {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    (family :
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily
        Observable ℚ Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    (cutoff : Nat)
    (left right : Observable)
    : Set₂ where
  field
    clusterJet : Cluster → Jet.TwoSourceJet

    clusterJetIsLiteralKPGerm :
      ∀ cluster →
      LiteralKPClusterBidegree11Germ
        family cutoff left right cluster (clusterJet cluster)

    supportLocality :
      Jet.JetSupportLocality clusterJet

    -- This is the remaining TOTAL same-generating-functional theorem.
    -- Both sides are now fixed objects: the left is the exact finite T5
    -- normalized-moment log jet, and the right is the sum of jets already
    -- proved above to be germs of the actual source-first KP cluster terms.
    normalizedPhysicalLogJetIsLiteralKPClusterJetSum :
      Jet.normalizedMomentLogJet
        (R573.r278MomentAlgebra
          (R575.rationalAbsoluteCovarianceExtension laws)
          (Gram.measureSequence dataSet cutoff))
        left right
      ≡
      Jet.sumJets
        (Jet.mapJets clusterJet
          (PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.commonClusters
            family cutoff left right))

open SourceFirstNormalizedWilsonJetExpansion public

asNormalizedWilsonMarkedLogJetExpansion :
  ∀ {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      PhysicalIncompatible family dataSet laws cutoff left right} →
  SourceFirstNormalizedWilsonJetExpansion
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {ShellVolume = ShellVolume}
    {Root = Root}
    {Polymer = Polymer}
    {Link = Link}
    {Cluster = Cluster}
    {FiniteVolume = FiniteVolume}
    {PhysicalIncompatible = PhysicalIncompatible}
    family dataSet laws cutoff left right →
  Jet.NormalizedWilsonMarkedLogJetExpansion
    {Cluster = Cluster}
    (R573.r278MomentAlgebra
      (R575.rationalAbsoluteCovarianceExtension laws)
      (Gram.measureSequence dataSet cutoff))
    left right
asNormalizedWilsonMarkedLogJetExpansion
    {family = family} source = record
  { Jet.NormalizedWilsonMarkedLogJetExpansion.clusters =
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.commonClusters
        family _ _ _
  ; Jet.NormalizedWilsonMarkedLogJetExpansion.clusterJet =
      clusterJet source
  ; Jet.NormalizedWilsonMarkedLogJetExpansion.normalizedLogJetExpansion =
      normalizedPhysicalLogJetIsLiteralKPClusterJetSum source
  ; Jet.NormalizedWilsonMarkedLogJetExpansion.supportLocality =
      supportLocality source
  }

sourceFirstNormalizedJetClusterCarrierIsKPEnumeration :
  ∀ {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      PhysicalIncompatible family dataSet laws cutoff left right}
    (source :
      SourceFirstNormalizedWilsonJetExpansion
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {ShellVolume = ShellVolume}
        {Root = Root}
        {Polymer = Polymer}
        {Link = Link}
        {Cluster = Cluster}
        {FiniteVolume = FiniteVolume}
        {PhysicalIncompatible = PhysicalIncompatible}
        family dataSet laws cutoff left right) →
  Jet.clusters (asNormalizedWilsonMarkedLogJetExpansion source)
  ≡
  PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.commonClusters
    family cutoff left right
sourceFirstNormalizedJetClusterCarrierIsKPEnumeration source = refl

sourceFirstClusterJetGermIdentificationLevel : ProofLevel
sourceFirstClusterJetGermIdentificationLevel = conditional

sourceFirstNormalizedPhysicalLogJetIdentificationLevel : ProofLevel
sourceFirstNormalizedPhysicalLogJetIdentificationLevel = conditional

sourceFirstNormalizedJetAdapterLevel : ProofLevel
sourceFirstNormalizedJetAdapterLevel = machineChecked
