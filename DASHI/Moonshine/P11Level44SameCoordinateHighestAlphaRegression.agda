module DASHI.Moonshine.P11Level44SameCoordinateHighestAlphaRegression where

------------------------------------------------------------------------
-- Focused regression for the p=11 level-44 same-coordinate weld.
--
-- This root consumes theorem surfaces, not only boundary receipts:
--
--   one Old3 coordinate module
--     -> analytic d=1,2,4 oldspace realization
--     -> marked v1,v2,v4 realization
--
-- and the whole analytic oldspace inherits every good-prime eigencharacter of
-- the level-11 source.
--
-- The later local-coordinate work adds a second, action-facing boundary:
-- representation-level JL may be closed while coordinate reopening remains
-- noncanonical.  A downstream consumer can forget alignment provenance exactly
-- when it is section independent; the actual transported U2 consumer fails
-- that test while the shared Satake residual passes it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.SectionIndependentConsumerExact as Section
import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Deg
import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as Eig
import DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact as Perm
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact as Cutset
import DASHI.Moonshine.P11Level44FormalSameCoordinateComparisonExact as Same
import DASHI.Moonshine.P11JacquetLanglandsSectionIndependenceExact as JLSection

formalComparisonRegression :
  (D : Same.Level44DegeneracyTriple) →
  Cutset.Level44OldspaceSameObjectComparison
formalComparisonRegression = Same.formalSameCoordinateComparison

analyticBasis1Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis1 n ≡ Same.copy1Series D n
analyticBasis1Regression = Same.analyticBasis1

analyticBasis2Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis2 n ≡ Same.copy2Series D n
analyticBasis2Regression = Same.analyticBasis2

analyticBasis4Regression :
  (D : Same.Level44DegeneracyTriple) → (n : Nat) →
  Same.analyticRealize D Marked.oldBasis4 n ≡ Same.copy4Series D n
analyticBasis4Regression = Same.analyticBasis4

wholeOldspaceGoodPrimeRegression :
  {D : Same.Level44DegeneracyTriple} {ell : Nat} →
  (H : Same.Level44GoodPrimeEigenData D ell) →
  (v : Marked.Old3) → (n : Nat) →
  Same.analyticHeckeRealize H v n
  ≡ Eig.scaleSeries (Same.eigenvalue H) (Same.analyticRealize D v) n
wholeOldspaceGoodPrimeRegression = Same.wholeOldspaceGoodPrimeEigen

markedDeckRRegression :
  (v : Marked.Old3) →
  Marked.realizeOld3 (Marked.oldR v)
  ≡ Perm.deckR5 (Marked.realizeOld3 v)
markedDeckRRegression = Marked.realizeDeckR

markedDeckSRegression :
  (v : Marked.Old3) →
  Marked.realizeOld3 (Marked.oldS v)
  ≡ Perm.deckS5 (Marked.realizeOld3 v)
markedDeckSRegression = Marked.realizeDeckS

actualAutomorphicComparisonStillOpen :
  Same.actualEichlerJacquetLanglandsComparisonConstructed
    Same.canonicalP11Level44FormalSameCoordinateBoundary ≡ false
actualAutomorphicComparisonStillOpen = refl

------------------------------------------------------------------------
-- New action-facing provenance regression.
------------------------------------------------------------------------

badPrimeConsumerSectionDependenceRegression :
  Section.DownstreamSectionIndependent
    JLSection.p11AlignmentReopeningFamily
    JLSection.identityConsumer → ⊥
badPrimeConsumerSectionDependenceRegression =
  JLSection.transportedU2ConsumerCannotBeSectionIndependent

satakeResidualSectionIndependenceRegression :
  (left right : JLSection.TwoAlignment) →
  (v : Marked.Old3) →
  JLSection.satakeResidualByAlignment left v
  ≡ JLSection.satakeResidualByAlignment right v
satakeResidualSectionIndependenceRegression =
  JLSection.satakeResidualSectionIndependent

reopenableNotCanonicalRegression :
  Section.reopenableImpliesCanonicalReopening
    Section.canonicalSectionIndependentConsumerBoundary ≡ false
reopenableNotCanonicalRegression = refl

sectionDependenceRequiresProvenanceRegression :
  Section.sectionDependenceRequiresProvenanceRetention
    Section.canonicalSectionIndependentConsumerBoundary ≡ true
sectionDependenceRequiresProvenanceRegression = refl
