module DASHI.Moonshine.P11JacquetLanglandsSectionIndependenceRegression where

------------------------------------------------------------------------
-- Focused regression for the action-facing consequence of p=11 coordinate
-- non-canonicity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.SectionIndependentConsumerExact as Section
import DASHI.Moonshine.P11JacquetLanglandsSectionIndependenceExact as JLSection
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal

badPrimeConsumerNeedsAlignmentProvenanceRegression :
  Section.DownstreamSectionIndependent
    JLSection.p11AlignmentReopeningFamily
    JLSection.identityConsumer → ⊥
badPrimeConsumerNeedsAlignmentProvenanceRegression =
  JLSection.transportedU2ConsumerCannotBeSectionIndependent

concreteDependenceWitnessRegression :
  Section.SectionDependenceWitness
    JLSection.p11AlignmentReopeningFamily
    JLSection.identityConsumer
concreteDependenceWitnessRegression =
  JLSection.transportedU2SectionDependenceWitness

satakeResidualIndependentRegression :
  (left right : JLSection.TwoAlignment) →
  (v : Principal.Old3) →
  JLSection.satakeResidualByAlignment left v
  ≡ JLSection.satakeResidualByAlignment right v
satakeResidualIndependentRegression =
  JLSection.satakeResidualSectionIndependent

reopenableDoesNotMeanCanonicalRegression :
  Section.reopenableImpliesCanonicalReopening
    Section.canonicalSectionIndependentConsumerBoundary ≡ false
reopenableDoesNotMeanCanonicalRegression = refl

factorizedConsumerIndependentRegression :
  Section.factorizedConsumerIsSectionIndependent
    Section.canonicalSectionIndependentConsumerBoundary ≡ true
factorizedConsumerIndependentRegression = refl

coveredIndependenceFactorsThroughRegression :
  Section.coveredSectionIndependentConsumerFactorsThroughQuotient
    Section.canonicalSectionIndependentConsumerBoundary ≡ true
coveredIndependenceFactorsThroughRegression = refl

worldAuthorityNotPromotedRegression :
  Section.quotientFactorizationConfersWorldAuthority
    Section.canonicalSectionIndependentConsumerBoundary ≡ false
worldAuthorityNotPromotedRegression = refl
