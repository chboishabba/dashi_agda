module DASHI.Moonshine.P11JacquetLanglandsSectionIndependenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hervé Jacquet and Robert P. Langlands,
-- "Automorphic Forms on GL(2), Part 1", LNM 114, Springer, 1970.
-- DOI: 10.1007/BFb0058988.
--
-- Kimball Martin,
-- "The basis problem revisited", Transactions of the AMS 373 (2020),
-- 4523--4559. DOI: 10.1090/tran/8077.
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- Journal of the Ramanujan Mathematical Society 17 (2002), 115--147.
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinate the generic section-independent-consumer criterion with the
-- exact p=11 Jacquet--Langlands coordinate non-canonicity witness.
--
-- Two admissible local coordinate alignments (+ and -) preserve all currently
-- declared invariant data: the same representation, common plane, complete
-- Satake residual and kernel generator.  Nevertheless their transported U2
-- operators differ.
--
-- Therefore the downstream consumer which asks for the reopened bad-prime
-- operator value is NOT section independent.  Alignment provenance cannot be
-- erased for that consumer.  In contrast, the Satake-residual consumer is
-- explicitly independent across the two admissible alignments.
--
-- This sharpens the distinction
--
--   invariant completeness != canonical reconstruction
--
-- to the action-facing statement
--
--   safe provenance erasure <=> downstream section independence.
--
-- It does not reopen the already-closed representation-level JL theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.SectionIndependentConsumerExact as Section
import DASHI.Moonshine.P11JacquetLanglandsCoordinateNonCanonicityExact as JL
import DASHI.Moonshine.P11Level44TransverseSatakeNonUniquenessExact as Satake
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal

------------------------------------------------------------------------
-- Restrict to the two exact admissible alignments already constructed.
------------------------------------------------------------------------

data TwoAlignment : Set where
  plus minus : TwoAlignment

alignment : TwoAlignment → JL.LocalCoordinateAlignment
alignment plus = JL.plusAlignment
alignment minus = JL.minusAlignment

p11AlignmentReopeningFamily : Section.ReopeningFamily
p11AlignmentReopeningFamily = record
  { Coarse = Principal.Old3
  ; Fine = Principal.Old3
  ; Section = TwoAlignment
  ; reopen = λ choice v → JL.transportedU2 (alignment choice) v
  }

------------------------------------------------------------------------
-- The identity downstream consumer exposes the noncanonical reopened U2 value.
------------------------------------------------------------------------

identityConsumer : Principal.Old3 → Principal.Old3
identityConsumer v = v

transverseBasisOutputsDistinct :
  JL.transportedU2 JL.plusAlignment Principal.oldBasis2
  ≡ JL.transportedU2 JL.minusAlignment Principal.oldBasis2 → ⊥
transverseBasisOutputsDistinct equality
  with trans
    (sym Satake.plusOnTransverseBasis)
    (trans equality Satake.minusOnTransverseBasis)
... | ()

transportedU2SectionDependenceWitness :
  Section.SectionDependenceWitness
    p11AlignmentReopeningFamily identityConsumer
transportedU2SectionDependenceWitness = record
  { leftSection = plus
  ; rightSection = minus
  ; coarsePoint = Principal.oldBasis2
  ; outputsDistinct = transverseBasisOutputsDistinct
  }

transportedU2ConsumerCannotBeSectionIndependent :
  Section.DownstreamSectionIndependent
    p11AlignmentReopeningFamily identityConsumer → ⊥
transportedU2ConsumerCannotBeSectionIndependent independent =
  JL.transportedOperatorsDistinct
    (λ v → independent plus minus v)

transportedU2DependenceDetectedByGenericCriterion :
  Section.DownstreamSectionIndependent
    p11AlignmentReopeningFamily identityConsumer → ⊥
transportedU2DependenceDetectedByGenericCriterion =
  Section.sectionDependenceRefutesIndependence
    p11AlignmentReopeningFamily
    identityConsumer
    transportedU2SectionDependenceWitness

------------------------------------------------------------------------
-- A coarser invariant consumer CAN be section independent.  The Satake
-- quadratic residual is exactly the same for the two transported operators.
------------------------------------------------------------------------

satakeResidualByAlignment :
  TwoAlignment → Principal.Old3 → Principal.Old3
satakeResidualByAlignment plus = Satake.plusSatakeQuadratic
satakeResidualByAlignment minus = Satake.minusSatakeQuadratic

satakeResidualSectionIndependent :
  (left right : TwoAlignment) →
  (v : Principal.Old3) →
  satakeResidualByAlignment left v ≡ satakeResidualByAlignment right v
satakeResidualSectionIndependent plus plus v = refl
satakeResidualSectionIndependent minus minus v = refl
satakeResidualSectionIndependent plus minus v = Satake.satakeResidualsIdentical v
satakeResidualSectionIndependent minus plus v =
  sym (Satake.satakeResidualsIdentical v)

------------------------------------------------------------------------
-- Exact safety boundary for future consumers.
------------------------------------------------------------------------

record P11JacquetLanglandsSectionIndependenceBoundary : Set where
  field
    invariantResidualSectionIndependent : Bool
    badPrimeOperatorSectionIndependent : Bool
    alignmentProvenanceRequiredForBadPrimeConsumer : Bool
    representationLevelJLReopened : Bool

canonicalP11JacquetLanglandsSectionIndependenceBoundary :
  P11JacquetLanglandsSectionIndependenceBoundary
canonicalP11JacquetLanglandsSectionIndependenceBoundary = record
  { invariantResidualSectionIndependent = true
  ; badPrimeOperatorSectionIndependent = false
  ; alignmentProvenanceRequiredForBadPrimeConsumer = true
  ; representationLevelJLReopened = false
  }
