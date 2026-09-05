module DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY: TEM / TE / TM MODES BETWEEN PARALLEL PLATES
--
-- SOURCE:
-- H. A. Haus and J. R. Melcher, Electromagnetic Fields and Energy,
-- MIT OpenCourseWare, Chapter 13, especially §13.2.
--
-- The source states that:
-- * fields between perfectly conducting parallel plates are linear
--   combinations of the modes;
-- * the longitudinal dependence is indexed by n*pi/a;
-- * the TE n=0 solution is excluded because it has zero amplitude;
-- * the TM0 solution has both E and H transverse to propagation and is the TEM
--   mode from §13.1.
--
-- This source correction matters to the formal carrier: the exceptional zero
-- mode should be represented as TEM, not as an undifferentiated TE/TM zero
-- sector.
------------------------------------------------------------------------

record ParallelPlateTETMModeExpansionSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String
    exactSectionLocator : String

    perfectlyConductingParallelPlateProblem : Set
    teTmModesDerived : Set
    longitudinalIntegerQuantisationDerived : Set
    fieldsExpandedAsLinearCombinationOfModes : Set

    teZeroExcludedBecauseZeroAmplitude : Set
    tmZeroIdentifiedAsTEM : Set
    positiveIndexHigherModes : Set

    sourceBackedOnly : Set
    reading : String

open ParallelPlateTETMModeExpansionSourceAuthority public

canonicalParallelPlateTETMModeExpansionAuthority :
  ParallelPlateTETMModeExpansionSourceAuthority
canonicalParallelPlateTETMModeExpansionAuthority = record
  { sourceName =
      "Haus and Melcher, Electromagnetic Fields and Energy, Chapter 13 (MIT OpenCourseWare)"
  ; sourceLocator =
      "https://ocw.mit.edu/courses/res-6-001-electromagnetic-fields-and-energy-spring-2008/pages/chapter-13/"
  ; exactSectionLocator =
      "https://ocw.mit.edu/courses/res-6-001-electromagnetic-fields-and-energy-spring-2008/e7b7eabc9d1921d231a012c6d0b94f93_13.pdf ; Section 13.2, equations (19)--(21)"
  ; perfectlyConductingParallelPlateProblem = ⊤
  ; teTmModesDerived = ⊤
  ; longitudinalIntegerQuantisationDerived = ⊤
  ; fieldsExpandedAsLinearCombinationOfModes = ⊤
  ; teZeroExcludedBecauseZeroAmplitude = ⊤
  ; tmZeroIdentifiedAsTEM = ⊤
  ; positiveIndexHigherModes = ⊤
  ; sourceBackedOnly = ⊤
  ; reading =
      "MIT source-backs a TEM zero mode plus positive-index TE/TM higher modes; the exact DASHI finite-energy/Hilbert carrier and quantum-mode identification remain local welds."
  }

data ClassicalParallelPlateExpansionAutomaticallyIsCasimirHilbertCompleteness : Set where

data ExceptionalZeroModeAutomaticallyMeansLegacyTEorTMZero : Set where

classicalExpansionNeedsCasimirCarrierWeld :
  ClassicalParallelPlateExpansionAutomaticallyIsCasimirHilbertCompleteness → ⊥
classicalExpansionNeedsCasimirCarrierWeld ()

zeroModeMustNotBeFlattenedBackToLegacyTETM :
  ExceptionalZeroModeAutomaticallyMeansLegacyTEorTMZero → ⊥
zeroModeMustNotBeFlattenedBackToLegacyTETMZero
  where
    LegacyTETMZero : Set
    LegacyTETMZero = ExceptionalZeroModeAutomaticallyMeansLegacyTEorTMZero
