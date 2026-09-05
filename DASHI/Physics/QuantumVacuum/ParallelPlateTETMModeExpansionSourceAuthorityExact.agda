module DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY: TE/TM MODE EXPANSION BETWEEN PARALLEL PLATES
--
-- SOURCE:
-- H. A. Haus and J. R. Melcher, Electromagnetic Fields and Energy,
-- MIT OpenCourseWare, Chapter 13, especially §§13.2--13.3.
-- The text derives TE/TM modes between perfectly conducting parallel plates,
-- identifies the longitudinal n*pi/a structure, discusses the exceptional
-- zero sector, and states that fields between the plates are linear
-- combinations of the modes.
--
-- This is SOURCEBACKED mode-expansion authority only.  It is not automatically
-- the same Hilbert/finite-energy carrier, transverse continuum normalization,
-- quantum mode space, or zero-sector convention used by the Casimir consumer.
------------------------------------------------------------------------

record ParallelPlateTETMModeExpansionSourceAuthority : Set where
  field
    sourceName : String
    sourceLocator : String

    perfectlyConductingParallelPlateProblem : Set
    teTmModesDerived : Set
    longitudinalIntegerQuantisationDerived : Set
    fieldsExpandedAsLinearCombinationOfModes : Set
    exceptionalZeroSectorDiscussed : Set

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
  ; perfectlyConductingParallelPlateProblem = ⊤
  ; teTmModesDerived = ⊤
  ; longitudinalIntegerQuantisationDerived = ⊤
  ; fieldsExpandedAsLinearCombinationOfModes = ⊤
  ; exceptionalZeroSectorDiscussed = ⊤
  ; sourceBackedOnly = ⊤
  ; reading =
      "MIT source-backs classical TE/TM mode expansion for perfectly conducting parallel plates; the exact DASHI finite-energy/Hilbert carrier and quantum-mode identification remain local welds."
  }

data ClassicalParallelPlateExpansionAutomaticallyIsCasimirHilbertCompleteness : Set where

classicalExpansionNeedsCasimirCarrierWeld :
  ClassicalParallelPlateExpansionAutomaticallyIsCasimirHilbertCompleteness → ⊥
classicalExpansionNeedsCasimirCarrierWeld ()
