{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- QUANTUM BIRTHMARK SOURCE / CLAIM BOUNDARY
--
-- Primary source:
-- Anton M. Graf, Saul Atwood, Mingxuan Xiao, Roland Ketzmerick,
-- Eric J. Heller, Joonas Keski-Rahkonen,
-- "Quantum Birthmarks: Ergodicity Breaking Beyond Scarring",
-- Physical Review X 16, 031063 (2026), DOI 10.1103/dhzb-28rb.
--
-- Secondary exposition:
-- Phys.org, 11 October 2026, "Quantum 'birthmarks' hold lasting traces of
-- a system's past".
--
-- The source boundary deliberately separates theorem-facing claims from the
-- stadium-billiard numerical illustration and from speculative technology or
-- broad thermodynamic interpretations.
------------------------------------------------------------------------

record BirthmarkSourceReceipt : Set where
  field
    title : String
    journal : String
    citation : String
    doi : String
    publicationDate : String
    primaryPeerReviewed : Bool
    openAccess : Bool

primaryBirthmarkSource : BirthmarkSourceReceipt
primaryBirthmarkSource = record
  { title = "Quantum Birthmarks: Ergodicity Breaking Beyond Scarring"
  ; journal = "Physical Review X"
  ; citation = "Phys. Rev. X 16, 031063 (2026)"
  ; doi = "10.1103/dhzb-28rb"
  ; publicationDate = "2026-09-10"
  ; primaryPeerReviewed = true
  ; openAccess = true
  }

------------------------------------------------------------------------
-- Source-calibrated universal factors.
--
-- PRX Eq. (23) gives the large-Hilbert-space universal enhancement as 2
-- without time-reversal symmetry, 3 with time-reversal symmetry, and at least
-- 3 when further symmetry structure increases the enhancement relative to the
-- full Hilbert-space dimension.  Finite-N RMT refinements live upstream of
-- this source-facing integer summary.
------------------------------------------------------------------------

universalFactorWithoutTRS : Nat
universalFactorWithoutTRS = 2

universalFactorWithTRS : Nat
universalFactorWithTRS = 3

record BirthmarkPrimaryClaimBoundary : Set where
  field
    arbitraryNonstationaryClosedStateHasUniversalMemory : Bool
    earlyRecurrencesCanEnhanceMemory : Bool
    scarIsSpecialCaseOfBroaderBirthmark : Bool
    longTimeLimitCanRetainInitialAndEarlyHistory : Bool
    maximumExplorationPrincipleIsPaperClaim : Bool
    additionalSymmetryNeedsSeparateSubspaceAccounting : Bool

    stadiumSimulationIsExampleNotUniversalProof : Bool
    openSystemGeneralityEstablished : Bool
    experimentalUniversalityEstablished : Bool
    thermodynamicsRefuted : Bool
    allThermalisationPrevented : Bool

birthmarkPrimaryBoundary : BirthmarkPrimaryClaimBoundary
birthmarkPrimaryBoundary = record
  { arbitraryNonstationaryClosedStateHasUniversalMemory = true
  ; earlyRecurrencesCanEnhanceMemory = true
  ; scarIsSpecialCaseOfBroaderBirthmark = true
  ; longTimeLimitCanRetainInitialAndEarlyHistory = true
  ; maximumExplorationPrincipleIsPaperClaim = true
  ; additionalSymmetryNeedsSeparateSubspaceAccounting = true
  ; stadiumSimulationIsExampleNotUniversalProof = true
  ; openSystemGeneralityEstablished = false
  ; experimentalUniversalityEstablished = false
  ; thermodynamicsRefuted = false
  ; allThermalisationPrevented = false
  }

record BirthmarkTimescaleBoundary : Set where
  field
    shortTimeDynamicsIncluded : Bool
    recurrenceBeforeHeisenbergTimeRelevant : Bool
    ThoulessTimeMarksExplorationCrossover : Bool
    finiteCutoffChoiceUniversallySolved : Bool

birthmarkTimescaleBoundary : BirthmarkTimescaleBoundary
birthmarkTimescaleBoundary = record
  { shortTimeDynamicsIncluded = true
  ; recurrenceBeforeHeisenbergTimeRelevant = true
  ; ThoulessTimeMarksExplorationCrossover = true
  ; finiteCutoffChoiceUniversallySolved = false
  }
