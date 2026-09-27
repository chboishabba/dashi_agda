{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyClassicalBenchmarkExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge as Lean
import DASHI.Quantum.QuantumMereologyExact as QM

------------------------------------------------------------------------
-- CLASSICAL MEREOLOGY BENCHMARK
--
-- The actual Lean RequestProject.Mereology source owns executable P361/P2670
-- mereology: certified part-of closure, proper-part order/well-foundedness,
-- overlap laws, completeness, and no-confusion with P279/P31.
--
-- DASHI consumes those as pinned theorem contracts.  They are a benchmark for
-- TPS-grounded quantum decomposition, not a proof that TPS refinement forms
-- the same classical lattice.
------------------------------------------------------------------------

partNotSubclassContract : Lean.LeanTheoremContract
partNotSubclassContract = Lean.contract35

partNotInstanceContract : Lean.LeanTheoremContract
partNotInstanceContract = Lean.contract36

record ClassicalToQuantumMereologyBoundary : Set where
  field
    classicalPartOrderAutomaticallyIsTPSRefinement : Bool
    classicalPartOrderAutomaticallyIsTPSRefinementIsFalse :
      classicalPartOrderAutomaticallyIsTPSRefinement ≡ false

    classicalOverlapAutomaticallyIsQuantumEntanglement : Bool
    classicalOverlapAutomaticallyIsQuantumEntanglementIsFalse :
      classicalOverlapAutomaticallyIsQuantumEntanglement ≡ false

    classicalPartitionMeetAutomaticallySuppliesTPSMeet : Bool
    classicalPartitionMeetAutomaticallySuppliesTPSMeetIsFalse :
      classicalPartitionMeetAutomaticallySuppliesTPSMeet ≡ false

    wikidataPartCompletenessSelectsPreferredTPS : Bool
    wikidataPartCompletenessSelectsPreferredTPSIsFalse :
      wikidataPartCompletenessSelectsPreferredTPS ≡ false

canonicalClassicalToQuantumMereologyBoundary :
  ClassicalToQuantumMereologyBoundary
canonicalClassicalToQuantumMereologyBoundary = record
  { classicalPartOrderAutomaticallyIsTPSRefinement = false
  ; classicalPartOrderAutomaticallyIsTPSRefinementIsFalse = refl
  ; classicalOverlapAutomaticallyIsQuantumEntanglement = false
  ; classicalOverlapAutomaticallyIsQuantumEntanglementIsFalse = refl
  ; classicalPartitionMeetAutomaticallySuppliesTPSMeet = false
  ; classicalPartitionMeetAutomaticallySuppliesTPSMeetIsFalse = refl
  ; wikidataPartCompletenessSelectsPreferredTPS = false
  ; wikidataPartCompletenessSelectsPreferredTPSIsFalse = refl
  }
