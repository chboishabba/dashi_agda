{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySelectionConvergence2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- 2024/2026 SUBSYSTEM-SELECTION COMPARISON BOUNDARY
--
-- Distinct external scientific programmes are deliberately not collapsed:
-- * Carroll--Singh 2021: Schwinger/quasiclassical preferred-TPS objective;
-- * Adil et al. 2026: search for factorizations admitting robust pointer states;
-- * Andreadakis--Dallas--Zanardi 2024: generalized TPS / operator-algebra
--   emergence via long-time algebraic OTOC / minimal scrambling;
-- * Zanardi--Dallas--Andreadakis 2026: parameter-dependent g-TPS selection by
--   a scrambling functional and induced information-geometric susceptibility.
--
-- Lean source owner:
--   RequestProject.QuantumMereologySelectionConvergence2026
--
-- It provides a proof-relevant common comparison surface where exact agreement
-- between objectives requires an explicit same-selected-candidate witness.
-- Consumer-level agreement is separately typed and weaker than candidate
-- identity.  A parameter-dependent selection change is not promoted to a
-- physical phase transition without further scientific payment.
------------------------------------------------------------------------

record SelectionConvergence2026Status : Set where
  field
    CrossObjectiveAgreementRequiresExplicitWitness : Bool
    CrossObjectiveAgreementRequiresExplicitWitnessIsTrue :
      CrossObjectiveAgreementRequiresExplicitWitness ≡ true

    SharedCandidateCarrierCreatesSamePreferredTPS : Bool
    SharedCandidateCarrierCreatesSamePreferredTPSIsFalse :
      SharedCandidateCarrierCreatesSamePreferredTPS ≡ false

    SharedHamiltonianCreatesSamePreferredTPS : Bool
    SharedHamiltonianCreatesSamePreferredTPSIsFalse :
      SharedHamiltonianCreatesSamePreferredTPS ≡ false

    FiniteMinimizersCreateCrossObjectiveConvergence : Bool
    FiniteMinimizersCreateCrossObjectiveConvergenceIsFalse :
      FiniteMinimizersCreateCrossObjectiveConvergence ≡ false

    ConsumerConvergenceCreatesCandidateIdentity : Bool
    ConsumerConvergenceCreatesCandidateIdentityIsFalse :
      ConsumerConvergenceCreatesCandidateIdentity ≡ false

    ParametricSelectionChangeCreatesPhysicalPhaseTransition : Bool
    ParametricSelectionChangeCreatesPhysicalPhaseTransitionIsFalse :
      ParametricSelectionChangeCreatesPhysicalPhaseTransition ≡ false

    GTPSSourceCreatesCarrollSinghObjectiveEquivalence : Bool
    GTPSSourceCreatesCarrollSinghObjectiveEquivalenceIsFalse :
      GTPSSourceCreatesCarrollSinghObjectiveEquivalence ≡ false

canonicalSelectionConvergence2026Status : SelectionConvergence2026Status
canonicalSelectionConvergence2026Status = record
  { CrossObjectiveAgreementRequiresExplicitWitness = true
  ; CrossObjectiveAgreementRequiresExplicitWitnessIsTrue = refl
  ; SharedCandidateCarrierCreatesSamePreferredTPS = false
  ; SharedCandidateCarrierCreatesSamePreferredTPSIsFalse = refl
  ; SharedHamiltonianCreatesSamePreferredTPS = false
  ; SharedHamiltonianCreatesSamePreferredTPSIsFalse = refl
  ; FiniteMinimizersCreateCrossObjectiveConvergence = false
  ; FiniteMinimizersCreateCrossObjectiveConvergenceIsFalse = refl
  ; ConsumerConvergenceCreatesCandidateIdentity = false
  ; ConsumerConvergenceCreatesCandidateIdentityIsFalse = refl
  ; ParametricSelectionChangeCreatesPhysicalPhaseTransition = false
  ; ParametricSelectionChangeCreatesPhysicalPhaseTransitionIsFalse = refl
  ; GTPSSourceCreatesCarrollSinghObjectiveEquivalence = false
  ; GTPSSourceCreatesCarrollSinghObjectiveEquivalenceIsFalse = refl
  }

andreadakisDallasZanardi2024Claim : Sources.AttributionReceipt
andreadakisDallasZanardi2024Claim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Faidon Andreadakis; Emanuel Dallas; Paolo Zanardi, Phys. Rev. A 109, 052424 (2024), DOI 10.1103/PhysRevA.109.052424"
    "Studies long-time algebraic OTOC relative to operator subalgebras/generalized TPSs and uses minimal long-time scrambling as a subsystem-emergence criterion. It is not identified with the Carroll--Singh Schwinger objective."

zanardiDallasAndreadakis2026Claim : Sources.AttributionReceipt
zanardiDallasAndreadakis2026Claim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Paolo Zanardi; Emanuel Dallas; Faidon Andreadakis, Phys. Rev. A 113, 042201 (2026), DOI 10.1103/r193-5s7w"
    "Introduces mereological quantum phase transitions from a variational family of operator algebras/generalized TPSs, a parameter-dependent Hamiltonian and scrambling-functional minimization, with an induced information-geometric metric/algebra susceptibility. Citation does not create a DASHI g-TPS implementation or physical phase-transition theorem."

adilEtAl2026SelectionClaim : Sources.AttributionReceipt
adilEtAl2026SelectionClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Arsalan Adil et al., Phys. Rev. D 113, 103535 (2026), DOI 10.1103/vj4x-96fk"
    "Searches fixed Hamiltonians for tensor-product structures admitting robust pointer states and reports multiple quasiclassical factorizations in studied settings. It is not imported as a universal local nonuniqueness theorem and is not identified with the Carroll--Singh or algebraic-OTOC objective."

leanSelectionConvergenceSourceReceipt : Sources.AttributionReceipt
leanSelectionConvergenceSourceReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologySelectionConvergence2026"
    "Source-written common selection-comparison surface: exact cross-objective convergence requires an explicit same-selected-candidate witness; consumer convergence is separately typed and weaker; parameter-dependent selected-candidate change is not automatically a physical phase transition."

dashiSelectionConvergenceCrossProverReceipt : Sources.AttributionReceipt
dashiSelectionConvergenceCrossProverReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI Agda"
    "Records the Lean comparison theorem surface and source roles while preserving objective non-collapse, consumer-relative equivalence, nonuniqueness and physical-phase-transition firewalls."
