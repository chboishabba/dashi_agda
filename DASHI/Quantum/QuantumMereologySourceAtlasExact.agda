{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

data AttributionRole : Set where
  externalSourceClaim :
    AttributionRole
  importedFormalTheoremSource :
    AttributionRole
  localFormalReconstruction :
    AttributionRole
  crossModuleInference :
    AttributionRole
  newDASHITheorem :
    AttributionRole

record AttributionReceipt : Set where
  constructor attribution-receipt
  field
    role : AttributionRole
    owner claim : String

open AttributionReceipt public

record QuantumMereologySource : Set where
  constructor quantum-mereology-source
  field
    authors title venue year identifier supports : String

open QuantumMereologySource public

carrollSingh2021 : QuantumMereologySource
carrollSingh2021 =
  quantum-mereology-source
    "Sean M. Carroll; Ashmeet Singh"
    "Quantum mereology: Factorizing Hilbert space into subsystems with quasiclassical dynamics"
    "Physical Review A 103, 022213"
    "2021"
    "doi:10.1103/PhysRevA.103.022213"
    "Given Hilbert space plus Hamiltonian, studies preferred tensor-product factorisations using quasiclassical pointer robustness and an in-principle objective combining entanglement growth with internal spreading/localization around approximately classical trajectories."

caoCarrollMichalakis2017 : QuantumMereologySource
caoCarrollMichalakis2017 =
  quantum-mereology-source
    "ChunJun Cao; Sean M. Carroll; Spyridon Michalakis"
    "Space from Hilbert space: Recovering geometry from bulk entanglement"
    "Physical Review D 95, 024031"
    "2017"
    "doi:10.1103/PhysRevD.95.024031"
    "Given an already supplied tensor factorisation, uses entanglement structure and mutual-information-derived graph data to reconstruct emergent spatial geometry and studies curvature response."

pasqualiniFortin2026 : QuantumMereologySource
pasqualiniFortin2026 =
  quantum-mereology-source
    "Matías Pasqualini; Sebastian Fortin"
    "Towards a Tensor Product Structure-Grounded Mereology"
    "Entropy 28(6), 627"
    "2026"
    "doi:10.3390/e28060627"
    "Treats tensor-product structures as the subsystem/mereological architecture and argues that the space of TPSs lacks a canonical global meet analogous to the classical partition lattice."

record QuantumMereologyAttributionBoundary : Set where
  field
    citationCreatesLocalProof : Bool
    citationCreatesLocalProofIsFalse : citationCreatesLocalProof ≡ false

    sourceClaimCreatesPreferredFactorisation : Bool
    sourceClaimCreatesPreferredFactorisationIsFalse :
      sourceClaimCreatesPreferredFactorisation ≡ false

    geometryPaperCreatesFullSpacetimeGR : Bool
    geometryPaperCreatesFullSpacetimeGRIsFalse :
      geometryPaperCreatesFullSpacetimeGR ≡ false

    noCanonicalMeetClaimImportedAsKernelTheorem : Bool
    noCanonicalMeetClaimImportedAsKernelTheoremIsFalse :
      noCanonicalMeetClaimImportedAsKernelTheorem ≡ false

canonicalQuantumMereologyAttributionBoundary :
  QuantumMereologyAttributionBoundary
canonicalQuantumMereologyAttributionBoundary = record
  { citationCreatesLocalProof = false
  ; citationCreatesLocalProofIsFalse = refl
  ; sourceClaimCreatesPreferredFactorisation = false
  ; sourceClaimCreatesPreferredFactorisationIsFalse = refl
  ; geometryPaperCreatesFullSpacetimeGR = false
  ; geometryPaperCreatesFullSpacetimeGRIsFalse = refl
  ; noCanonicalMeetClaimImportedAsKernelTheorem = false
  ; noCanonicalMeetClaimImportedAsKernelTheoremIsFalse = refl
  }


carrollSinghObjectiveClaim : AttributionReceipt
carrollSinghObjectiveClaim =
  attribution-receipt
    externalSourceClaim
    "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
    "The source proposes an in-principle preferred-factorisation search minimizing a combination of entanglement growth and internal spreading for quasiclassical subsystem behaviour."

pasqualiniFortinNoCanonicalMeetClaim : AttributionReceipt
pasqualiniFortinNoCanonicalMeetClaim =
  attribution-receipt
    externalSourceClaim
    "Matías Pasqualini; Sebastian Fortin, Entropy 28(6), 627 (2026)"
    "The source argues that the space of tensor-product structures lacks the canonical global meet/lattice structure of classical partition mereology."

dashiSelectionReconstructionReceipt : AttributionReceipt
dashiSelectionReconstructionReceipt =
  attribution-receipt
    localFormalReconstruction
    "DASHI"
    "Typed candidate/criterion/selection records reconstruct the source-described preferred-TPS search without importing existence, uniqueness, or physical correctness."

dashiObserverCrossModuleReceipt : AttributionReceipt
dashiObserverCrossModuleReceipt =
  attribution-receipt
    crossModuleInference
    "DASHI"
    "Existing consumer-descent/non-factorability theorems apply to criterion observations once a TPS candidate family and declared consumer are supplied."

dashiFiniteNoMeetTheoremReceipt : AttributionReceipt
dashiFiniteNoMeetTheoremReceipt =
  attribution-receipt
    newDASHITheorem
    "DASHI"
    "The finite two-tag TPSRefinementSpace regression has no CanonicalMeetAuthority; this local theorem is not the Pasqualini--Fortin physical TPS theorem."


jmdWikidataMereologyFormalSource : AttributionReceipt
jmdWikidataMereologyFormalSource =
  attribution-receipt
    importedFormalTheoremSource
    "JMD (github.com/meta-introspector), RequestProject.Mereology"
    "Retained Lean theorem source for executable Wikidata P361/P2670 mereology: certified part-of closure, proper-part order and well-foundedness, overlap laws, part completeness, and P279/P31 no-confusion. Source-manifest digest: b81a8632dce181845e4c9ca500fb4a9a74df77aeb86a99392361eda991347c35."
