module DASHI.Core.BiologicalEvidenceBridge where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Core.NonlinearExplodedSparsity
open import DASHI.Core.ExplodedGraphGeometry

------------------------------------------------------------------------
-- Metadata and empirical evidence are explicit inputs
------------------------------------------------------------------------

record NeuronMetadata (X : Set) : Set₁ where
  field
    ROI : Set
    CellType : Set
    MotifClass : Set

    roi : X → ROI
    cellType : X → CellType
    motifClass : X → MotifClass
    degreeImbalance : X → Nat

open NeuronMetadata public

record EnrichmentEvidence
  {X L : Set}
  (K : ThresholdKernel X L)
  (s : State X)
  (Property : X → Set) : Set₁ where
  field
    enrichedAmongDefects : Set
    enrichmentWitness : enrichedAmongDefects

record PerturbationEvidence
  {X L : Set}
  (K : ThresholdKernel X L)
  (s : State X) : Set₁ where
  field
    Perturbation : Set
    applyPerturbation : Perturbation → State X
    sensitiveNode : X → Set
    sensitivityWitness :
      (x : X) → sensitiveNode x →
      Σ Perturbation (λ p → KernelDefect K (applyPerturbation p) x)

------------------------------------------------------------------------
-- Interpretation claims cannot be manufactured from geometry alone
------------------------------------------------------------------------

data BiologicalInterpretation : Set where
  localBuffer
  developmentalConstraintBoundary
  homeostaticControlSite
  perturbationSensitiveSite
  diseaseSensitivityCandidate

record SupportedBiologicalClaim
  {X L : Set}
  (K : ThresholdKernel X L)
  (s : State X)
  (claim : BiologicalInterpretation) : Set₁ where
  field
    target : X → Set
    formalLink : (x : X) → target x →
      (s x ≡ zer) ⊎ KernelDefect K s x
    empiricalEvidence : Set
    evidenceWitness : empiricalEvidence

open SupportedBiologicalClaim public

record ConnectomeEvidenceBridge
  {X L : Set}
  (G : GraphGeometry X)
  (K : ThresholdKernel X L)
  (s : State X) : Set₁ where
  field
    metadata : NeuronMetadata X
    formalGeometry : Set
    formalGeometryWitness : formalGeometry
    claims : BiologicalInterpretation → Set
    supported :
      (claim : BiologicalInterpretation) →
      claims claim → SupportedBiologicalClaim K s claim

supportedClaimCarriesEvidence :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {claim : BiologicalInterpretation} →
  SupportedBiologicalClaim K s claim → Set
supportedClaimCarriesEvidence C = empiricalEvidence C

supportedClaimHasEvidenceWitness :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {claim : BiologicalInterpretation} →
  (C : SupportedBiologicalClaim K s claim) →
  supportedClaimCarriesEvidence C
supportedClaimHasEvidenceWitness C = evidenceWitness C

-- There is intentionally no constructor from neutral/defect geometry alone to
-- SupportedBiologicalClaim.  Metadata, enrichment, perturbation, or equivalent
-- empirical evidence must be supplied.
