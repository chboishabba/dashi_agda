module DASHI.Chemistry.LineageBidiDiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)

import DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact as Bidi
import DASHI.Biology.KitzerowBH4FluxCausalModelsExact as BH4

------------------------------------------------------------------------
-- Compile an explicit pair of competing causal models plus a blocked consumer
-- into the repo's existing lineage-aware BIDI candidate surface.
------------------------------------------------------------------------

record ModelDiscriminationProblem : Set where
  constructor modelDiscriminationProblem
  field
    problemKey : String
    leftModelReference : String
    rightModelReference : String
    collisionReference : String
    separatingCoordinateReference : String
    perturbationKind : Bidi.LineagePerturbationKind
    interventionReference : String
    authorityReference : String
    atomReadoutReference : String
    electronReadoutReference : String
    bondGeometryReadoutReference : String
    productByproductReadoutReference : String
    biologicalReadoutReference : String
    frozenConsumerReference : String
    nuisanceReference : String
    calibrationReference : String
    provenanceReference : String

open ModelDiscriminationProblem public

synthesizeCandidate : ModelDiscriminationProblem → Bidi.LineageDiscriminatorCandidate
synthesizeCandidate p =
  Bidi.lineageDiscriminatorCandidate
    (problemKey p)
    (perturbationKind p)
    (leftModelReference p ++ " versus " ++ rightModelReference p)
    (collisionReference p)
    (interventionReference p)
    (authorityReference p)
    (atomReadoutReference p)
    (electronReadoutReference p)
    (bondGeometryReadoutReference p)
    (productByproductReadoutReference p)
    (biologicalReadoutReference p)
    (frozenConsumerReference p)
    (nuisanceReference p)
    (calibrationReference p)
    (separatingCoordinateReference p)
    (provenanceReference p)

bh4AllocatorVsParallelProblem : ModelDiscriminationProblem
bh4AllocatorVsParallelProblem =
  modelDiscriminationProblem
    "BH4 H1 allocator vs H3 parallel-redox discriminator"
    "BH4.h1Allocator"
    "BH4.h3Parallel"
    "both models can explain stress-associated BH4/redox/branch covariance"
    "selective BH4-mediated change in branch flux after orthogonal BH4 versus redox perturbation"
    Bidi.redoxPerturbation
    "factorial perturbation of BH4 synthesis/recycling and redox driver"
    "independent experimental/clinical authority required"
    "stable-isotope atom tracing where informative"
    "BH4/BH2 and NAD(P)H redox/electron-equivalent readouts"
    "enzyme/cofactor state and any source-backed structural change"
    "J_PAH/J_TH/J_TPH/J_NOS/J_AGMO products and byproducts"
    "cell-type-specific downstream mTOR/circuit/metabolic readouts"
    "does BH4 mediate coordinated branch redistribution for the declared context?"
    "genotype, sex, development, cell type, compartment, substrate/O2 and baseline redox"
    "quantitative concentration/flux calibration required"
    "Kitzerow BH4 reaction/source atlas plus acquired perturbation dataset"

canonicalBH4AllocatorVsParallelCandidate : Bidi.LineageDiscriminatorCandidate
canonicalBH4AllocatorVsParallelCandidate = synthesizeCandidate bh4AllocatorVsParallelProblem

pbCaLocalVsFunctionalProblem : ModelDiscriminationProblem
pbCaLocalVsFunctionalProblem =
  modelDiscriminationProblem
    "Pb/Ca local-recognition vs functional-equivalence discriminator"
    "local target substitution model"
    "whole downstream functional equivalence model"
    "both can agree on +2 charge and site occupancy"
    "coordination geometry plus protein/cell functional divergence"
    Bidi.ionicSubstitutionPerturbation
    "controlled Pb2+ for Ca2+ substitution at specified target"
    "independent exposure/intervention authority required"
    "Z/isotope lineage retains Pb versus Ca identity"
    "electronic/coordination state readout; no fictive persistent electron identity"
    "coordination number/geometry and protein conformation"
    "bound/unbound ionic species and competing ligand products"
    "protein function and calcium-signalling downstream readouts"
    "does target-local substitution preserve the declared downstream function?"
    "ion concentration, competing Ca/Mg/Zn, pH, hydration, site rigidity and target expression"
    "affinity/occupancy/functional assay calibration required"
    "ionic mimicry source atlas + target-specific assay"

canonicalPbCaFunctionalCandidate : Bidi.LineageDiscriminatorCandidate
canonicalPbCaFunctionalCandidate = synthesizeCandidate pbCaLocalVsFunctionalProblem

record LineageBidiSynthesisBoundary : Set where
  constructor lineageBidiSynthesisBoundary
  field
    competingModelsDriveCandidateGeneration : Bool
    competingModelsDriveCandidateGenerationIsTrue : competingModelsDriveCandidateGeneration ≡ true
    generatedCandidateCreatesTruth : Bool
    generatedCandidateCreatesTruthIsFalse : generatedCandidateCreatesTruth ≡ false
    generatedCandidateCreatesAuthority : Bool
    generatedCandidateCreatesAuthorityIsFalse : generatedCandidateCreatesAuthority ≡ false
    nuisanceAndCalibrationRemainExplicit : Bool
    nuisanceAndCalibrationRemainExplicitIsTrue : nuisanceAndCalibrationRemainExplicit ≡ true
    consumerFrozenDuringSynthesis : Bool
    consumerFrozenDuringSynthesisIsTrue : consumerFrozenDuringSynthesis ≡ true

open LineageBidiSynthesisBoundary public

canonicalLineageBidiSynthesisBoundary : LineageBidiSynthesisBoundary
canonicalLineageBidiSynthesisBoundary =
  lineageBidiSynthesisBoundary true refl false refl false refl true refl true refl
