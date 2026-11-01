module Ontology.DNA.SupervoxelAdmissibility where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec using (Vec; map; []; _∷_)
open import Data.Vec.Base using (reverse)
open import Data.Vec.Properties using (map-reverse; reverse-involutive)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import Ontology.DNA.Supervoxel4Adic using
  (complement; complement-involutive; FlatDNA256)
open import Ontology.DNA.ChemistryConcrete using
  (_&&_; featureMapConcrete; admissibleConcrete)
open import Ontology.DNA.ChemistryUVConcrete using
  (uvKernelConcrete; admissibleUVConcrete)
open import Ontology.DNA.ComplementLaws using (complementFeature; featureMap-complement)
open import Ontology.DNA.ChemistrySheetHamiltonian using
  (chemistryHamiltonian)

------------------------------------------------------------------------
-- Supervoxel admissibility surface.
-- Chemistry constraints act on paired voxels under reverse-complement, so we
-- package the paired state, its checksum surface, and the theorem-thin
-- admissibility contract in one local owner module.

record Supervoxel256 : Set where
  constructor supervoxel256
  field
    leftVoxel : FlatDNA256
    rightVoxel : FlatDNA256

reverseComplement256 : FlatDNA256 → FlatDNA256
reverseComplement256 xs = reverse (map complement xs)

map-complement-involutive :
  ∀ {n} →
  (xs : Vec _ n) →
  map complement (map complement xs) ≡ xs
map-complement-involutive [] = refl
map-complement-involutive (x ∷ xs)
  rewrite complement-involutive x
        | map-complement-involutive xs = refl

reverseComplement256-involutive :
  (xs : FlatDNA256) →
  reverseComplement256 (reverseComplement256 xs) ≡ xs
reverseComplement256-involutive xs
  rewrite map-reverse complement (map complement xs)
        | map-complement-involutive xs
        | reverse-involutive xs = refl

record SupervoxelChecksum : Set where
  constructor superChecksum
  field
    leftHamiltonian : Nat
    rightHamiltonian : Nat
    uvRisk : Nat

supervoxelChecksum : Supervoxel256 → SupervoxelChecksum
supervoxelChecksum sv =
  superChecksum
    (chemistryHamiltonian (Supervoxel256.leftVoxel sv))
    (chemistryHamiltonian (Supervoxel256.rightVoxel sv))
    (uvKernelConcrete (Supervoxel256.leftVoxel sv)
      + uvKernelConcrete (Supervoxel256.rightVoxel sv))

pairedByComplementFeature : (sv : Supervoxel256) → Set
pairedByComplementFeature sv =
  featureMapConcrete (map complement (Supervoxel256.leftVoxel sv))
    ≡ complementFeature (featureMapConcrete (Supervoxel256.leftVoxel sv))

pairedByComplementFeatureWitness :
  (sv : Supervoxel256) → pairedByComplementFeature sv
pairedByComplementFeatureWitness sv =
  featureMap-complement (Supervoxel256.leftVoxel sv)

admissibleSupervoxel : Supervoxel256 → Bool
admissibleSupervoxel sv =
  (admissibleConcrete (Supervoxel256.leftVoxel sv)
    && admissibleConcrete (Supervoxel256.rightVoxel sv))
    && (admissibleUVConcrete (Supervoxel256.leftVoxel sv)
    && admissibleUVConcrete (Supervoxel256.rightVoxel sv))

record SupervoxelAdmissibilitySurface : Set₁ where
  field
    localAdmissible : Supervoxel256 → Bool
    pairedFeatureLaw : (sv : Supervoxel256) → pairedByComplementFeature sv
    checksum : Supervoxel256 → SupervoxelChecksum
    involution : Supervoxel256 → Supervoxel256
    involutionLaw : (sv : Supervoxel256) → involution (involution sv) ≡ sv
    checksumWitness : (sv : Supervoxel256) → checksum sv ≡ supervoxelChecksum sv

swapRC : Supervoxel256 → Supervoxel256
swapRC sv =
  supervoxel256
    (reverseComplement256 (Supervoxel256.rightVoxel sv))
    (reverseComplement256 (Supervoxel256.leftVoxel sv))

swapRC-involutive : (sv : Supervoxel256) → swapRC (swapRC sv) ≡ sv
swapRC-involutive sv
  rewrite reverseComplement256-involutive (Supervoxel256.leftVoxel sv)
        | reverseComplement256-involutive (Supervoxel256.rightVoxel sv) = refl

swapRC-leftHamiltonianWitness :
  (sv : Supervoxel256) →
  SupervoxelChecksum.leftHamiltonian (supervoxelChecksum (swapRC sv))
    ≡ chemistryHamiltonian (reverseComplement256 (Supervoxel256.rightVoxel sv))
swapRC-leftHamiltonianWitness sv = refl

swapRC-rightHamiltonianWitness :
  (sv : Supervoxel256) →
  SupervoxelChecksum.rightHamiltonian (supervoxelChecksum (swapRC sv))
    ≡ chemistryHamiltonian (reverseComplement256 (Supervoxel256.leftVoxel sv))
swapRC-rightHamiltonianWitness sv = refl

swapRC-uvRiskWitness :
  (sv : Supervoxel256) →
  SupervoxelChecksum.uvRisk (supervoxelChecksum (swapRC sv))
    ≡ uvKernelConcrete (reverseComplement256 (Supervoxel256.rightVoxel sv))
      + uvKernelConcrete (reverseComplement256 (Supervoxel256.leftVoxel sv))
swapRC-uvRiskWitness sv = refl

swapRC-checksum-swapped :
  (hamiltonianRCInvariant : ∀ xs →
    chemistryHamiltonian (reverseComplement256 xs) ≡ chemistryHamiltonian xs) →
  (uvRCInvariant : ∀ xs →
    uvKernelConcrete (reverseComplement256 xs) ≡ uvKernelConcrete xs) →
  (sv : Supervoxel256) →
  supervoxelChecksum (swapRC sv)
    ≡ superChecksum
        (SupervoxelChecksum.rightHamiltonian (supervoxelChecksum sv))
        (SupervoxelChecksum.leftHamiltonian (supervoxelChecksum sv))
        (SupervoxelChecksum.uvRisk (supervoxelChecksum sv))
swapRC-checksum-swapped hamiltonianRCInvariant uvRCInvariant sv
  rewrite hamiltonianRCInvariant (Supervoxel256.rightVoxel sv)
        | hamiltonianRCInvariant (Supervoxel256.leftVoxel sv)
        | uvRCInvariant (Supervoxel256.rightVoxel sv)
        | uvRCInvariant (Supervoxel256.leftVoxel sv)
        | +-comm
            (uvKernelConcrete (Supervoxel256.rightVoxel sv))
            (uvKernelConcrete (Supervoxel256.leftVoxel sv)) = refl

swapRC-checksum-invariant :
  (hamiltonianRCInvariant : ∀ xs →
    chemistryHamiltonian (reverseComplement256 xs) ≡ chemistryHamiltonian xs) →
  (uvRCInvariant : ∀ xs →
    uvKernelConcrete (reverseComplement256 xs) ≡ uvKernelConcrete xs) →
  (sv : Supervoxel256) →
  supervoxelChecksum (swapRC sv)
    ≡ superChecksum
        (chemistryHamiltonian (Supervoxel256.rightVoxel sv))
        (chemistryHamiltonian (Supervoxel256.leftVoxel sv))
        (uvKernelConcrete (Supervoxel256.leftVoxel sv)
          + uvKernelConcrete (Supervoxel256.rightVoxel sv))
swapRC-checksum-invariant hamiltonianRCInvariant uvRCInvariant sv =
  swapRC-checksum-swapped hamiltonianRCInvariant uvRCInvariant sv

supervoxelAdmissibilitySurface : SupervoxelAdmissibilitySurface
supervoxelAdmissibilitySurface = record
  { localAdmissible = admissibleSupervoxel
  ; pairedFeatureLaw = pairedByComplementFeatureWitness
  ; checksum = supervoxelChecksum
  ; involution = swapRC
  ; involutionLaw = swapRC-involutive
  ; checksumWitness = λ _ → refl
  }
