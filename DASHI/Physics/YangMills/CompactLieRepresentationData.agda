module DASHI.Physics.YangMills.CompactLieRepresentationData where

-- Finite-dimensional structure data needed to replace SU(2)-specific
-- coefficient expansions in large-field, gauge-fixing, and character bounds.

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieGroupGeometry

record RootStructureData
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    rank dimension : Nat
    Root BasisIndex : Set
    positiveRoot : Root → Set
    cartanBasis : BasisIndex → 𝔤
    rootVector : Root → 𝔤
    structureConstant : BasisIndex → BasisIndex → BasisIndex → Scalar

    rootNormBound structureConstantBound dualCoxeterNumber : Scalar

    FiniteRootSystem : Set
    BasisSpansAlgebra : Set
    StructureConstantsRepresentBracket : Set
    RootNormControlled : Set
    StructureConstantsControlled : Set

    finiteRootSystem : FiniteRootSystem
    basisSpansAlgebra : BasisSpansAlgebra
    structureConstantsRepresentBracket : StructureConstantsRepresentBracket
    rootNormControlled : RootNormControlled
    structureConstantsControlled : StructureConstantsControlled

open RootStructureData public

record HaarMeasureData
    {g a s : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s)) where
  field
    MeasurableSet : Set
    haar : MeasurableSet → Scalar
    wholeGroup : MeasurableSet
    translateLeft translateRight : G → MeasurableSet → MeasurableSet

    normalized : haar wholeGroup ≡ oneS S
    leftInvariant : ∀ x A → haar (translateLeft x A) ≡ haar A
    rightInvariant : ∀ x A → haar (translateRight x A) ≡ haar A

    LocalDensity : Set
    WeylIntegrationFormula : Set
    localDensity : LocalDensity
    weylIntegrationFormula : WeylIntegrationFormula

open HaarMeasureData public

record CharacterEstimateData
    {g a s r : Level}
    {G : Set g} {𝔤 : Set a} {Scalar : Set s}
    (K : CompactSimpleLieGroup G 𝔤)
    (S : OrderedScalar Scalar) : Set (lsuc (g ⊔ a ⊔ s ⊔ r)) where
  field
    Representation : Set r
    character : Representation → G → Scalar
    representationDimension : Representation → Scalar
    normalizedCharacter : Representation → G → Scalar

    CharacterBound : Representation → Set (g ⊔ s)
    SpectralGapAwayFromCenter : Representation → Set (g ⊔ s)
    TensorProductControl : Representation → Representation → Set (r ⊔ s)

    characterBound : ∀ ρ → CharacterBound ρ
    spectralGapAwayFromCenter : ∀ ρ → SpectralGapAwayFromCenter ρ
    tensorProductControl : ∀ ρ σ → TensorProductControl ρ σ

open CharacterEstimateData public
