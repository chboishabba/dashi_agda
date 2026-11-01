module DASHI.Information.PNFSpectralGeometry where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

------------------------------------------------------------------------
-- Numeric and finite-coordinate carriers
------------------------------------------------------------------------

record ScalarStructure : Set₁ where
  field
    Scalar : Set
    0# 1# : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    -_ : Scalar → Scalar
    _≤_ _<_ : Scalar → Scalar → Set

open ScalarStructure public

record FiniteCoordinateCarrier : Set₁ where
  field
    Coordinate : Set
    code       : Coordinate → Nat
    code-injective : ∀ {x y} → code x ≡ code y → x ≡ y

open FiniteCoordinateCarrier public

-- A token, word, concept, or PNF predicate is assigned a stable integer
-- coordinate.  The integer is an identifier/index, not its semantic content.
record AtomCoordinate : Set where
  constructor atom-coordinate
  field
    atomCode : Nat

open AtomCoordinate public

atom-coordinate-injective :
  ∀ {x y} → atomCode x ≡ atomCode y → x ≡ y
atom-coordinate-injective {atom-coordinate x} {atom-coordinate .x} refl = refl

atomCarrier : FiniteCoordinateCarrier
atomCarrier = record
  { Coordinate = AtomCoordinate
  ; code = atomCode
  ; code-injective = atom-coordinate-injective
  }

------------------------------------------------------------------------
-- PNF activation coordinates
------------------------------------------------------------------------

-- Rows are evidence windows/documents/events.  Columns are stable atom or
-- predicate coordinates.  Entries are explicit activation measurements,
-- rather than opaque embedding dimensions.
record ActivationSurface (𝕂 : ScalarStructure) : Set₁ where
  open ScalarStructure 𝕂
  field
    Sample    : Set
    Predicate : FiniteCoordinateCarrier
    activation : Sample → Coordinate Predicate → Scalar

open ActivationSurface public

-- Integer-valued coordinates and continuous activation values have different
-- roles.  This prevents an atom identifier from being mistaken for a score.
data NumericRole : Set where
  coordinateIdentifier : NumericRole
  activationScore       : NumericRole
  covarianceWeight      : NumericRole
  spectralWeight        : NumericRole

atomCodeRole : NumericRole
atomCodeRole = coordinateIdentifier

------------------------------------------------------------------------
-- Covariance construction
------------------------------------------------------------------------

record CovarianceConstruction
  (𝕂 : ScalarStructure)
  (X : ActivationSurface 𝕂) : Set₁ where
  open ScalarStructure 𝕂
  open ActivationSurface X
  field
    mean       : Coordinate Predicate → Scalar
    centered   : Sample → Coordinate Predicate → Scalar
    covariance : Coordinate Predicate → Coordinate Predicate → Scalar

    centered-definition :
      ∀ s p → centered s p ≡ activation s p + (- mean p)

    covariance-symmetric :
      ∀ p q → covariance p q ≡ covariance q p

open CovarianceConstruction public

-- The covariance surface is structural co-instantiation over the explicit PNF
-- basis.  It is not cosine similarity between raw-text embeddings.
CovarianceSurface :
  (𝕂 : ScalarStructure) →
  (X : ActivationSurface 𝕂) →
  Set
CovarianceSurface 𝕂 X =
  let open ActivationSurface X
      open ScalarStructure 𝕂
  in Coordinate Predicate → Coordinate Predicate → Scalar

------------------------------------------------------------------------
-- Anonymous spectral coordinates
------------------------------------------------------------------------

-- A mode is identified only by a stable ordinal/index.  No semantic name is
-- required or authorised by the spectral construction.
record ModeCoordinate : Set where
  constructor mode-coordinate
  field
    modeCode : Nat

open ModeCoordinate public

record AnonymousEigenMode
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier)
  (C : Coordinate P → Coordinate P → Scalar 𝕂) : Set₁ where
  open ScalarStructure 𝕂
  field
    mode       : ModeCoordinate
    component  : Coordinate P → Scalar
    eigenvalue : Scalar
    matVec     : Coordinate P → Scalar

    eigen-equation :
      ∀ i → matVec i ≡ eigenvalue * component i

open AnonymousEigenMode public

record AnonymousSpectrum
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier)
  (C : Coordinate P → Coordinate P → Scalar 𝕂) : Set₁ where
  field
    Mode      : Set
    ordinal   : Mode → ModeCoordinate
    eigenMode : Mode → AnonymousEigenMode 𝕂 P C
    ordinal-agrees : ∀ k → mode (eigenMode k) ≡ ordinal k

open AnonymousSpectrum public

-- The output of decomposition is the operator plus anonymous modes.  A
-- downstream label is neither needed nor present in this type.
record SpectralDecomposition
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier)
  (C : Coordinate P → Coordinate P → Scalar 𝕂) : Set₁ where
  field
    spectrum : AnonymousSpectrum 𝕂 P C
    exactReconstruction : Set

open SpectralDecomposition public

------------------------------------------------------------------------
-- Random-matrix noise gate and cleaning
------------------------------------------------------------------------

record SpectralNoiseBand (𝕂 : ScalarStructure) : Set where
  open ScalarStructure 𝕂
  field
    lower upper : Scalar
    ordered     : lower ≤ upper

open SpectralNoiseBand public

data SpectralClass : Set where
  nullBand        : SpectralClass
  candidateSignal : SpectralClass

record NoiseClassifier
  (𝕂 : ScalarStructure)
  (band : SpectralNoiseBand 𝕂) : Set₁ where
  open ScalarStructure 𝕂
  field
    classify : Scalar → SpectralClass
    inside-null-band :
      ∀ {λ} → lower band ≤ λ → λ ≤ upper band → classify λ ≡ nullBand
    above-null-band :
      ∀ {λ} → upper band < λ → classify λ ≡ candidateSignal

open NoiseClassifier public

record EigenvalueFilter
  (𝕂 : ScalarStructure)
  (band : SpectralNoiseBand 𝕂)
  (gate : NoiseClassifier 𝕂 band) : Set₁ where
  open ScalarStructure 𝕂
  field
    shrink : Scalar → Scalar
    filter : Scalar → Scalar

    null-sector-shrunk :
      ∀ {λ} → classify gate λ ≡ nullBand → filter λ ≡ shrink λ

    candidate-sector-retained :
      ∀ {λ} → classify gate λ ≡ candidateSignal → filter λ ≡ λ

open EigenvalueFilter public

-- Cleaning modifies spectral weights while retaining the anonymous modal
-- coordinates used for basis change and reconstruction.
record CleanedCovariance
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier)
  (raw : Coordinate P → Coordinate P → Scalar 𝕂) : Set₁ where
  open ScalarStructure 𝕂
  field
    clean : Coordinate P → Coordinate P → Scalar
    decomposition : SpectralDecomposition 𝕂 P raw
    modeCoordinatesPreserved : Set
    filteredReconstruction    : Set

open CleanedCovariance public

------------------------------------------------------------------------
-- Sparse graph, transport, motif, and lattice views
------------------------------------------------------------------------

record SparsePredicateGraph
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier) : Set₁ where
  open ScalarStructure 𝕂
  field
    edge      : Coordinate P → Coordinate P → Scalar
    supported : Coordinate P → Coordinate P → Bool
    absent-is-zero :
      ∀ {p q} → supported p q ≡ false → edge p q ≡ 0#

open SparsePredicateGraph public

record GraphOperators
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier)
  (G : SparsePredicateGraph 𝕂 P) : Set₁ where
  open ScalarStructure 𝕂
  field
    adjacency : Coordinate P → Coordinate P → Scalar
    degree    : Coordinate P → Scalar
    laplacian : Coordinate P → Coordinate P → Scalar

open GraphOperators public

record TransportOperator
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier) : Set₁ where
  open ScalarStructure 𝕂
  field
    State     : Set
    transport : State → State
    kernel    : Coordinate P → Coordinate P → Scalar

open TransportOperator public

record MotifCompression
  (𝕂 : ScalarStructure)
  (P : FiniteCoordinateCarrier) : Set₁ where
  open ScalarStructure 𝕂
  field
    Motif       : Set
    coefficient : Motif → Scalar
    participates : Coordinate P → Motif → Bool
    reconstructionReceipt : Set
    compressionReceipt    : Set

open MotifCompression public

record PredicateLattice
  (P : FiniteCoordinateCarrier) : Set₁ where
  field
    _⊑_  : Coordinate P → Coordinate P → Set
    meet : Coordinate P → Coordinate P → Coordinate P
    join : Coordinate P → Coordinate P → Coordinate P
    reflexive  : ∀ p → p ⊑ p
    transitive : ∀ {p q r} → p ⊑ q → q ⊑ r → p ⊑ r

open PredicateLattice public

------------------------------------------------------------------------
-- Vector-database boundary
------------------------------------------------------------------------

record RetrievalEmbedding (𝕂 : ScalarStructure) : Set₁ where
  open ScalarStructure 𝕂
  field
    Dimension : Set
    value     : Dimension → Scalar

open RetrievalEmbedding public

data KnowledgeRole : Set where
  retrievalHint       : KnowledgeRole
  structuralCoordinate : KnowledgeRole
  promotionReceipt    : KnowledgeRole

-- Dense embeddings may propose retrieval candidates, but are not the PNF
-- coordinate system and are not promotion receipts.
embeddingRole : ∀ {𝕂} → RetrievalEmbedding 𝕂 → KnowledgeRole
embeddingRole _ = retrievalHint

embedding-role-is-retrieval-only :
  ∀ {𝕂} (e : RetrievalEmbedding 𝕂) → embeddingRole e ≡ retrievalHint
embedding-role-is-retrieval-only e = refl

------------------------------------------------------------------------
-- End-to-end automatic carrier
------------------------------------------------------------------------

record AutomaticPNFSpectralPipeline (𝕂 : ScalarStructure) : Set₁ where
  field
    activations : ActivationSurface 𝕂

  open ActivationSurface activations

  field
    covarianceConstruction : CovarianceConstruction 𝕂 activations
    band       : SpectralNoiseBand 𝕂
    classifier : NoiseClassifier 𝕂 band
    filter     : EigenvalueFilter 𝕂 band classifier
    cleaned    : CleanedCovariance 𝕂 Predicate
                   (covariance covarianceConstruction)

    noModeNamingRequired : Set
    automaticReceipt     : Set

open AutomaticPNFSpectralPipeline public
