module DASHI.Analysis.NonArchimedeanSpectralBidiObligationExact where

------------------------------------------------------------------------
-- Reverse / BIDI obligation compiler for the non-Archimedean spectral lane.
--
-- Downstream advertised claims compile back into exact missing producers.
-- Typed constructors keep distinct claims from collapsing merely because they
-- share the same Boolean status summary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)


data ClaimKind : Set where
  spatialSpectralCircle : ClaimKind
  orbitProduct : ClaimKind
  arbitraryDagCover : ClaimKind
  depthDecaySparsity : ClaimKind
  contractedBoundaryEntropy : ClaimKind
  ropeOptimality : ClaimKind

record BidiClaim : Set where
  constructor bidiClaim
  field
    kind : ClaimKind
    claimName : String
    producerName : String
    theoremExists : Bool
    sameObjectWeldOwned : Bool
    advertisedStrengthOwned : Bool
    promotionAllowed : Bool

open BidiClaim public

spectralCircleSpatialClaim : BidiClaim
spectralCircleSpatialClaim =
  bidiClaim spatialSpectralCircle
    "spatial twisted-block spectral circle"
    "concrete twistedDirMatrix character rechart + group labels + scalar action"
    true false false false

orbitProductClaim : BidiClaim
orbitProductClaim =
  bidiClaim orbitProduct
    "two x3 orbit products multiply to two"
    "odd-residue cyclotomic product + separate x3 orbit partition receipt"
    true true true true

multiPrimeCoverClaim : BidiClaim
multiPrimeCoverClaim =
  bidiClaim arbitraryDagCover
    "arbitrary DAG admits multi-prime adelic cover"
    "construction of MultiPrimeTreeDecomposition from graph hypotheses"
    true false false false

multiPrimeSparsityClaim : BidiClaim
multiPrimeSparsityClaim =
  bidiClaim depthDecaySparsity
    "depth-decaying active attention fraction"
    "nontrivial quantitative bound connecting routing depth to active set size"
    true false false false

holographicAreaClaim : BidiClaim
holographicAreaClaim =
  bidiClaim contractedBoundaryEntropy
    "contracted boundary-state entropy equals cut size times log two"
    "same-object equality between contracted density-state entropy and the existential entropy scalar"
    true false false false

ropeOptimalityClaim : BidiClaim
ropeOptimalityClaim =
  bidiClaim ropeOptimality
    "RoPE medoid compression is transformer-optimal"
    "model-level loss / fidelity theorem built on the geometric invariance theorem"
    true false false false


data MissingObligation : Set where
  needConcreteTwistedCharacterRechart : MissingObligation
  needConcreteGroupLabelling : MissingObligation
  needConcreteScalarActionWeld : MissingObligation
  needConcretePeriodAttachment : MissingObligation
  needConcreteOrbitWeightAttachment : MissingObligation
  needOrbitPartitionWeld : MissingObligation
  needGraphToDecompositionProducer : MissingObligation
  needDepthDecayProducer : MissingObligation
  needBoundaryEntropySameObjectWeld : MissingObligation
  needModelLevelRoPEConsumerTheorem : MissingObligation
  noMissingObligation : MissingObligation

compileMissing : ClaimKind → List MissingObligation
compileMissing spatialSpectralCircle =
  needConcreteTwistedCharacterRechart ∷
  needConcreteGroupLabelling ∷
  needConcreteScalarActionWeld ∷
  needConcretePeriodAttachment ∷
  needConcreteOrbitWeightAttachment ∷
  []
compileMissing orbitProduct = []
compileMissing arbitraryDagCover = needGraphToDecompositionProducer ∷ []
compileMissing depthDecaySparsity = needDepthDecayProducer ∷ []
compileMissing contractedBoundaryEntropy = needBoundaryEntropySameObjectWeld ∷ []
compileMissing ropeOptimality = needModelLevelRoPEConsumerTheorem ∷ []

record BidiFirewall : Set where
  constructor bidiFirewall
  field
    theoremNameImpliesAdvertisedStrength : Bool
    theoremExistsImpliesSameObjectWeld : Bool
    conditionalConsumerImpliesProducer : Bool
    architecturalAnalogyImpliesTheoremTransport : Bool
    genericInfrastructureMayReplaceConcreteAttachment : Bool

canonicalBidiFirewall : BidiFirewall
canonicalBidiFirewall = bidiFirewall false false false false false

spatialSpectralCircleExactCutset :
  compileMissing (kind spectralCircleSpatialClaim)
  ≡ needConcreteTwistedCharacterRechart ∷
    needConcreteGroupLabelling ∷
    needConcreteScalarActionWeld ∷
    needConcretePeriodAttachment ∷
    needConcreteOrbitWeightAttachment ∷
    []
spatialSpectralCircleExactCutset = refl

orbitProductIsPromotable :
  compileMissing (kind orbitProductClaim) ≡ []
orbitProductIsPromotable = refl

multiPrimeCoverNeedsProducer :
  compileMissing (kind multiPrimeCoverClaim)
  ≡ needGraphToDecompositionProducer ∷ []
multiPrimeCoverNeedsProducer = refl

multiPrimeSparsityNeedsQuantitativeProducer :
  compileMissing (kind multiPrimeSparsityClaim)
  ≡ needDepthDecayProducer ∷ []
multiPrimeSparsityNeedsQuantitativeProducer = refl

holographicClaimNeedsSameObjectWeld :
  compileMissing (kind holographicAreaClaim)
  ≡ needBoundaryEntropySameObjectWeld ∷ []
holographicClaimNeedsSameObjectWeld = refl

ropeOptimalityNeedsModelConsumer :
  compileMissing (kind ropeOptimalityClaim)
  ≡ needModelLevelRoPEConsumerTheorem ∷ []
ropeOptimalityNeedsModelConsumer = refl
