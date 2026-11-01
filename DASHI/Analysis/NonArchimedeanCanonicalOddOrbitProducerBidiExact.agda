module DASHI.Analysis.NonArchimedeanCanonicalOddOrbitProducerBidiExact where

------------------------------------------------------------------------
-- CANONICAL TWO-ORBIT PRODUCER
--
-- The source repo owns the exact order of 3 modulo 2^n and the cardinality of
-- the odd residues.  `orbit_weight_magnitude_sq` then consumes an arbitrary
-- finite C carrying closure/cardinality/oddness receipts.  What is not located
-- as one exported theorem is the canonical package
--
--   C1 = <3>,   C2 = -C1,
--
-- together with all receipts required by the downstream weight theorem and the
-- product/partition theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record CanonicalOddOrbitProducer : Set₁ where
  field
    OddResidue : Set
    C₁ C₂ : OddResidue → Set
    timesThree negate : OddResidue → OddResidue

    cOneGeneratedByThree : Set
    cOneClosedUnderThree : Set
    cOneHasRequiredCardinality : Set
    cOneContainsOnlyOddResidues : Set

    cTwoIsNegativeImage : Set
    cTwoClosedUnderThree : Set
    cTwoHasRequiredCardinality : Set
    cTwoContainsOnlyOddResidues : Set

    cOneCtwoDisjoint : Set
    cOneCtwoCoverAllOddResidues : Set

open CanonicalOddOrbitProducer public


data OrbitProducerObligation : Set where
  instantiateCOneAsPowersOfThree : OrbitProducerObligation
  proveCOneClosure : OrbitProducerObligation
  proveCOneCardinalityFromOrder : OrbitProducerObligation
  proveCOneOddness : OrbitProducerObligation
  defineCTwoByNegation : OrbitProducerObligation
  provePartitionDisjointness : OrbitProducerObligation
  provePartitionExhaustivityFromOddCardinality : OrbitProducerObligation

  reproveOrderOfThree : OrbitProducerObligation
  reproveOddResidueCardinality : OrbitProducerObligation
  reproveCyclotomicProduct : OrbitProducerObligation


data OrbitProducerDisposition : Set where
  live : OrbitProducerDisposition
  downstream : OrbitProducerDisposition
  pruned : OrbitProducerDisposition

orbitProducerDisposition : OrbitProducerObligation → OrbitProducerDisposition
orbitProducerDisposition instantiateCOneAsPowersOfThree = live
orbitProducerDisposition proveCOneClosure = downstream
orbitProducerDisposition proveCOneCardinalityFromOrder = downstream
orbitProducerDisposition proveCOneOddness = downstream
orbitProducerDisposition defineCTwoByNegation = downstream
orbitProducerDisposition provePartitionDisjointness = downstream
orbitProducerDisposition provePartitionExhaustivityFromOddCardinality = downstream
orbitProducerDisposition reproveOrderOfThree = pruned
orbitProducerDisposition reproveOddResidueCardinality = pruned
orbitProducerDisposition reproveCyclotomicProduct = pruned

highestAlphaOrbitProducerPath : List OrbitProducerObligation
highestAlphaOrbitProducerPath =
  instantiateCOneAsPowersOfThree ∷
  proveCOneClosure ∷
  proveCOneCardinalityFromOrder ∷
  proveCOneOddness ∷
  defineCTwoByNegation ∷
  provePartitionDisjointness ∷
  provePartitionExhaustivityFromOddCardinality ∷
  []

record SourceOrbitProducerBoundary : Set where
  constructor sourceOrbitProducerBoundary
  field
    orderOfThreeOwned : Bool
    oddResidueCardinalityOwned : Bool
    conditionalOrbitWeightMagnitudeOwned : Bool
    conditionalCyclotomicPartitionProductOwned : Bool
    exportedCanonicalCOneCTwoPackageLocated : Bool
    canonicalPackageShouldBeReplacedByPaperProse : Bool

canonicalSourceOrbitProducerBoundary : SourceOrbitProducerBoundary
canonicalSourceOrbitProducerBoundary =
  sourceOrbitProducerBoundary true true true true false false

canonicalPackageStillLive :
  SourceOrbitProducerBoundary.exportedCanonicalCOneCTwoPackageLocated
    canonicalSourceOrbitProducerBoundary
  ≡ false
canonicalPackageStillLive = refl
