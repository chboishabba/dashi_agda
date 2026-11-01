module DASHI.Analysis.NonArchimedeanDFTSimilaritySpectrumReuseExact where

------------------------------------------------------------------------
-- EXISTING-MACHINERY CROSS-POLLINATION: DFT SIMILARITY -> SPECTRUM
--
-- DASHI already owns an exact generic finite-matrix similarity theorem in the
-- Yang--Mills Gate-4 lane: explicit change/inverse matrices transport an
-- eigenpair through S^-1 A S with the same eigenvalue, and determinants are
-- invariant under the same similarity data.
--
-- Therefore this non-Archimedean lane does not reopen generic basis-invariance
-- mathematics.  Source `DFT.lean` already provides the concrete DFT basis and
-- inverse relation.  The only source-specific spectral payment is identifying
-- the concrete conjugated twisted matrix with the claimed monomial operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteSimilaritySpectrumDeterminantExact as Similarity

record DFTSimilarityInstantiation
    (Matrix Vector Scalar : Set) : Set₁ where
  field
    similarityData : Similarity.FiniteSimilaritySpectrumData Matrix Vector Scalar
    sourceDFTBasisReceipt : Set
    sourceDFTInverseReceipt : Set
    concreteTwistedOperatorReceipt : Set

open DFTSimilarityInstantiation public

transportEigenpair :
  ∀ {Matrix Vector Scalar}
    (inst : DFTSimilarityInstantiation Matrix Vector Scalar) →
  Similarity.Eigenpair
    (similarityData inst)
    (Similarity.operator (similarityData inst)) →
  Similarity.Eigenpair
    (similarityData inst)
    (Similarity.similarityOperator (similarityData inst))
transportEigenpair inst =
  Similarity.transportEigenpairThroughSimilarity (similarityData inst)

record SimilarityReuseBoundary : Set where
  constructor similarityReuseBoundary
  field
    genericSimilaritySpectrumTransportOwned : Bool
    genericDeterminantSimilarityTransportOwned : Bool
    sourceConcreteDFTBasisOwned : Bool
    sourceConcreteDFTInverseOwned : Bool
    genericSimilarityProofShouldBeRebuiltHere : Bool
    concreteConjugatedMatrixMonomialIdentityStillSourceSpecific : Bool

canonicalSimilarityReuseBoundary : SimilarityReuseBoundary
canonicalSimilarityReuseBoundary =
  similarityReuseBoundary true true true true false true

genericSimilaritySearchPruned :
  SimilarityReuseBoundary.genericSimilarityProofShouldBeRebuiltHere
    canonicalSimilarityReuseBoundary
  ≡ false
genericSimilaritySearchPruned = refl
