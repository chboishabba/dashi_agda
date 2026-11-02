{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact where

------------------------------------------------------------------------
-- N21: EXACT INPUT-WORD / SPARSE-WITNESS BOUNDARY FOR KARP MAX CUT.
--
-- THIS IS AN INTERFACE: no gamma/zigzag graph decoder is fabricated.
-- Consume the actual graph Cut.WeightedCutGraph n with signed weights.
-- A GraphWordCodec must supply a faithful total parser with a strict
-- 2m <= input bit length theorem. The existing sparse verifier then
-- proves a bounded witness BIDI for every word, including malformed
-- words that are false in the source language.
--
-- Conditional InNP assembler requires real verifier machine cost and
-- certificate-bound receipts. Those are not inferred from AST purity.
--
-- Original: Richard Karp (1972). DASHI source owners:
--   Karp21SparseEndpointConsistencySoundExact,
--   Karp21PartitionSparseCutBidiExact, PolynomialReductionExact.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (trans; subst)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact as N21
import DASHI.Mathematics.Complexity.Karp21PartitionSparseCutBidiExact as Bidi

GraphInstance : Set
GraphInstance = Σ Nat (λ n → Cut.WeightedCutGraph n)

record SparseGraphWordCodec : Set where
  field
    decodeGraph : Word.BitWord → Maybe GraphInstance

    -- In the intended Karp graph word this is checked after parsing
    -- gamma(n), gamma(m), m strictly ordered triples and gamma(W).
    -- Each triple uses at least three bits, so 2m <= word length.
    edgeBitBound :
      (word : Word.BitWord) (graph : GraphInstance) →
      decodeGraph word ≡ just graph →
      Sparse.twoPerEdge (length (Cut.edges (proj₂ graph)))
        ≤ Word.encodingSize word

open SparseGraphWordCodec public

module OnCodec (codec : SparseGraphWordCodec) where
  CanonicalWeightedMaxCutWordYES : Word.BitWord → Set
  CanonicalWeightedMaxCutWordYES word
    with decodeGraph codec word
  ... | nothing = ⊥
  ... | just graph = Cut.WeightedMaxCutYES (proj₂ graph)

  canonicalWeightedMaxCutLanguage : PR.Language Word.BitWord
  canonicalWeightedMaxCutLanguage =
    record { PR.accepts = CanonicalWeightedMaxCutWordYES }

  verifyCanonicalSparseGraphWord :
    Word.BitWord → Word.BitWord → Bool
  verifyCanonicalSparseGraphWord word certificate
    with decodeGraph codec word
  ... | nothing = false
  ... | just graph =
    Sparse.verifySparseCutBitWord (proj₂ graph) certificate

  canonicalSparseCertificateAdmissible :
    Word.BitWord → Word.BitWord → Set
  canonicalSparseCertificateAdmissible word bits =
    Word.encodingSize bits ≤ Word.encodingSize word

  BoundedSparseGraphWordYES : Word.BitWord → Set
  BoundedSparseGraphWordYES word =
    Σ Word.BitWord (λ bits →
      canonicalSparseCertificateAdmissible word bits
      × verifyCanonicalSparseGraphWord word bits ≡ true)

  -- Every graph YES has an accepted certificate of exact size 2m;
  -- the codec's strictly checked edge budget converts it to a
  -- certificate no longer than its own canonical graph input word.
  canonicalGraphWordToBoundedSparse :
    (word : Word.BitWord) →
    CanonicalWeightedMaxCutWordYES word →
    BoundedSparseGraphWordYES word
  canonicalGraphWordToBoundedSparse word accepted
    with decodeGraph codec word
  ... | nothing = ⊥-elim accepted
  ... | just graph
    with Bidi.actualCutToSizeExactSparse (proj₂ graph) accepted
  ...   | bits , (exactLength , acceptedBits) =
    bits ,
      ( NatP.≤-trans
          (NatP.≤-reflexive exactLength)
          (edgeBitBound codec word graph refl)
      , acceptedBits )

  boundedSparseToCanonicalGraphWord :
    (word : Word.BitWord) →
    BoundedSparseGraphWordYES word →
    CanonicalWeightedMaxCutWordYES word
  boundedSparseToCanonicalGraphWord word
    (bits , (bound , accepted))
    with decodeGraph codec word
  ... | nothing = ⊥-elim (N21.falseNotTrue accepted)
  ... | just graph =
    N21.sparseAcceptedBitWordImpliesFullGraphYES
      (proj₂ graph) bits accepted

  n21EncodedSparseWordBidi :
    (word : Word.BitWord) →
    PR.Iff (CanonicalWeightedMaxCutWordYES word)
      (BoundedSparseGraphWordYES word)
  n21EncodedSparseWordBidi word =
    PR.iff
      (canonicalGraphWordToBoundedSparse word)
      (boundedSparseToCanonicalGraphWord word)

  -- Concrete NP certificate assembly; polynomial evidence is deliberately
  -- not conjured from an arbitrary extensional function or Boolean flag.
  karpWeightedMaxCutInNPFromMachineReceipts :
    (cost : PR.PolynomialCostModel Word.BitWord) →
    PR.polynomialTimeVerifier cost verifyCanonicalSparseGraphWord →
    PR.polynomialCertificateBound
      cost canonicalSparseCertificateAdmissible →
    PR.InNP cost canonicalWeightedMaxCutLanguage
  karpWeightedMaxCutInNPFromMachineReceipts
    cost verifierClock certificateBound =
    record
      { PR.Certificate = Word.BitWord
      ; PR.verifies = verifyCanonicalSparseGraphWord
      ; PR.certificateAdmissible = canonicalSparseCertificateAdmissible
      ; PR.sound = λ word bits _ check →
          boundedSparseToCanonicalGraphWord word
            (bits , (NatP.≤-refl , check))
      ; PR.complete = canonicalGraphWordToBoundedSparse
      ; PR.polynomialVerification = verifierClock
      ; PR.polynomialCertificateSize = certificateBound
      }
