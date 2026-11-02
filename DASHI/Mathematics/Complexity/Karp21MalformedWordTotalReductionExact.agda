module DASHI.Mathematics.Complexity.Karp21MalformedWordTotalReductionExact where

------------------------------------------------------------------------
-- SHARED K00 REUSABLE PROOF: malformed SOURCE words must not be left
-- outside a many-one reduction's domain. The reduction is TOTAL over
-- every Word, not just parseable source instances.
--
-- For a total decoder Word → Maybe Source, reject the invalid source
-- branch with a proof that its source language is empty, then map it
-- to a concrete target NO instance with a target-NO proof.
-- For every valid source, reuse its *actual* instance reduction iff.
-- Both branches finish in the target's own faithful Word encoding.
--
-- This is a general mathematical *totalization theorem*. The encoded
-- map's polynomial machine time remains an explicit parameter. Unlike
-- a ghost constructor or evidence-flag, the malformed branch contains
-- a real negation proof and the word reduction is executable.
--
-- Historical root: Cook (1971), Karp (1972). Source-specific E20
-- fixed-NO target in scripts/karp21_signed_cut_binary_codec.py.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Empty using (⊥; ⊥-elim)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

module TotalMalformedSource
  {Word Source Target : Set}
  (decodeSource : Word → Maybe Source)
  (sourceAccepts : Source → Set)
  (targetAccepts : Target → Set)
  (transform : Source → Target)
  (targetNo : Target)
  (targetNoProof : targetAccepts targetNo → ⊥)
  (encodeTarget : Target → Word)
  (targetLanguage : PR.Language Word)
  (instanceCorrect :
    ∀ instance →
      PR.Iff (sourceAccepts instance)
             (targetAccepts (transform instance)))
  (targetWordFaithful :
    ∀ target →
      PR.Iff (targetAccepts target)
        (PR.accepts targetLanguage (encodeTarget target)))
  where

  -- No artificial ACCEPT predicate on malformed source encodings.
  SourceWordAccepts : Word → Set
  SourceWordAccepts word with decodeSource word
  ... | nothing = ⊥
  ... | just instance = sourceAccepts instance

  sourceLanguage : PR.Language Word
  sourceLanguage = record
    { PR.accepts = SourceWordAccepts }

  -- Explicit total reduction: neither branch reads a guessed witness.
  totalReduce : Word → Word
  totalReduce word with decodeSource word
  ... | nothing = encodeTarget targetNo
  ... | just instance = encodeTarget (transform instance)

  -- For an actual target language the independent target parser must
  -- establish the faithful word iff for ALL target encodings.


  totalMalformedReductionIff :
    (word : Word) →
    PR.Iff
      (PR.accepts sourceLanguage word)
      (PR.accepts targetLanguage (totalReduce word))
  totalMalformedReductionIff word with decodeSource word
  ... | nothing =
    PR.iff
      (λ ())
      (λ encodedProof →
        ⊥-elim
          (targetNoProof
            (PR.backward
              (targetWordFaithful targetNo) encodedProof)))
  ... | just instance =
    PR.iffTransitive
      (instanceCorrect instance)
      (targetWordFaithful (transform instance))

  -- Only the independent polynomial-time map proof can fill the
  -- resource certificate; this theorem does NOT manufacture one.
  makeCostedTotalReduction :
    (cost : PR.PolynomialCostModel Word) →
    PR.polynomialTimeMap cost totalReduce →
    PR.PolynomialManyOneReduction
      cost sourceLanguage targetLanguage
  makeCostedTotalReduction cost clock = record
    { PR.reduce = totalReduce
    ; PR.preservesLanguage = totalMalformedReductionIff
    ; PR.polynomialReduction = clock
    }
