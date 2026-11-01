module DASHI.Mathematics.Complexity.Karp21HeterogeneousEncodingExact where

------------------------------------------------------------------------
-- SOURCE OWNERS: Cook (1971), Karp (1972), and
-- DASHI.Mathematics.Complexity.PolynomialReductionExact.
--
-- DASHI contribution:
-- Turn a concrete *heterogeneous* A→B semantic iff plus actual faithful
-- total word decoders/encoders and an explicit polynomial map certificate
-- into the repo's canonical PolynomialManyOneReduction on a shared Word.
--
-- IMPORTANT: the faithful-source obligation is over EVERY word and must
-- classify malformed source encodings as well. "decode" is intentionally
-- total and may carry an invalid-value constructor. Target faithfulness
-- is only needed on the image of encodeTarget; its off-image behavior is
-- governed by the independent target language's own parser.
-- No polynomial-clock witness is manufactured from pure semantic data.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

compileHeterogeneousKarpReduction :
  ∀ {Word Source Target : Set}
    {cost : PR.PolynomialCostModel Word}
    {sourceLanguage targetLanguage : PR.Language Word}
    (sourceAccepts : Source → Set)
    (targetAccepts : Target → Set)
    (decodeSource : Word → Source)
    (transform : Source → Target)
    (encodeTarget : Target → Word) →
  ((word : Word) →
    PR.Iff
      (PR.accepts sourceLanguage word)
      (sourceAccepts (decodeSource word))) →
  ((instance : Source) →
    PR.Iff
      (sourceAccepts instance)
      (targetAccepts (transform instance))) →
  ((instance : Target) →
    PR.Iff
      (targetAccepts instance)
      (PR.accepts targetLanguage (encodeTarget instance))) →
  PR.polynomialTimeMap cost
    (λ word → encodeTarget (transform (decodeSource word))) →
  PR.PolynomialManyOneReduction cost sourceLanguage targetLanguage
compileHeterogeneousKarpReduction
  sourceAccepts targetAccepts decodeSource transform encodeTarget
  sourceFaithful targetIff outputFaithful polynomialWordMap =
  record
    { PR.reduce =
        λ word → encodeTarget (transform (decodeSource word))
    ; PR.preservesLanguage = λ word →
        PR.iffTransitive
          (sourceFaithful word)
          (PR.iffTransitive
            (targetIff (decodeSource word))
            (outputFaithful (transform (decodeSource word))))
    ; PR.polynomialReduction = polynomialWordMap
    }
