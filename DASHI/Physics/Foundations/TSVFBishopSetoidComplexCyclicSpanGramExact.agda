module DASHI.Physics.Foundations.TSVFBishopSetoidComplexCyclicSpanGramExact where

------------------------------------------------------------------------
-- HIL07/HIL08, constructive Bishop complex:
-- EVERY FINITE SESQUILINEAR CYCLIC SPAN GRAM IS PRESERVED.
--
-- Uses the *actual* Bishop complex carrier and componentwise setoid
-- equality from BishopSetoidComplexExact, not the axiomatic real
-- RealAnalysisAxioms.ℝ or propositional equality on Bishop reals.
--
-- Given original/independent OS all-word pair equivalence, compute
-- the finite Gram of arbitrary complex-weighted cyclic vectors:
--  Σ_i Σ_j conj(a_i) b_j <w_i,w_j>.
--
-- Only finite induction and the genuine Bishop setoid congruences
-- are used. Completeness, positivity, physically selected observer
-- M1/M2, OS cyclic density, and the infinite Cauchy product are NOT
-- supplied by a finite equality theorem.
--
-- Scientific sources: Errett Bishop & Douglas Bridges (1985),
-- Zachary Murray (2022), vendored Csimma/Bishop continuation;
-- DASHI original BishopSetoidComplexExact owner.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import DASHI.Analysis.BishopSetoidComplexExact as C

module _
    {ObserverWord OSWord : Set}
    (observerWordGram : ObserverWord → ObserverWord → C.BishopComplex)
    (osWordGram : OSWord → OSWord → C.BishopComplex)
    (mapOriginalWordToOS : ObserverWord → OSWord)
    (allOriginalWordGramsAgree :
      ∀ x y →
      C._≈C_ (observerWordGram x y)
        (osWordGram (mapOriginalWordToOS x)
          (mapOriginalWordToOS y)))
  where

  OriginalFiniteComplexSpan : Set
  OriginalFiniteComplexSpan = List (C.BishopComplex × ObserverWord)

  OSFiniteComplexSpan : Set
  OSFiniteComplexSpan = List (C.BishopComplex × OSWord)

  mapOriginalComplexSpan : OriginalFiniteComplexSpan → OSFiniteComplexSpan
  mapOriginalComplexSpan [] = []
  mapOriginalComplexSpan ((weight , word) ∷ tail) =
    (weight , mapOriginalWordToOS word) ∷ mapOriginalComplexSpan tail

  observerComplexRow :
    C.BishopComplex × ObserverWord →
    OriginalFiniteComplexSpan → C.BishopComplex
  observerComplexRow left [] = C.zeroC
  observerComplexRow (a , x) ((b , y) ∷ tail) =
    C._+C_
      (C._*C_ (C._*C_ (C.conjugate a) b)
        (observerWordGram x y))
      (observerComplexRow (a , x) tail)

  osComplexRow :
    C.BishopComplex × OSWord →
    OSFiniteComplexSpan → C.BishopComplex
  osComplexRow left [] = C.zeroC
  osComplexRow (a , x) ((b , y) ∷ tail) =
    C._+C_
      (C._*C_ (C._*C_ (C.conjugate a) b)
        (osWordGram x y))
      (osComplexRow (a , x) tail)

  observerComplexSpanGram :
    OriginalFiniteComplexSpan → OriginalFiniteComplexSpan →
    C.BishopComplex
  observerComplexSpanGram [] right = C.zeroC
  observerComplexSpanGram (left ∷ rest) right =
    C._+C_ (observerComplexRow left right)
      (observerComplexSpanGram rest right)

  osComplexSpanGram :
    OSFiniteComplexSpan → OSFiniteComplexSpan →
    C.BishopComplex
  osComplexSpanGram [] right = C.zeroC
  osComplexSpanGram (left ∷ rest) right =
    C._+C_ (osComplexRow left right)
      (osComplexSpanGram rest right)

  -- Uses the actual setoid not a fake all-word propositional equality.
  originalBishopComplexRowGramTransport :
    (left : C.BishopComplex × ObserverWord)
    (right : OriginalFiniteComplexSpan) →
    C._≈C_
      (observerComplexRow left right)
      (osComplexRow
        (proj₁ left , mapOriginalWordToOS (proj₂ left))
        (mapOriginalComplexSpan right))
  originalBishopComplexRowGramTransport left [] =
    C.≈C-refl C.zeroC
  originalBishopComplexRowGramTransport
      (a , x) ((b , y) ∷ tail) =
    C.addCongruent
      (C.mulCongruent
        (C.≈C-refl (C._*C_ (C.conjugate a) b))
        (allOriginalWordGramsAgree x y))
      (originalBishopComplexRowGramTransport
        (a , x) tail)

  -- Fully constructive 2D induction on arbitrary finite ordered
  -- original/OS cyclic combinations. This is the complex analogue
  -- of the real finite-span Gram compiler, now on native Bishop.
  originalAllBishopComplexFiniteSpanGramsAgree :
    (left right : OriginalFiniteComplexSpan) →
    C._≈C_
      (observerComplexSpanGram left right)
      (osComplexSpanGram
        (mapOriginalComplexSpan left)
        (mapOriginalComplexSpan right))
  originalAllBishopComplexFiniteSpanGramsAgree [] right =
    C.≈C-refl C.zeroC
  originalAllBishopComplexFiniteSpanGramsAgree (left ∷ rest) right =
    C.addCongruent
      (originalBishopComplexRowGramTransport left right)
      (originalAllBishopComplexFiniteSpanGramsAgree rest right)

  originalAllBishopComplexDiagonalGramsAgree :
    (span : OriginalFiniteComplexSpan) →
    C._≈C_
      (observerComplexSpanGram span span)
      (osComplexSpanGram
        (mapOriginalComplexSpan span)
        (mapOriginalComplexSpan span))
  originalAllBishopComplexDiagonalGramsAgree span =
    originalAllBishopComplexFiniteSpanGramsAgree span span

  -- Equality against every finite original test transports to
  -- every test in the native OS image, and conversely. Completeness
  -- and independent OS *onto* density remain separate.
  OriginalSpanEquivalent :
    OriginalFiniteComplexSpan → OriginalFiniteComplexSpan → Set
  OriginalSpanEquivalent x y =
    (test : OriginalFiniteComplexSpan) →
    C._≈C_ (observerComplexSpanGram x test)
      (observerComplexSpanGram y test)

  OSImageSpanEquivalent :
    OriginalFiniteComplexSpan → OriginalFiniteComplexSpan → Set
  OSImageSpanEquivalent x y =
    (test : OriginalFiniteComplexSpan) →
    C._≈C_
      (osComplexSpanGram
        (mapOriginalComplexSpan x)
        (mapOriginalComplexSpan test))
      (osComplexSpanGram
        (mapOriginalComplexSpan y)
        (mapOriginalComplexSpan test))

  originalBishopComplexSpanIndistinguishabilityForward :
    ∀ x y →
    OriginalSpanEquivalent x y →
    OSImageSpanEquivalent x y
  originalBishopComplexSpanIndistinguishabilityForward x y eq test =
    C.≈C-trans
      (C.≈C-sym (originalAllBishopComplexFiniteSpanGramsAgree x test))
      (C.≈C-trans
        (eq test)
        (originalAllBishopComplexFiniteSpanGramsAgree y test))

  originalBishopComplexSpanIndistinguishabilityBackward :
    ∀ x y →
    OSImageSpanEquivalent x y →
    OriginalSpanEquivalent x y
  originalBishopComplexSpanIndistinguishabilityBackward x y eq test =
    C.≈C-trans
      (originalAllBishopComplexFiniteSpanGramsAgree x test)
      (C.≈C-trans
        (eq test)
        (C.≈C-sym (originalAllBishopComplexFiniteSpanGramsAgree y test)))

-- HIL07: actual original TSVF->YM complex all-word matching still needs
-- a source-derived physical complex cyclic Gram equality; a calibrated
-- real-part-only Wilson expectation does not provide it. HIL08: no
-- infinite complex GNS completion or independently onto unitary here.
-- K05: this proves the finite Bishop complex sum/congruence analogue;
-- it does not identify infinite signed-factorial convolution limits.
