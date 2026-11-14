module DASHI.Analysis.BishopOriginalEtaRawAllCutoffPrefixExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP ETA: RAW 0,1,2,... PREFIX, NOT ONLY 2N PAIRS.
--
-- The actual term a_s(j) is indexed from j=0, representing (j+1)^-s.
-- Eta.originalEtaPrefix term n stores n PAIRS, hence 2*n raw terms.
-- This module defines the raw alternating term for ALL Nat indices
-- and proves:
--   rawPrefix(2n)   ~= originalEtaPrefix(n)
--   rawPrefix(2n+1) ~= originalEtaPrefix(n) + term(2n).
--
-- Proof is strictly finite original Bishop-complex setoid algebra
-- and Nat parity; the analytic bound for unmatched term and uniform
-- Cauchy convergence remain OPEN.
-- SOURCE-WRITTEN; pinned Agda 2.9 acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_,_)
import Data.Nat.Properties as NatP
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopOriginalEtaPairBlockTelescopingExact as Pair
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Recursion descends by two and advances the physical term source
-- by two; it never uses any arbitrary Nat parity oracle.
originalAlternatingRawTerm :
  (Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalAlternatingRawTerm term zero = term zero
originalAlternatingRawTerm term (suc zero) = BC.negC (term (suc zero))
originalAlternatingRawTerm term (suc (suc n)) =
  originalAlternatingRawTerm (λ j → term (suc (suc j))) n

originalRawEtaPrefix :
  (Nat → BC.BishopComplex) → Nat → BC.BishopComplex
originalRawEtaPrefix term =
  Eta.originalBishopPrefix (originalAlternatingRawTerm term)

twiceSucExact :
  (n : Nat) →
  Eta.twice (suc n) ≡ suc (suc (Eta.twice n))
twiceSucExact n rewrite NatP.+-suc n n = refl

originalEvenRawTerm :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  originalAlternatingRawTerm term (Eta.twice n)
    ≡ term (Eta.twice n)
originalEvenRawTerm term zero = refl
originalEvenRawTerm term (suc n)
  rewrite twiceSucExact n =
  originalEvenRawTerm (λ j → term (suc (suc j))) n

originalOddRawTerm :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  originalAlternatingRawTerm term (suc (Eta.twice n))
    ≡ BC.negC (term (suc (Eta.twice n)))
originalOddRawTerm term zero = refl
originalOddRawTerm term (suc n)
  rewrite twiceSucExact n =
  originalOddRawTerm (λ j → term (suc (suc j))) n

-- The raw even cutoff is the EXACT original eta pair prefix.
originalRawEvenPrefixEqualsSelectedPairs :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  Eta._≈C_
    (originalRawEtaPrefix term (Eta.twice n))
    (Eta.originalEtaPrefix term n)
originalRawEvenPrefixEqualsSelectedPairs term zero =
  RP.≃-refl , RP.≃-refl
originalRawEvenPrefixEqualsSelectedPairs term (suc n)
  rewrite twiceSucExact n
        | originalEvenRawTerm term n
        | originalOddRawTerm term n =
  Eta.≈C-trans
    (Eta.addRightCongruent
      (Eta.addRightCongruent
        (originalRawEvenPrefixEqualsSelectedPairs term n)
        (term (Eta.twice n)))
      (BC.negC (term (suc (Eta.twice n)))))
    (Pair.bishopComplexAddAssoc
      (Eta.originalEtaPrefix term n)
      (term (Eta.twice n))
      (BC.negC (term (suc (Eta.twice n)))))

-- The odd raw cutoff has one unmatched positive-index term.
-- This term MUST be paid for in the analytic uniform Cauchy proof.
originalRawOddPrefixEqualsSelectedPairsPlusOne :
  (term : Nat → BC.BishopComplex) (n : Nat) →
  Eta._≈C_
    (originalRawEtaPrefix term (suc (Eta.twice n)))
    (BC._+C_ (Eta.originalEtaPrefix term n)
      (term (Eta.twice n)))
originalRawOddPrefixEqualsSelectedPairsPlusOne term n
  rewrite originalEvenRawTerm term n =
  Eta.addRightCongruent
    (originalRawEvenPrefixEqualsSelectedPairs term n)
    (term (Eta.twice n))

-- For literal Round11:
--   Eta.OriginalRound11DirichletEta.sourceTerms inputs s
-- may be passed as term, without replacing the original Nat-log,
-- expC, or Bishop series carrier.
--
-- Analytic follow-up:
--   originalBishopRawOddUnmatchedTermUniformBound
--   originalRound11EtaAllRawCutoffsUniformCauchy
--   originalRound11EtaCompactUniformConvergence

-- Concrete original Round11 source instantiation: no replacement logNat
-- candidate, exponent, or Dirichlet term-family can be slipped in here.
module OriginalRound11 (inputs : Round11.Round11BishopCutset) where
  module Selected = Eta.OriginalRound11DirichletEta inputs

  actualOriginalRound11RawEvenPrefix :
    (s : BC.BishopComplex) (n : Nat) →
    Eta._≈C_
      (originalRawEtaPrefix (Selected.sourceTerms s) (Eta.twice n))
      (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
  actualOriginalRound11RawEvenPrefix s n =
    originalRawEvenPrefixEqualsSelectedPairs (Selected.sourceTerms s) n

  actualOriginalRound11RawOddPrefix :
    (s : BC.BishopComplex) (n : Nat) →
    Eta._≈C_
      (originalRawEtaPrefix
        (Selected.sourceTerms s) (suc (Eta.twice n)))
      (BC._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (Selected.sourceTerms s (Eta.twice n)))
  actualOriginalRound11RawOddPrefix s n =
    originalRawOddPrefixEqualsSelectedPairsPlusOne
      (Selected.sourceTerms s) n
