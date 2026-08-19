module DASHI.Moonshine.DuncanSwisherDeligneA1SharpnessExact where

------------------------------------------------------------------------
-- DELIGNE/DWORK/KOIKE AUTHORITY CUT AT THE n=1 COEFFICIENT
--
-- PRIMARY SOURCES
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026,
-- arXiv:2602.09135, DOI: 10.48550/arXiv.2602.09135,
-- Proposition 3.1 and equations (3.1)--(3.7).
--
-- Bernard Dwork, "$p$-adic cycles", Publ. Math. IHES 37 (1969),
-- DOI: 10.1007/BF02684886.
--
-- Masao Koike, "Congruences between modular forms and functions and
-- applications to the conjecture of Atkin", 1973,
-- repository DOI/identifier: 10.15083/00039793.
--
-- Holly Swisher, "A remark on Hecke operators and a theorem of Dwork and
-- Koike", Illinois J. Math. 48 (2004), DOI: 10.1215/ijm/1258136188.
--
-- SOURCE SHAPE
--
--   p J_1|U_p = - sum_alpha sum_{n>=1}
--                   A_n(alpha^) (J_1-alpha^)^{-n}.
--
-- The high-alpha formal boundary is not the whole p-adic analytic theory.
-- It is the sharp first-pole statement for A_1.  Once its valuation is tied to
-- the source's three automorphism types, the full-automorphism identity is a
-- theorem:
--
--   2 v_p(A_1(alpha^)) = |Aut(E_alpha)|.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.DuncanSwisherDelignePartialFractionMechanismExact as Partial

record DeligneA1SharpnessAuthority (Point : Set) : Set₁ where
  field
    automorphismType : Point → Deligne.SupersingularAutomorphismType
    a1PadicDepth : Point → Nat

    -- This is the exact n=1 sharpness boundary extracted from Proposition 3.1.
    a1Sharp :
      (x : Point) →
      a1PadicDepth x
      ≡ Deligne.deligneFirstPoleDepth (automorphismType x)

open DeligneA1SharpnessAuthority public

a1DepthDoublesToFullAutomorphismOrder :
  ∀ {Point : Set} →
  (A : DeligneA1SharpnessAuthority Point) →
  (x : Point) →
  2 * a1PadicDepth A x
  ≡ Deligne.fullAutomorphismOrder (automorphismType A x)
a1DepthDoublesToFullAutomorphismOrder A x =
  trans
    (cong (λ n → 2 * n) (a1Sharp A x))
    (Deligne.firstPoleDepthDoublesToFullAutomorphismOrder
      (automorphismType A x))

-- A pointwise equality of A1 depth with the selected minimum order is now
-- sufficient only when a genuine minimum-over-locus witness is supplied by the
-- prime-indexed minimum module.  This file intentionally does not manufacture
-- such a witness from a bare automorphism type.

a1DepthClassification :
  (t : Deligne.SupersingularAutomorphismType) → Nat
a1DepthClassification = Deligne.deligneFirstPoleDepth

jZeroA1DepthIsThree : a1DepthClassification Deligne.jZeroExceptional ≡ 3
jZeroA1DepthIsThree = refl

j1728A1DepthIsTwo : a1DepthClassification Deligne.j1728Exceptional ≡ 2
j1728A1DepthIsTwo = refl

genericA1DepthIsOne : a1DepthClassification Deligne.ordinaryType ≡ 1
genericA1DepthIsOne = refl

partialFractionMechanismPinned :
  Partial.dworkKoikePartialFractionShapePinned
    Partial.canonicalDuncanSwisherDelignePartialFractionBoundary ≡ true
partialFractionMechanismPinned = refl

partialFractionNumericReceiptsNotUsedAsProof :
  Partial.propositions32And33ImportedAsNumericReceipts
    Partial.canonicalDuncanSwisherDelignePartialFractionBoundary ≡ false
partialFractionNumericReceiptsNotUsedAsProof = refl

record DuncanSwisherDeligneA1SharpnessBoundary : Set where
  field
    partialFractionShapeReused : Bool
    a1SharpnessIsAuthorityCut : Bool
    twiceA1DepthEqualsFullAutDerived : Bool
    wholeDworkTheoryReformalized : Bool
    bareAutTypePromotedToMinimum : Bool
    lowPrimeTwoThreeIncluded : Bool

canonicalDuncanSwisherDeligneA1SharpnessBoundary :
  DuncanSwisherDeligneA1SharpnessBoundary
canonicalDuncanSwisherDeligneA1SharpnessBoundary = record
  { partialFractionShapeReused = true
  ; a1SharpnessIsAuthorityCut = true
  ; twiceA1DepthEqualsFullAutDerived = true
  ; wholeDworkTheoryReformalized = false
  ; bareAutTypePromotedToMinimum = false
  ; lowPrimeTwoThreeIncluded = false
  }
