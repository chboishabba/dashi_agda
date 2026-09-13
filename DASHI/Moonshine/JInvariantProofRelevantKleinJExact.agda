module DASHI.Moonshine.JInvariantProofRelevantKleinJExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT KLEIN-j CONSTRUCTION
--
-- The older KleinJAlgebra intentionally captured only the construction shape
--     J = g2^3 / Delta
-- but its quotient field is total.  That is too weak for a literal
-- constructive-complex instantiation, where division requires evidence that
-- the denominator is nonzero.
--
-- This owner refines exactly that seam.  It does not replace the older owner;
-- a totalization adapter is provided only when an explicit total quotient and
-- agreement receipt are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Legacy

record ProofRelevantKleinJAlgebra : Set₁ where
  constructor proof-relevant-klein-j-algebra
  field
    Point : Set
    Value : Set
    g2 : Point → Value
    delta : Point → Value
    cube : Value → Value

    Nonzero : Value → Set
    deltaNonzero : (z : Point) → Nonzero (delta z)
    quotient : (numerator denominator : Value) → Nonzero denominator → Value

open ProofRelevantKleinJAlgebra public

KleinJ :
  (A : ProofRelevantKleinJAlgebra) →
  Point A →
  Value A
KleinJ A z =
  quotient A
    (cube A (g2 A z))
    (delta A z)
    (deltaNonzero A z)

------------------------------------------------------------------------
-- Forgetting proof relevance is NOT free.  To recover the old total algebra,
-- the caller must explicitly supply a total quotient together with agreement
-- on every denominator that is known nonzero.
------------------------------------------------------------------------

record TotalQuotientExtension (A : ProofRelevantKleinJAlgebra) : Set₁ where
  constructor total-quotient-extension
  field
    totalQuotient : Value A → Value A → Value A
    agreesWhenNonzero :
      (numerator denominator : Value A) →
      (nz : Nonzero A denominator) →
      totalQuotient numerator denominator
      ≡ quotient A numerator denominator nz

open TotalQuotientExtension public

toLegacyAlgebra :
  (A : ProofRelevantKleinJAlgebra) →
  TotalQuotientExtension A →
  Legacy.KleinJAlgebra
toLegacyAlgebra A extension =
  Legacy.klein-j-algebra
    (Point A)
    (Value A)
    (g2 A)
    (delta A)
    (cube A)
    (totalQuotient extension)

legacyKleinJAgreesOnConstructedPoint :
  (A : ProofRelevantKleinJAlgebra) →
  (extension : TotalQuotientExtension A) →
  (z : Point A) →
  Legacy.KleinJ (toLegacyAlgebra A extension) z ≡ KleinJ A z
legacyKleinJAgreesOnConstructedPoint A extension z =
  agreesWhenNonzero extension
    (cube A (g2 A z))
    (delta A z)
    (deltaNonzero A z)

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ProofRelevantKleinJBoundary : Set where
  constructor proof-relevant-klein-j-boundary
  field
    discriminantNonzeroEvidenceIsExplicit : Bool
    constructiveDivisionCanConsumeEvidence : Bool
    legacyTotalQuotientRecoveredAutomatically : Bool
    arbitraryDivisionByZeroPermitted : Bool
    analyticDeltaNonvanishingAlreadyProvedHere : Bool

canonicalProofRelevantKleinJBoundary : ProofRelevantKleinJBoundary
canonicalProofRelevantKleinJBoundary =
  proof-relevant-klein-j-boundary true true false false false
