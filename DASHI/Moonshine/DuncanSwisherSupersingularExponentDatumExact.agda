module DASHI.Moonshine.DuncanSwisherSupersingularExponentDatumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Duncan--Swisher Theorem 1.2 states, for prime p > 3,
--
--   v_p(|M|) = 3/2 m_p   if |S_p^1| = 1 and |S_p^2| = 0,
--              1/2 m_p   if |S_p^1| > 1 and |S_p^2| = 0,
--              0         if |S_p^2| > 0,
--
-- where S_p^1 is the set of F_p-rational supersingular j-invariants,
-- S_p^2 is the set of supersingular j-invariants defined over F_{p^2} but
-- not F_p, and
--
--   m_p = min { # Aut(E) : E supersingular in characteristic p }.
--
-- IMPORTANT NORMALIZATION
-- m_p is the FULL elliptic-curve automorphism-group order.  It is not the
-- reduced Brandt stabilizer #Aut(E)/{+/-1}, and it is not the reciprocal
-- stack-unweighting sheet multiplicity.
--
-- DASHI CONTRIBUTION
--
-- Encode the theorem's geometric input with proof-relevant regime evidence and
-- use the denominator-cleared law
--
--   2 v_p(|M|) = 3 m_p, m_p, or 0.
--
-- This avoids introducing rationals into the finite theorem surface and makes
-- the convention bridge to the existing Brandt/stabilizer lane explicit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- Exact source regimes.
------------------------------------------------------------------------

data SupersingularExponentRegime : Set where
  singletonRationalNoQuadratic : SupersingularExponentRegime
  multipleRationalNoQuadratic  : SupersingularExponentRegime
  quadraticLocusPresent         : SupersingularExponentRegime

data RegimeEvidence
    (rationalCount quadraticCount : Nat) :
    SupersingularExponentRegime → Set where
  singletonEvidence :
    rationalCount ≡ 1 →
    quadraticCount ≡ 0 →
    RegimeEvidence rationalCount quadraticCount singletonRationalNoQuadratic

  multipleEvidence :
    2 ≤ rationalCount →
    quadraticCount ≡ 0 →
    RegimeEvidence rationalCount quadraticCount multipleRationalNoQuadratic

  quadraticEvidence :
    1 ≤ quadraticCount →
    RegimeEvidence rationalCount quadraticCount quadraticLocusPresent

record SupersingularExponentGeometry : Set where
  constructor supersingular-exponent-geometry
  field
    characteristic : Nat
    rationalSupersingularCount : Nat
    quadraticSupersingularCount : Nat
    minFullAutomorphismOrder : Nat
    regime : SupersingularExponentRegime
    regimeEvidence :
      RegimeEvidence rationalSupersingularCount quadraticSupersingularCount regime

open SupersingularExponentGeometry public

------------------------------------------------------------------------
-- Division-free geometric right-hand side of Duncan--Swisher Theorem 1.2.
------------------------------------------------------------------------

doubledGeometricExponent : SupersingularExponentGeometry → Nat
doubledGeometricExponent G with regime G
... | singletonRationalNoQuadratic = 3 * minFullAutomorphismOrder G
... | multipleRationalNoQuadratic  = minFullAutomorphismOrder G
... | quadraticLocusPresent         = 0

record DuncanSwisherExponentLaw
    (G : SupersingularExponentGeometry)
    (monsterExponent : Nat) : Set where
  field
    characteristicGreaterThanThree : 4 ≤ characteristic G
    doubledExponentExact :
      2 * monsterExponent ≡ doubledGeometricExponent G

open DuncanSwisherExponentLaw public

------------------------------------------------------------------------
-- Useful regime consequences.  These are local finite consequences, not new
-- arithmetic-geometry claims.
------------------------------------------------------------------------

quadraticRegimeForcesDoubledExponentZero :
  (G : SupersingularExponentGeometry) →
  regime G ≡ quadraticLocusPresent →
  doubledGeometricExponent G ≡ 0
quadraticRegimeForcesDoubledExponentZero G refl = refl

singletonRegimeUsesTripleFullAutOrder :
  (G : SupersingularExponentGeometry) →
  regime G ≡ singletonRationalNoQuadratic →
  doubledGeometricExponent G ≡ 3 * minFullAutomorphismOrder G
singletonRegimeUsesTripleFullAutOrder G refl = refl

multipleRegimeUsesFullAutOrder :
  (G : SupersingularExponentGeometry) →
  regime G ≡ multipleRationalNoQuadratic →
  doubledGeometricExponent G ≡ minFullAutomorphismOrder G
multipleRegimeUsesFullAutOrder G refl = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record DuncanSwisherSupersingularExponentDatumBoundary : Set where
  field
    theoremRestrictedToPrimesAboveThree : Bool
    fullAutomorphismOrderConventionRetained : Bool
    reducedBrandtWeightIdentifiedWithMp : Bool
    reciprocalSheetMultiplicityIdentifiedWithMp : Bool
    denominatorClearedThreeRegimeFormulaConstructed : Bool

canonicalDuncanSwisherSupersingularExponentDatumBoundary :
  DuncanSwisherSupersingularExponentDatumBoundary
canonicalDuncanSwisherSupersingularExponentDatumBoundary = record
  { theoremRestrictedToPrimesAboveThree = true
  ; fullAutomorphismOrderConventionRetained = true
  ; reducedBrandtWeightIdentifiedWithMp = false
  ; reciprocalSheetMultiplicityIdentifiedWithMp = false
  ; denominatorClearedThreeRegimeFormulaConstructed = true
  }
