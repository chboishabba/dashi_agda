module DASHI.Moonshine.PrimeLevelDeligneRapoportStandardAuthority where

------------------------------------------------------------------------
-- STANDARD IMPORTED PRIME-LEVEL GEOMETRIC AUTHORITY
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schémas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- Robin Hartshorne,
-- "Algebraic Geometry", Graduate Texts in Mathematics 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
-- Proper flat families / Hilbert-polynomial constancy used for arithmetic-genus
-- transport.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "On the p-adic periods of the modular curve X(Gamma_0(p) cap Gamma(2))",
-- Transactions of the AMS 371 (2019), 413--429.
-- DOI: 10.1090/tran/7236.
-- Marked Gamma(2) companion geometry only; it is NOT substituted for the
-- coarse X_0(p)/w_p carrier in this authority.
--
-- AUTHORITY BOUNDARY
--
-- This module imports exactly the source-facing object required by
-- PrimeLevelDeligneRapoportFrickeSelectorExact.  In particular it does NOT
-- postulate
--
--   g(X_0^+(p)) = Frobenius-pair-count
--
-- or the all-fixed selector.  Those are derived downstream from:
--
--   * actual coarse supersingular Frobenius normal form;
--   * actual Fricke quotient special fibre;
--   * completed-local nodal same-object comparison at every derived node;
--   * proper-flat Hilbert-polynomial data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector

postulate
  publishedPrimeLevelFrickeAuthority :
    (p : Nat) → Prime p → 5 ≤ p → Selector.PrimeLevelFrickeSpecialFibreAuthority

record PrimeLevelDeligneRapoportStandardAuthorityBoundary : Set where
  field
    deligneRapoportIntegralModelImported : Bool
    treneerCoarseFrickeDescriptionImported : Bool
    completedLocalNodeAuthorityImported : Bool
    properFlatHilbertAuthorityImported : Bool
    gamma2MarkedCarrierSubstitutedForCoarseCarrier : Bool
    pairDefectEqualsGenusPostulated : Bool
    finiteOggTableImported : Bool
    monsterLabelImported : Bool

canonicalPrimeLevelDeligneRapoportStandardAuthorityBoundary :
  PrimeLevelDeligneRapoportStandardAuthorityBoundary
canonicalPrimeLevelDeligneRapoportStandardAuthorityBoundary = record
  { deligneRapoportIntegralModelImported = true
  ; treneerCoarseFrickeDescriptionImported = true
  ; completedLocalNodeAuthorityImported = true
  ; properFlatHilbertAuthorityImported = true
  ; gamma2MarkedCarrierSubstitutedForCoarseCarrier = false
  ; pairDefectEqualsGenusPostulated = false
  ; finiteOggTableImported = false
  ; monsterLabelImported = false
  }
