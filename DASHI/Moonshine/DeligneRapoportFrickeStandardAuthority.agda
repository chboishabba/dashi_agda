module DASHI.Moonshine.DeligneRapoportFrickeStandardAuthority where

------------------------------------------------------------------------
-- STANDARD IMPORTED GEOMETRIC AUTHORITY
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schémas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
-- Integral modular-curve models and the bad-reduction geometry of X_0(p).
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
-- Recalls the Deligne--Rapoport/Ogg picture used here: modulo p, X_0(p)
-- consists of two rational components meeting at supersingular points;
-- w_p exchanges the two components, and the quotient special fibre has one
-- rational component with one self-node for each non-rational Frobenius pair.
--
-- Adel Betina and Emmanuel Lecouturier,
-- "On the p-adic periods of the modular curve X(Gamma_0(p) cap Gamma(2))",
-- Transactions of the AMS 371 (2019), 413--429.
-- DOI: 10.1090/tran/7236.
-- This is a MARKED/full-level-2 companion authority.  It is deliberately NOT
-- used to identify marked Frobenius pair counts with the coarse X_0^+(p)
-- genus: forgetting level structure can collapse Frobenius pairs.
--
-- AUTHORITY BOUNDARY
--
-- The theorem below is the ONE imported classical algebraic-geometry witness
-- in this lane.  It does not postulate the Ogg selector conclusion.  It only
-- supplies the source-facing object already required by
-- FrickeSpecialFibreFrobeniusFixedSelectorExact:
--
--   * the actual coarse supersingular Frobenius carrier;
--   * its fixed/two-cycle normal-form realization;
--   * the actual X_0(p)/w_p nodal special fibre;
--   * equality of its nodes with the same coarse quadratic Frobenius pairs;
--   * proper-flat arithmetic-genus preservation.
--
-- All consequences (pair defect = genus, all-fixed iff genus zero) remain
-- derived locally in DASHI.  No finite Ogg table and no Monster label occurs
-- in this authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.FrickeSpecialFibreFrobeniusFixedSelectorExact as Selector

postulate
  publishedCoarseFrickeFrobeniusGeometry :
    (p : Nat) → Prime p → 5 ≤ p → Selector.PrimeFrickeFrobeniusGeometry

record DeligneRapoportFrickeStandardAuthorityBoundary : Set where
  field
    deligneRapoportCoarseModelImported : Bool
    treneerFrickeQuotientDescriptionImported : Bool
    betinaLecouturierGamma2UsedOnlyAsMarkedCompanion : Bool
    finiteOggControlTableImported : Bool
    monsterLabelImported : Bool
    selectorConclusionPostulated : Bool

canonicalDeligneRapoportFrickeStandardAuthorityBoundary :
  DeligneRapoportFrickeStandardAuthorityBoundary
canonicalDeligneRapoportFrickeStandardAuthorityBoundary = record
  { deligneRapoportCoarseModelImported = true
  ; treneerFrickeQuotientDescriptionImported = true
  ; betinaLecouturierGamma2UsedOnlyAsMarkedCompanion = true
  ; finiteOggControlTableImported = false
  ; monsterLabelImported = false
  ; selectorConclusionPostulated = false
  }
