module DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Pierre Deligne and Michael Rapoport,
-- "Les schemas de modules de courbes elliptiques",
-- Lecture Notes in Mathematics 349 (1973), 143--316.
-- DOI: 10.1007/978-3-540-37855-6_4.
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
-- Chapter III, Section 9: flat families / Hilbert polynomial constancy;
-- arithmetic genus is constant in the relevant proper flat curve family.
--
-- DASHI CONTRIBUTION
--
-- The preceding module has already derived the complete FINITE combinatorics
-- of the Fricke quotient from the actual supersingular Frobenius involution:
-- one rational dual-graph vertex and one loop edge for every nonfixed
-- Frobenius pair.  Therefore arithmetic genus = pair count is no longer a
-- source premise.
--
-- The genuinely geometric same-object authority is now exactly:
--
--   1. construct the actual special fibre of the proper integral model of
--      X_0^+(p);
--   2. identify its nodal dual-graph/genus data with the canonical quotient
--      data derived from supersingular Frobenius;
--   3. transport arithmetic genus from that special fibre to the generic
--      Fricke curve by proper flatness.
--
-- Once those two proof-relevant equalities are supplied, the global selector
-- theorem is pure composition:
--
--   g(X_0^+(p)) = d_F(p).
--
-- No Fricke/class-number control table is consumed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

record PrimeLevelFrickeSpecialFibreAuthority : Set₁ where
  field
    supersingularFrobenius : DR.PrimeLevelSupersingularFrobeniusData

    -- Arithmetic genus of the smooth generic Fricke curve X_0^+(p).
    genericFrickeGenus : Nat

    -- Actual source-native special-fibre nodal data obtained from the proper
    -- integral modular-curve model / Fricke quotient.
    actualSpecialFibre : Nodal.NodalDualGraphGenusData

    -- SAME-OBJECT theorem: the actual quotient special fibre has precisely the
    -- quotient combinatorics derived from supersingular Frobenius above.
    deligneRapoportFrickeSameObject :
      actualSpecialFibre
      ≡ DR.canonicalFrickeQuotientDualGraph supersingularFrobenius

    -- Proper-flat arithmetic-genus transport from generic to special fibre.
    properFlatGenusTransport :
      genericFrickeGenus ≡ Nodal.arithmeticGenus actualSpecialFibre

open PrimeLevelFrickeSpecialFibreAuthority public

------------------------------------------------------------------------
-- Global geometric selector theorem.
------------------------------------------------------------------------

genericFrickeGenusEqualsSpectrumPairCount :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  genericFrickeGenus A
  ≡ Orbit.pairedOrbitCount
      (DR.spectrum (supersingularFrobenius A))
genericFrickeGenusEqualsSpectrumPairCount A =
  trans
    (properFlatGenusTransport A)
    (trans
      (cong Nodal.arithmeticGenus
        (deligneRapoportFrickeSameObject A))
      (DR.canonicalFrickeArithmeticGenusEqualsPaired
        (supersingularFrobenius A)))

genericFrickeGenusEqualsDeclaredPairDefect :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  genericFrickeGenus A
  ≡ DR.pairedCount (supersingularFrobenius A)
genericFrickeGenusEqualsDeclaredPairDefect A =
  trans
    (genericFrickeGenusEqualsSpectrumPairCount A)
    (DR.spectrumPaired (supersingularFrobenius A))

zeroGenusIffZeroPairDefect :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  genericFrickeGenus A ≡ 0
  ↔ DR.pairedCount (supersingularFrobenius A) ≡ 0
zeroGenusIffZeroPairDefect A =
  (λ genusZero →
    trans (sym (genericFrickeGenusEqualsDeclaredPairDefect A)) genusZero)
  ,
  (λ pairZero →
    trans (genericFrickeGenusEqualsDeclaredPairDefect A) pairZero)

------------------------------------------------------------------------
-- Adapter to the older selector interface.  Notice that nodesAreQuadraticPairs
-- and arithmetic genus = nodes are no longer independent authority premises:
-- they come from the derived canonical quotient graph.
------------------------------------------------------------------------

import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Older

asOlderSpecialFibreRealization :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  Older.PrimeFrickeSpecialFibreRealization
asOlderSpecialFibreRealization A = record
  { Older.prime = DR.prime (supersingularFrobenius A)
  ; Older.frobeniusPairDefect = DR.pairedCount (supersingularFrobenius A)
  ; Older.genericFrickeGenus = genericFrickeGenus A
  ; Older.specialFibre = actualSpecialFibre A
  ; Older.nodesAreQuadraticPairs =
      trans
        (cong Nodal.nodeCount (deligneRapoportFrickeSameObject A))
        (DR.spectrumPaired (supersingularFrobenius A))
  ; Older.flatGenusPreservation = properFlatGenusTransport A
  }

olderSelectorRecovered :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  Older.genericFrickeGenus (asOlderSpecialFibreRealization A)
  ≡ Older.frobeniusPairDefect (asOlderSpecialFibreRealization A)
olderSelectorRecovered A =
  Older.frickeGenusEqualsFrobeniusPairDefect
    (asOlderSpecialFibreRealization A)

record PrimeLevelDeligneRapoportFrickeSelectorBoundary : Set where
  field
    finitePairedOrbitQuotientDerived : Bool
    canonicalNodalDualGraphDerived : Bool
    arithmeticGenusEqualsPairCountDerived : Bool
    sameObjectSpecialFibreEqualityRequired : Bool
    properFlatGenusTransportRequired : Bool
    finiteFrickeTableUsed : Bool
    arbitraryPrimeAuthorityConstructedHere : Bool

canonicalPrimeLevelDeligneRapoportFrickeSelectorBoundary :
  PrimeLevelDeligneRapoportFrickeSelectorBoundary
canonicalPrimeLevelDeligneRapoportFrickeSelectorBoundary = record
  { finitePairedOrbitQuotientDerived = true
  ; canonicalNodalDualGraphDerived = true
  ; arithmeticGenusEqualsPairCountDerived = true
  ; sameObjectSpecialFibreEqualityRequired = true
  ; properFlatGenusTransportRequired = true
  ; finiteFrickeTableUsed = false
  ; arbitraryPrimeAuthorityConstructedHere = false
  }
