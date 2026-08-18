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
-- The finite combinatorics of the Fricke quotient is already derived from the
-- SAME supersingular Frobenius involution.  For every derived node the source
-- authority must additionally provide the completed-local normalization
-- comparison, so cardinality/branch counting cannot manufacture nodality.
--
-- Proper-flat genus transport is no longer stored as an opaque genus equality.
-- It is derived from a common Hilbert-polynomial carrier and the flat-family
-- equality of the generic and special Hilbert polynomials.
--
-- Therefore the genuinely geometric authority is now:
--
--   1. actual quotient special fibre = canonical Frobenius-pair nodal model;
--   2. completed local-node same-object comparison at every loop;
--   3. proper-flat Hilbert-polynomial constancy, with both fibre genera
--      identified as the arithmetic genus interpretation of that polynomial.
--
-- Everything downstream, including
--
--   g(X_0^+(p)) = d_F(p)
--
-- and pointwise Frobenius fixed iff genus zero, is derived without the finite
-- Fricke/Ogg control table.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.AlgebraicGeometry.ProperFlatHilbertGenusTransportExact as Flat
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR
import DASHI.Moonshine.DeligneRapoportCompletedLocalNodeAuthorityExact as LocalNode
import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Older
import DASHI.Moonshine.FrickeSpecialFibreFrobeniusFixedSelectorExact as Fixed

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

    -- Local scheme authority at EVERY derived nonfixed Frobenius pair.
    completedLocalNode :
      Fin (Orbit.pairedOrbitCount (DR.spectrum supersingularFrobenius)) →
      LocalNode.CompletedLocalNodeAuthority

    -- Source-native flat-family/Hilbert-polynomial data.  Genus transport will
    -- be derived from this object rather than accepted independently.
    flatHilbertGenusData : Flat.ProperFlatHilbertGenusData

    flatGenericGenusIsFrickeGenus :
      Flat.genericGenus flatHilbertGenusData ≡ genericFrickeGenus

    flatSpecialGenusIsActualSpecialFibre :
      Flat.specialArithmeticGenus flatHilbertGenusData
      ≡ Nodal.arithmeticGenus actualSpecialFibre

open PrimeLevelFrickeSpecialFibreAuthority public

------------------------------------------------------------------------
-- Every canonical quotient node now carries explicit completed-local authority.
------------------------------------------------------------------------

completedLocalAuthorityAt :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  Fin (Orbit.pairedOrbitCount (DR.spectrum (supersingularFrobenius A))) →
  LocalNode.CompletedLocalNodeAuthority
completedLocalAuthorityAt = completedLocalNode

------------------------------------------------------------------------
-- Derive the former proper-flat genus equality from Hilbert-polynomial
-- constancy.  This theorem is the only surface consumed by older adapters.
------------------------------------------------------------------------

properFlatGenusTransport :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  genericFrickeGenus A ≡ Nodal.arithmeticGenus (actualSpecialFibre A)
properFlatGenusTransport A =
  trans
    (sym (flatGenericGenusIsFrickeGenus A))
    (trans
      (Flat.properFlatGenusTransport (flatHilbertGenusData A))
      (flatSpecialGenusIsActualSpecialFibre A))

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
-- Adapter to the older special-fibre selector interface.  Node/pair count and
-- genus transport are both theorem-derived here.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Stronger adapter: consume the existing pointwise-fixed selector without an
-- independent pairCountSameObject authority.  Both sides use the same spectrum.
------------------------------------------------------------------------

asFixedSelectorGeometry :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  Fixed.PrimeFrickeFrobeniusGeometry
asFixedSelectorGeometry A = record
  { Fixed.Carrier = DR.Supersingular (supersingularFrobenius A)
  ; Fixed.frobenius = DR.frobenius (supersingularFrobenius A)
  ; Fixed.spectrum = DR.spectrum (supersingularFrobenius A)
  ; Fixed.frobeniusRealization = DR.normalForm (supersingularFrobenius A)
  ; Fixed.specialFibreRealization = asOlderSpecialFibreRealization A
  ; Fixed.pairCountSameObject = DR.spectrumPaired (supersingularFrobenius A)
  }

GeometricallyFullyFixed : PrimeLevelFrickeSpecialFibreAuthority → Set
GeometricallyFullyFixed A =
  Fixed.GeometricallyFullyFixed (asFixedSelectorGeometry A)

frobeniusFullyFixedIffGenericFrickeGenusZero :
  (A : PrimeLevelFrickeSpecialFibreAuthority) →
  GeometricallyFullyFixed A ↔ genericFrickeGenus A ≡ 0
frobeniusFullyFixedIffGenericFrickeGenusZero A =
  Fixed.frobeniusFullyFixedIffFrickeGenusZero
    (asFixedSelectorGeometry A)

record PrimeLevelDeligneRapoportFrickeSelectorBoundary : Set where
  field
    finitePairedOrbitQuotientDerived : Bool
    canonicalNodalDualGraphDerived : Bool
    arithmeticGenusEqualsPairCountDerived : Bool
    duplicatePairCountAuthorityEliminated : Bool
    completedLocalAuthorityRequiredPerNode : Bool
    branchCountAloneSufficient : Bool
    flatHilbertPolynomialConstancyRequired : Bool
    directGenusEqualityAcceptedAsPrimitive : Bool
    fixedIffGenusZeroRecovered : Bool
    sameObjectSpecialFibreEqualityRequired : Bool
    finiteFrickeTableUsed : Bool
    arbitraryPrimeAuthorityConstructedHere : Bool

canonicalPrimeLevelDeligneRapoportFrickeSelectorBoundary :
  PrimeLevelDeligneRapoportFrickeSelectorBoundary
canonicalPrimeLevelDeligneRapoportFrickeSelectorBoundary = record
  { finitePairedOrbitQuotientDerived = true
  ; canonicalNodalDualGraphDerived = true
  ; arithmeticGenusEqualsPairCountDerived = true
  ; duplicatePairCountAuthorityEliminated = true
  ; completedLocalAuthorityRequiredPerNode = true
  ; branchCountAloneSufficient = false
  ; flatHilbertPolynomialConstancyRequired = true
  ; directGenusEqualityAcceptedAsPrimitive = false
  ; fixedIffGenusZeroRecovered = true
  ; sameObjectSpecialFibreEqualityRequired = true
  ; finiteFrickeTableUsed = false
  ; arbitraryPrimeAuthorityConstructedHere = false
  }
