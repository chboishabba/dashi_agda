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
-- SAME supersingular Frobenius involution: one rational dual-graph vertex and
-- one loop edge for every nonfixed pair.  Arithmetic genus = pair count is
-- therefore no longer a source premise.
--
-- The geometric authority required here is deliberately stronger than a graph
-- count.  For EVERY derived loop/node it must additionally provide the actual
-- completed-local-node comparison to the two-branch normalization pullback.
-- Thus the global special-fibre equality cannot be discharged from cardinality
-- or from an abstract two-branch label alone.
--
-- Remaining source-facing equalities:
--
--   1. actual quotient special fibre = canonical nodal model derived from
--      supersingular Frobenius;
--   2. each canonical node has the source-native completed-local-node model;
--   3. generic Fricke genus = arithmetic genus of the proper-flat special
--      fibre.
--
-- Once supplied, g(X_0^+(p)) = d_F(p) is pure composition, and the older
-- pointwise-fixed selector is recovered without an independent pair-count
-- alignment premise.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
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

    -- Local scheme authority at EVERY derived nonfixed Frobenius pair.  The
    -- index is the same canonical loop/node index used by the quotient graph.
    completedLocalNode :
      Fin (Orbit.pairedOrbitCount (DR.spectrum supersingularFrobenius)) →
      LocalNode.CompletedLocalNodeAuthority

    -- Proper-flat arithmetic-genus transport from generic to special fibre.
    properFlatGenusTransport :
      genericFrickeGenus ≡ Nodal.arithmeticGenus actualSpecialFibre

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
-- arithmetic genus are no longer independent authority premises.
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
    fixedIffGenusZeroRecovered : Bool
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
  ; duplicatePairCountAuthorityEliminated = true
  ; completedLocalAuthorityRequiredPerNode = true
  ; branchCountAloneSufficient = false
  ; fixedIffGenusZeroRecovered = true
  ; sameObjectSpecialFibreEqualityRequired = true
  ; properFlatGenusTransportRequired = true
  ; finiteFrickeTableUsed = false
  ; arbitraryPrimeAuthorityConstructedHere = false
  }
