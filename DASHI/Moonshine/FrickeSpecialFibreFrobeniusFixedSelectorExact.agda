module DASHI.Moonshine.FrickeSpecialFibreFrobeniusFixedSelectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephanie Treneer,
-- "Weierstrass points on X_0^+(p) and supersingular j-invariants",
-- Research in the Mathematical Sciences 4 (2017), article 25.
-- DOI: 10.1186/s40687-017-0115-z.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Weld the two generic theorem packages already present on PR #585:
--
--   (1) an ACTUAL involution carrier realized as fixed points plus two-cycles;
--   (2) an ACTUAL Fricke nodal special fibre whose self-node count is the
--       quadratic Frobenius-pair count and whose arithmetic genus equals the
--       generic Fricke genus by flatness.
--
-- Once those two source-facing objects are tied by equality of their pair
-- counts, the selector becomes entirely geometric and table-free:
--
--     Frobenius pointwise fixed
--       <=> no paired orbit
--       <=> g(X_0^+(p)) = 0.
--
-- This is intentionally NOT the finite under-72 Ogg-label theorem.  No Ogg
-- control table is imported, and no external Monster label is used.  The only
-- remaining all-prime producer is the actual Deligne--Rapoport/Fricke
-- special-fibre realization together with the actual supersingular Frobenius
-- normal-form realization and their same-object pair-count identification.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero)
open import Data.Sum using (inj₁; inj₂)

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Moonshine.SupersingularFrickeSpecialFibreSelectorExact as Fricke

record PrimeFrickeFrobeniusGeometry : Set₁ where
  field
    Carrier : Set
    frobenius : Carrier → Carrier
    spectrum : Orbit.InvolutionOrbitSpectrum

    frobeniusRealization :
      Orbit.InvolutionNormalFormRealization Carrier frobenius spectrum

    specialFibreRealization : Fricke.PrimeFrickeSpecialFibreRealization

    -- This equality is the real seam between the two source-facing models:
    -- the pairs counted by the actual involution carrier are exactly the
    -- quadratic pairs that become nodes in the actual Fricke special fibre.
    pairCountSameObject :
      Orbit.pairedOrbitCount spectrum
      ≡ Fricke.frobeniusPairDefect specialFibreRealization

open PrimeFrickeFrobeniusGeometry public

GeometricallyFullyFixed : PrimeFrickeFrobeniusGeometry → Set
GeometricallyFullyFixed G =
  (x : Carrier G) → frobenius G x ≡ x

------------------------------------------------------------------------
-- Generic normal-form equivalence: all fixed iff paired count is zero.
------------------------------------------------------------------------

noPairsImpliesAllFixed :
  (G : PrimeFrickeFrobeniusGeometry) →
  Orbit.pairedOrbitCount (spectrum G) ≡ 0 →
  GeometricallyFullyFixed G
noPairsImpliesAllFixed G pairZero x
  rewrite pairZero
  with Orbit.toNormal (frobeniusRealization G) x
... | inj₁ fixedIndex =
  trans
    (sym
      (Orbit.fromAfterTo
        (frobeniusRealization G)
        (frobenius G x)))
    (trans
      (cong
        (Orbit.fromNormal (frobeniusRealization G))
        (trans
          (Orbit.intertwinesInvolution (frobeniusRealization G) x)
          (Orbit.fixedSummandReallyFixed fixedIndex)))
      (Orbit.fromAfterTo (frobeniusRealization G) x))
... | inj₂ (() , bit)

allFixedImpliesNoPairs :
  (G : PrimeFrickeFrobeniusGeometry) →
  GeometricallyFullyFixed G →
  Orbit.pairedOrbitCount (spectrum G) ≡ 0
allFixedImpliesNoPairs G allFixed
  with Orbit.pairedOrbitCount (spectrum G)
... | zero = refl
... | suc paired =
  let
    R = frobeniusRealization G
    normalPoint = inj₂ (zero , Orbit.bit0)
    x = Orbit.fromNormal R normalPoint

    geometricFixed : frobenius G x ≡ x
    geometricFixed = allFixed x

    normalFixed : Orbit.orbitInvolution normalPoint ≡ normalPoint
    normalFixed =
      trans
        (cong Orbit.orbitInvolution
          (sym (Orbit.toAfterFrom R normalPoint)))
        (trans
          (sym (Orbit.intertwinesInvolution R x))
          (trans
            (cong (Orbit.toNormal R) geometricFixed)
            (Orbit.toAfterFrom R normalPoint)))
  in
  ⊥-elim (Orbit.pairedSummandHasNoFixedPoint zero Orbit.bit0 normalFixed)

------------------------------------------------------------------------
-- Same-object pair count plus the nodal special-fibre theorem converts the
-- involution statement directly into the generic Fricke genus statement.
------------------------------------------------------------------------

noPairsImpliesGenusZero :
  (G : PrimeFrickeFrobeniusGeometry) →
  Orbit.pairedOrbitCount (spectrum G) ≡ 0 →
  Fricke.genericFrickeGenus (specialFibreRealization G) ≡ 0
noPairsImpliesGenusZero G pairZero =
  trans
    (Fricke.frickeGenusEqualsFrobeniusPairDefect
      (specialFibreRealization G))
    (trans
      (sym (pairCountSameObject G))
      pairZero)

genusZeroImpliesNoPairs :
  (G : PrimeFrickeFrobeniusGeometry) →
  Fricke.genericFrickeGenus (specialFibreRealization G) ≡ 0 →
  Orbit.pairedOrbitCount (spectrum G) ≡ 0
genusZeroImpliesNoPairs G genusZero =
  trans
    (pairCountSameObject G)
    (trans
      (sym
        (Fricke.frickeGenusEqualsFrobeniusPairDefect
          (specialFibreRealization G)))
      genusZero)

allFixedImpliesFrickeGenusZero :
  (G : PrimeFrickeFrobeniusGeometry) →
  GeometricallyFullyFixed G →
  Fricke.genericFrickeGenus (specialFibreRealization G) ≡ 0
allFixedImpliesFrickeGenusZero G allFixed =
  noPairsImpliesGenusZero G (allFixedImpliesNoPairs G allFixed)

frickeGenusZeroImpliesAllFixed :
  (G : PrimeFrickeFrobeniusGeometry) →
  Fricke.genericFrickeGenus (specialFibreRealization G) ≡ 0 →
  GeometricallyFullyFixed G
frickeGenusZeroImpliesAllFixed G genusZero =
  noPairsImpliesAllFixed G (genusZeroImpliesNoPairs G genusZero)

frobeniusFullyFixedIffFrickeGenusZero :
  (G : PrimeFrickeFrobeniusGeometry) →
  GeometricallyFullyFixed G
  ↔ Fricke.genericFrickeGenus (specialFibreRealization G) ≡ 0
frobeniusFullyFixedIffFrickeGenusZero G =
  allFixedImpliesFrickeGenusZero G
  , frickeGenusZeroImpliesAllFixed G

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record FrickeFrobeniusFixedSelectorBoundary : Set where
  field
    fixedIffNoPairsDerivedFromRealization : Bool
    fixedIffNoPairsDerivedFromRealizationIsTrue :
      fixedIffNoPairsDerivedFromRealization ≡ true

    allFixedIffFrickeGenusZeroDerived : Bool
    allFixedIffFrickeGenusZeroDerivedIsTrue :
      allFixedIffFrickeGenusZeroDerived ≡ true

    finiteOggControlTableUsed : Bool
    finiteOggControlTableUsedIsFalse : finiteOggControlTableUsed ≡ false

    arbitraryPrimeGeometryConstructedHere : Bool
    arbitraryPrimeGeometryConstructedHereIsFalse :
      arbitraryPrimeGeometryConstructedHere ≡ false

    monsterEquivalenceClaimedHere : Bool
    monsterEquivalenceClaimedHereIsFalse : monsterEquivalenceClaimedHere ≡ false

canonicalFrickeFrobeniusFixedSelectorBoundary :
  FrickeFrobeniusFixedSelectorBoundary
canonicalFrickeFrobeniusFixedSelectorBoundary = record
  { fixedIffNoPairsDerivedFromRealization = true
  ; fixedIffNoPairsDerivedFromRealizationIsTrue = refl
  ; allFixedIffFrickeGenusZeroDerived = true
  ; allFixedIffFrickeGenusZeroDerivedIsTrue = refl
  ; finiteOggControlTableUsed = false
  ; finiteOggControlTableUsedIsFalse = refl
  ; arbitraryPrimeGeometryConstructedHere = false
  ; arbitraryPrimeGeometryConstructedHereIsFalse = refl
  ; monsterEquivalenceClaimedHere = false
  ; monsterEquivalenceClaimedHereIsFalse = refl
  }
