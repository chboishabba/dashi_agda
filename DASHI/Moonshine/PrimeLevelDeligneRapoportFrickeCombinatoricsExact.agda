module DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact where

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
-- Treneer recalls the Deligne--Rapoport/Ogg reduction picture used here:
-- X_0(p) mod p has two X_0(1) components meeting transversally at the
-- supersingular points.  The Fricke involution exchanges the components;
-- on the supersingular intersections it fixes F_p-rational j-invariants and
-- exchanges Frobenius-conjugate quadratic pairs.  In the quotient, linear
-- supersingular intersections are resolved while each quadratic pair produces
-- one self-intersection.
--
-- DASHI CONTRIBUTION
--
-- Formalize the finite combinatorial content of that description on top of the
-- repository's existing finite-involution normal form.  Given an ACTUAL
-- supersingular carrier and an explicit realization of arithmetic Frobenius as
--
--   Fin fixed  +  (Fin paired x Bit2),
--
-- construct:
--
--   * the two Deligne--Rapoport component labels and Fricke component swap;
--   * explicit oriented representatives of every quadratic Frobenius pair;
--   * the quotient-node coordinate Fin paired;
--   * the canonical one-vertex / paired-loop dual graph;
--   * arithmetic genus = paired, using the generic nodal dual-graph theorem.
--
-- This file still does NOT manufacture the modular scheme X_0(p), its quotient,
-- or flatness.  Those source-facing geometric identifications are isolated in
-- a separate authority/transport layer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
import Data.Nat.Properties as Nat

import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit
import DASHI.Foundations.FiniteInvolutionPairedOrbitQuotientExact as PairQuot
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal

------------------------------------------------------------------------
-- The two irreducible components before Fricke quotienting.
------------------------------------------------------------------------

data DRComponent : Set where
  component0 componentInfinity : DRComponent

frickeComponent : DRComponent → DRComponent
frickeComponent component0 = componentInfinity
frickeComponent componentInfinity = component0

frickeComponentInvolutive :
  (component : DRComponent) →
  frickeComponent (frickeComponent component) ≡ component
frickeComponentInvolutive component0 = refl
frickeComponentInvolutive componentInfinity = refl

------------------------------------------------------------------------
-- Source-facing finite supersingular/Frobenius realization.
------------------------------------------------------------------------

record PrimeLevelSupersingularFrobeniusData : Set₁ where
  field
    prime : Nat
    Supersingular : Set
    frobenius : Supersingular → Supersingular

    fixedCount : Nat
    pairedCount : Nat
    totalCount : Nat

    spectrum : Orbit.InvolutionOrbitSpectrum
    spectrumFixed : Orbit.fixedOrbitCount spectrum ≡ fixedCount
    spectrumPaired : Orbit.pairedOrbitCount spectrum ≡ pairedCount
    spectrumTotal : Orbit.totalCarrierCount spectrum ≡ totalCount

    normalForm :
      Orbit.InvolutionNormalFormRealization Supersingular frobenius spectrum

open PrimeLevelSupersingularFrobeniusData public

------------------------------------------------------------------------
-- Work directly in the spectrum-indexed normal form.  Keeping these versions
-- spectrum-indexed avoids unsafe casts from a count equality.
------------------------------------------------------------------------

NormalPairedCarrier : PrimeLevelSupersingularFrobeniusData → Set
NormalPairedCarrier D =
  PairQuot.PairedOrbitCarrier (Orbit.pairedOrbitCount (spectrum D))

normalPairedRepresentative :
  (D : PrimeLevelSupersingularFrobeniusData) →
  NormalPairedCarrier D → Supersingular D
normalPairedRepresentative D (index , bit) =
  Orbit.fromNormal (normalForm D) (inj₂ (index , bit))

normalPairedRepresentative0 :
  (D : PrimeLevelSupersingularFrobeniusData) →
  Fin (Orbit.pairedOrbitCount (spectrum D)) → Supersingular D
normalPairedRepresentative0 D index =
  normalPairedRepresentative D (index , Orbit.bit0)

normalPairedRepresentative1 :
  (D : PrimeLevelSupersingularFrobeniusData) →
  Fin (Orbit.pairedOrbitCount (spectrum D)) → Supersingular D
normalPairedRepresentative1 D index =
  normalPairedRepresentative D (index , Orbit.bit1)

frobeniusExchangesNormalPair0 :
  (D : PrimeLevelSupersingularFrobeniusData) →
  (index : Fin (Orbit.pairedOrbitCount (spectrum D))) →
  Orbit.toNormal (normalForm D)
    (frobenius D (normalPairedRepresentative0 D index))
  ≡ inj₂ (index , Orbit.bit1)
frobeniusExchangesNormalPair0 D index =
  trans
    (Orbit.intertwinesInvolution (normalForm D)
      (normalPairedRepresentative0 D index))
    (cong Orbit.orbitInvolution
      (Orbit.toAfterFrom (normalForm D) (inj₂ (index , Orbit.bit0))))

frobeniusExchangesNormalPair1 :
  (D : PrimeLevelSupersingularFrobeniusData) →
  (index : Fin (Orbit.pairedOrbitCount (spectrum D))) →
  Orbit.toNormal (normalForm D)
    (frobenius D (normalPairedRepresentative1 D index))
  ≡ inj₂ (index , Orbit.bit0)
frobeniusExchangesNormalPair1 D index =
  trans
    (Orbit.intertwinesInvolution (normalForm D)
      (normalPairedRepresentative1 D index))
    (cong Orbit.orbitInvolution
      (Orbit.toAfterFrom (normalForm D) (inj₂ (index , Orbit.bit1))))

------------------------------------------------------------------------
-- Canonical quotient-node coordinate on the nonfixed supersingular locus.
------------------------------------------------------------------------

FrickeNode : PrimeLevelSupersingularFrobeniusData → Set
FrickeNode D = Fin (Orbit.pairedOrbitCount (spectrum D))

frickeNodeOfNormalPair :
  (D : PrimeLevelSupersingularFrobeniusData) →
  NormalPairedCarrier D → FrickeNode D
frickeNodeOfNormalPair D = PairQuot.pairedOrbitNode

frickeNodeInvariantUnderFrobenius :
  (D : PrimeLevelSupersingularFrobeniusData) →
  (pair : NormalPairedCarrier D) →
  frickeNodeOfNormalPair D (PairQuot.pairedOrbitInvolution pair)
  ≡ frickeNodeOfNormalPair D pair
frickeNodeInvariantUnderFrobenius D = PairQuot.pairedOrbitNodeInvariant

frickeNodeSection :
  (D : PrimeLevelSupersingularFrobeniusData) →
  FrickeNode D → NormalPairedCarrier D
frickeNodeSection D = PairQuot.pairedOrbitNodeSection

frickeNodeAfterSection :
  (D : PrimeLevelSupersingularFrobeniusData) →
  (node : FrickeNode D) →
  frickeNodeOfNormalPair D (frickeNodeSection D node) ≡ node
frickeNodeAfterSection D = PairQuot.pairedOrbitNodeAfterSection

------------------------------------------------------------------------
-- Canonical combinatorial Fricke quotient special fibre.
--
-- One rational component gives one dual-graph vertex.  Each nonfixed
-- Frobenius pair gives one self-node / loop edge.  The generic nodal theorem
-- therefore computes arithmetic genus exactly as the paired-orbit count.
------------------------------------------------------------------------

canonicalFrickeQuotientDualGraph :
  (D : PrimeLevelSupersingularFrobeniusData) →
  Nodal.NodalDualGraphGenusData
canonicalFrickeQuotientDualGraph D = record
  { Nodal.nodeCount = Orbit.pairedOrbitCount (spectrum D)
  ; Nodal.vertexCount = 1
  ; Nodal.edgeCount = Orbit.pairedOrbitCount (spectrum D)
  ; Nodal.cycleRank = Orbit.pairedOrbitCount (spectrum D)
  ; Nodal.componentGenusSum = 0
  ; Nodal.arithmeticGenus = Orbit.pairedOrbitCount (spectrum D)
  ; Nodal.oneComponent = refl
  ; Nodal.oneEdgePerNode = refl
  ; Nodal.graphEuler = Nat.+-comm (Orbit.pairedOrbitCount (spectrum D)) 1
  ; Nodal.rationalComponents = refl
  ; Nodal.nodalGenusFormula = refl
  }

canonicalFrickeArithmeticGenusEqualsPaired :
  (D : PrimeLevelSupersingularFrobeniusData) →
  Nodal.arithmeticGenus (canonicalFrickeQuotientDualGraph D)
  ≡ Orbit.pairedOrbitCount (spectrum D)
canonicalFrickeArithmeticGenusEqualsPaired D =
  Nodal.arithmeticGenusEqualsNodeCount (canonicalFrickeQuotientDualGraph D)

canonicalFrickeArithmeticGenusEqualsDeclaredPairCount :
  (D : PrimeLevelSupersingularFrobeniusData) →
  Nodal.arithmeticGenus (canonicalFrickeQuotientDualGraph D)
  ≡ pairedCount D
canonicalFrickeArithmeticGenusEqualsDeclaredPairCount D =
  trans
    (canonicalFrickeArithmeticGenusEqualsPaired D)
    (spectrumPaired D)

record PrimeLevelDeligneRapoportFrickeCombinatoricsBoundary : Set where
  field
    twoComponentSwapConstructed : Bool
    pairedFrobeniusRepresentativesConstructed : Bool
    quotientNodeCoordinateConstructed : Bool
    oneLoopPerPairedOrbitConstructed : Bool
    arithmeticGenusEqualsPairCountDerived : Bool
    actualModularSpecialFibreIdentifiedHere : Bool
    flatFamilyConstructedHere : Bool

canonicalPrimeLevelDeligneRapoportFrickeCombinatoricsBoundary :
  PrimeLevelDeligneRapoportFrickeCombinatoricsBoundary
canonicalPrimeLevelDeligneRapoportFrickeCombinatoricsBoundary = record
  { twoComponentSwapConstructed = true
  ; pairedFrobeniusRepresentativesConstructed = true
  ; quotientNodeCoordinateConstructed = true
  ; oneLoopPerPairedOrbitConstructed = true
  ; arithmeticGenusEqualsPairCountDerived = true
  ; actualModularSpecialFibreIdentifiedHere = false
  ; flatFamilyConstructedHere = false
  }
