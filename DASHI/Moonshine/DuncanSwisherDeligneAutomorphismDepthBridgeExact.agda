module DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Their Proposition 3.1 applies Deligne/Dwork/Koike p-adic rigidity to
-- p J_1|U_p.  For p>3 the n=1 partial-fraction coefficient has exact p-adic
-- depth
--
--   3  at the supersingular J_1-value -744  (j=0),
--   2  at the supersingular J_1-value  984  (j=1728),
--   1  at every other supersingular j-class.
--
-- The full automorphism orders of elliptic curves in characteristic p>3 are
-- correspondingly
--
--   6 at j=0,  4 at j=1728,  2 generically.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42 DOI: 10.1007/978-3-030-56694-4_42.
--
-- DASHI CONTRIBUTION
--
-- Make the hidden equality theorem-level:
--
--   2 * (Deligne first-pole depth) = full automorphism order.
--
-- Therefore Duncan--Swisher's m_p/2 is exactly the MINIMUM first-pole depth
-- over the supersingular locus.  At p=11 this consumes the existing geometric
-- j=0/j=1728 carrier and gives depths 3 and 2 from full orders 6 and 4.
--
-- IMPORTANT BOUNDARY
-- This module imports the source's exact first-pole depth classification.  It
-- does not reprove Deligne's p-adic partial-fraction expansion from scratch.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11

------------------------------------------------------------------------
-- The only full automorphism types occurring for elliptic curves in p>3.
------------------------------------------------------------------------

data SupersingularAutomorphismType : Set where
  jZeroExceptional : SupersingularAutomorphismType
  j1728Exceptional : SupersingularAutomorphismType
  ordinaryType : SupersingularAutomorphismType

fullAutomorphismOrder : SupersingularAutomorphismType → Nat
fullAutomorphismOrder jZeroExceptional = 6
fullAutomorphismOrder j1728Exceptional = 4
fullAutomorphismOrder ordinaryType = 2

------------------------------------------------------------------------
-- Exact n=1 Deligne coefficient depths from Duncan--Swisher Proposition 3.1.
------------------------------------------------------------------------

deligneFirstPoleDepth : SupersingularAutomorphismType → Nat
deligneFirstPoleDepth jZeroExceptional = 3
deligneFirstPoleDepth j1728Exceptional = 2
deligneFirstPoleDepth ordinaryType = 1

firstPoleDepthDoublesToFullAutomorphismOrder :
  (t : SupersingularAutomorphismType) →
  2 * deligneFirstPoleDepth t ≡ fullAutomorphismOrder t
firstPoleDepthDoublesToFullAutomorphismOrder jZeroExceptional = refl
firstPoleDepthDoublesToFullAutomorphismOrder j1728Exceptional = refl
firstPoleDepthDoublesToFullAutomorphismOrder ordinaryType = refl

------------------------------------------------------------------------
-- Minimum-depth interface.  A witness attaining the minimum full automorphism
-- order automatically attains half that order as a Deligne first-pole depth.
------------------------------------------------------------------------

record MinimumAutomorphismWitness : Set where
  constructor minimum-automorphism-witness
  field
    minimumType : SupersingularAutomorphismType
    minimumFullOrder : Nat
    minimumOrderExact : fullAutomorphismOrder minimumType ≡ minimumFullOrder

open MinimumAutomorphismWitness public

minimumFirstPoleDepth : MinimumAutomorphismWitness → Nat
minimumFirstPoleDepth W = deligneFirstPoleDepth (minimumType W)

minimumDepthDoublesToMinimumFullOrder :
  (W : MinimumAutomorphismWitness) →
  2 * minimumFirstPoleDepth W ≡ minimumFullOrder W
minimumDepthDoublesToMinimumFullOrder W =
  trans
    (firstPoleDepthDoublesToFullAutomorphismOrder (minimumType W))
    (minimumOrderExact W)

------------------------------------------------------------------------
-- Exact p=11 bridge to the old #567 reduced-stabilizer carrier.
------------------------------------------------------------------------

p11AutType : P11.P11SupersingularJ → SupersingularAutomorphismType
p11AutType P11.jZeroSS = jZeroExceptional
p11AutType P11.j1728SS = j1728Exceptional

p11FullOrderFromType :
  (j : P11.P11SupersingularJ) →
  fullAutomorphismOrder (p11AutType j)
  ≡ 2 * P11.reducedAutomorphismOrder j
p11FullOrderFromType P11.jZeroSS = refl
p11FullOrderFromType P11.j1728SS = refl

p11JZeroDeligneDepthIsThree :
  deligneFirstPoleDepth (p11AutType P11.jZeroSS) ≡ 3
p11JZeroDeligneDepthIsThree = refl

p11J1728DeligneDepthIsTwo :
  deligneFirstPoleDepth (p11AutType P11.j1728SS) ≡ 2
p11J1728DeligneDepthIsTwo = refl

p11MinimumWitness : MinimumAutomorphismWitness
p11MinimumWitness = minimum-automorphism-witness j1728Exceptional 4 refl

p11MinimumDeligneDepthIsTwo : minimumFirstPoleDepth p11MinimumWitness ≡ 2
p11MinimumDeligneDepthIsTwo = refl

p11MinimumDepthDoublesToMp :
  2 * minimumFirstPoleDepth p11MinimumWitness ≡ 4
p11MinimumDepthDoublesToMp = minimumDepthDoublesToMinimumFullOrder p11MinimumWitness

------------------------------------------------------------------------
-- Explicit convention separation from the earlier stack-unweighting lane.
------------------------------------------------------------------------

record DuncanSwisherDeligneAutomorphismDepthBoundary : Set where
  field
    deligneFirstPoleDepthClassificationImported : Bool
    fullAutomorphismTypeClassificationRetained : Bool
    depthDoublesToFullAutomorphismOrderDerived : Bool
    p11BrandtReducedOrderBridgeConstructed : Bool
    p11MinimumDepthEqualsTwoDerived : Bool
    reciprocalSheetMultiplicityUsedAsDeligneDepth : Bool
    fullDelignePartialFractionExpansionConstructedHere : Bool

canonicalDuncanSwisherDeligneAutomorphismDepthBoundary :
  DuncanSwisherDeligneAutomorphismDepthBoundary
canonicalDuncanSwisherDeligneAutomorphismDepthBoundary = record
  { deligneFirstPoleDepthClassificationImported = true
  ; fullAutomorphismTypeClassificationRetained = true
  ; depthDoublesToFullAutomorphismOrderDerived = true
  ; p11BrandtReducedOrderBridgeConstructed = true
  ; p11MinimumDepthEqualsTwoDerived = true
  ; reciprocalSheetMultiplicityUsedAsDeligneDepth = false
  ; fullDelignePartialFractionExpansionConstructedHere = false
  }
