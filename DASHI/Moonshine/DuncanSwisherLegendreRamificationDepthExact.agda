module DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 and its sharpness proof.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
-- In particular the Legendre local-coordinate discussion used in §7.e.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Supersingular / Brandt weight convention 2 w(E)=|Aut(E)|.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
-- Exceptional elliptic automorphism groups at j=0 and j=1728.
--
-- SOURCE MECHANISM
--
-- Duncan--Swisher explain the exceptional sharpness in Proposition 3.1 by the
-- local Legendre coordinate lambda:
--
--   J_1+744  behaves like (lambda-lambda_0)^3 at j=0,
--   J_1-984  behaves like (lambda-lambda_0)^2 at j=1728,
--
-- while an ordinary point has ramification index 1.  The sharp first-pole
-- depths are therefore 3,2,1.  These are simultaneously half the full elliptic
-- automorphism orders 6,4,2.
--
-- DASHI CONTRIBUTION
--
-- Make the common scale theorem-level:
--
--   first-pole depth
--     = Legendre j-map ramification index
--     = reduced automorphism / Brandt monodromy weight
--     = |Aut(E)| / 2.
--
-- This is NOT the reciprocal stack-sheet multiplicity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact as Stack11
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

------------------------------------------------------------------------
-- Ramification index on the source's three supersingular automorphism types.
------------------------------------------------------------------------

legendreJRamificationIndex : Deligne.SupersingularAutomorphismType → Nat
legendreJRamificationIndex Deligne.jZeroExceptional = 3
legendreJRamificationIndex Deligne.j1728Exceptional = 2
legendreJRamificationIndex Deligne.ordinaryType = 1

firstPoleDepthIsLegendreRamification :
  (t : Deligne.SupersingularAutomorphismType) →
  Deligne.firstPoleDepth t ≡ legendreJRamificationIndex t
firstPoleDepthIsLegendreRamification Deligne.jZeroExceptional = refl
firstPoleDepthIsLegendreRamification Deligne.j1728Exceptional = refl
firstPoleDepthIsLegendreRamification Deligne.ordinaryType = refl

fullAutomorphismOrderIsTwiceRamification :
  (t : Deligne.SupersingularAutomorphismType) →
  Deligne.fullAutomorphismOrder t ≡ 2 * legendreJRamificationIndex t
fullAutomorphismOrderIsTwiceRamification Deligne.jZeroExceptional = refl
fullAutomorphismOrderIsTwiceRamification Deligne.j1728Exceptional = refl
fullAutomorphismOrderIsTwiceRamification Deligne.ordinaryType = refl

firstPoleDepthIsReducedAutomorphismWeight :
  (t : Deligne.SupersingularAutomorphismType) →
  2 * Deligne.firstPoleDepth t ≡ Deligne.fullAutomorphismOrder t
firstPoleDepthIsReducedAutomorphismWeight =
  Deligne.depthDoublesToFullAutomorphismOrder

------------------------------------------------------------------------
-- p=11 weld to the EXISTING Brandt-stack monodromy-weight owner.
------------------------------------------------------------------------

p11AutType : Geo.P11SupersingularJ → Deligne.SupersingularAutomorphismType
p11AutType Geo.jZeroSS = Deligne.jZeroExceptional
p11AutType Geo.j1728SS = Deligne.j1728Exceptional

p11DeligneDepth : Geo.P11SupersingularJ → Nat
p11DeligneDepth c = Deligne.firstPoleDepth (p11AutType c)

p11RamificationIndex : Geo.P11SupersingularJ → Nat
p11RamificationIndex c = legendreJRamificationIndex (p11AutType c)

p11DepthIsRamification :
  (c : Geo.P11SupersingularJ) →
  p11DeligneDepth c ≡ p11RamificationIndex c
p11DepthIsRamification Geo.jZeroSS = refl
p11DepthIsRamification Geo.j1728SS = refl

p11RamificationIsBrandtMonodromyWeight :
  (c : Geo.P11SupersingularJ) →
  p11RamificationIndex c ≡ Stack11.p11MonodromyWeight c
p11RamificationIsBrandtMonodromyWeight Geo.jZeroSS = refl
p11RamificationIsBrandtMonodromyWeight Geo.j1728SS = refl

p11DeligneDepthIsBrandtMonodromyWeight :
  (c : Geo.P11SupersingularJ) →
  p11DeligneDepth c ≡ Stack11.p11MonodromyWeight c
p11DeligneDepthIsBrandtMonodromyWeight c =
  trans
    (p11DepthIsRamification c)
    (p11RamificationIsBrandtMonodromyWeight c)

------------------------------------------------------------------------
-- Exact p11 values.
------------------------------------------------------------------------

p11JZeroDepthWeight :
  p11DeligneDepth Geo.jZeroSS ≡ 3
  × Stack11.p11MonodromyWeight Geo.jZeroSS ≡ 3
p11JZeroDepthWeight = refl , refl

p11J1728DepthWeight :
  p11DeligneDepth Geo.j1728SS ≡ 2
  × Stack11.p11MonodromyWeight Geo.j1728SS ≡ 2
p11J1728DepthWeight = refl , refl

------------------------------------------------------------------------
-- Reciprocal sheet multiplicity is the DUAL stack construction, not Deligne
-- depth.  Both p11 fibres give explicit contradictions to such an identification.
------------------------------------------------------------------------

jZeroSheetMultiplicityIsNotDeligneDepth :
  Stack11.p11SheetMultiplicity Geo.jZeroSS ≡ p11DeligneDepth Geo.jZeroSS → ⊥
jZeroSheetMultiplicityIsNotDeligneDepth ()

j1728SheetMultiplicityIsNotDeligneDepth :
  Stack11.p11SheetMultiplicity Geo.j1728SS ≡ p11DeligneDepth Geo.j1728SS → ⊥
j1728SheetMultiplicityIsNotDeligneDepth ()

------------------------------------------------------------------------
-- The common scale can be summarized without division:
--
--   2 * monodromyWeight = fullAut,
--   sheetMultiplicity * monodromyWeight = commonScale.
--
-- Thus the same weight is DIRECT in the Deligne depth lane and RECIPROCAL in
-- the stack-unweighting lane.
------------------------------------------------------------------------

p11TwiceDepthIsFullAut :
  (c : Geo.P11SupersingularJ) →
  2 * p11DeligneDepth c ≡ Deligne.fullAutomorphismOrder (p11AutType c)
p11TwiceDepthIsFullAut Geo.jZeroSS = refl
p11TwiceDepthIsFullAut Geo.j1728SS = refl

p11SheetTimesDepthIsCommonScale :
  (c : Geo.P11SupersingularJ) →
  Stack11.p11SheetMultiplicity c * p11DeligneDepth c
  ≡ Stack11.p11CommonScale
p11SheetTimesDepthIsCommonScale Geo.jZeroSS = refl
p11SheetTimesDepthIsCommonScale Geo.j1728SS = refl

record DuncanSwisherLegendreRamificationDepthBoundary : Set where
  field
    legendreRamificationIndexConstructed : Bool
    firstPoleDepthEqualsRamification : Bool
    ramificationEqualsHalfFullAut : Bool
    p11DepthEqualsBrandtMonodromyWeight : Bool
    p11DepthEqualsReciprocalSheetMultiplicity : Bool
    directVsReciprocalStackRolesSeparated : Bool
    dworkLocalAnalyticSharpnessReprovedHere : Bool

canonicalDuncanSwisherLegendreRamificationDepthBoundary :
  DuncanSwisherLegendreRamificationDepthBoundary
canonicalDuncanSwisherLegendreRamificationDepthBoundary = record
  { legendreRamificationIndexConstructed = true
  ; firstPoleDepthEqualsRamification = true
  ; ramificationEqualsHalfFullAut = true
  ; p11DepthEqualsBrandtMonodromyWeight = true
  ; p11DepthEqualsReciprocalSheetMultiplicity = false
  ; directVsReciprocalStackRolesSeparated = true
  ; dworkLocalAnalyticSharpnessReprovedHere = false
  }
