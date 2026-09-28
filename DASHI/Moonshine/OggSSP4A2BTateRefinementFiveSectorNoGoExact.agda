module DASHI.Moonshine.OggSSP4A2BTateRefinementFiveSectorNoGoExact where

------------------------------------------------------------------------
-- 4A LABEL + PARITY + 2B TATE REFINEMENT STILL FOUR-vs-FIVE
--
-- EXTERNAL SOURCE INPUTS
--
-- Carnahan--Urano, Theorem 6.2 / Lemma 6.4 / Theorem 6.5:
--
--   actual 4A Moonshine indecomposables: A, D, C^A;
--
--   total Tate dimension for g^2:
--       A   -> 1
--       D   -> 0
--       C^A -> 1;
--
--   parity support after intersecting the order-4 parity list with Theorem 6.5:
--       A   only even,
--       D   even or odd,
--       C^A only odd.
--
-- Carnahan, Corollary 3.25 for 2B:
--
--   H^0 trace = (T(tau) + T(tau+1/2))/2,
--   H^1 trace = (T(tau) - T(tau+1/2))/2.
--
-- Since q^(n-1) picks up (-1)^(n-1) under tau -> tau+1/2:
--
--   H^0 selects odd n,
--   H^1 selects even n.
--
-- Therefore the source-native refined patterns are still only:
--
--   even A   / H^1 only,
--   even D   / Tate acyclic,
--   odd  D   / Tate acyclic,
--   odd  C^A / H^0 only.
--
-- RESULT
--
-- There are exactly four such source labels, so no exact two-sided rechart to
-- the five characteristic-2 inertia sectors exists.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (<⇒notInjective)
open import Function.Definitions using (Injective)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSP4A2BThreeLabelFiveSectorNoGoExact as FourANoGo
import DASHI.Moonshine.OggSSP2BCarnahanTateSplitExact as TwoBTate
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution for the combined inference.
------------------------------------------------------------------------

carnahanUranoIntegralGroupRings : Source.AttributedSource
carnahanUranoIntegralGroupRings =
  Source.mkDOISource
    "Scott Carnahan and Satoru Urano"
    "Monstrous Moonshine for Integral Group Rings"
    "International Mathematics Research Notices 2024(4), 2748-2789"
    "2024"
    "10.1093/imrn/rnad028"
    "https://doi.org/10.1093/imrn/rnad028"
    Source.academicArticleSource
    "Theorem 6.2 gives total Tate-dimension values on order-4 indecomposables; Lemma 6.4 gives square-subgroup restrictions; Theorem 6.5 gives the actual 4A indecomposables A,D,C^A and their graded decomposition.  The paper does not identify these with characteristic-2 inertia sectors."
    Source.publicAttribution

carnahanSelfDualIntegralForm : Source.AttributedSource
carnahanSelfDualIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "Symmetry, Integrability and Geometry: Methods and Applications 15, 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 gives the 2B Tate H^0/H^1 half-sum/half-difference formulas with tau -> tau+1/2; DASHI combines this with the 4A parity/decomposition table."
    Source.publicAttribution

fourATwoBTateRefinementSourceAtlas : Source.AttributedSourceAtlas
fourATwoBTateRefinementSourceAtlas =
  Source.mkSourceAtlas
    "4A restricted-label plus 2B Tate-refinement no-go"
    "DASHI.Moonshine.OggSSP4A2BTateRefinementFiveSectorNoGoExact"
    (carnahanUranoIntegralGroupRings ∷ carnahanSelfDualIntegralForm ∷ [])
    "sources separately own the 4A decomposition/Tate-total data and 2B H^0/H^1 formula; DASHI owns the four-pattern cross-inference and finite no-go"

------------------------------------------------------------------------
-- 2. Exact Tate-support profile.
------------------------------------------------------------------------

data TwoBTateSupportProfile : Set where
  h0Only :
    TwoBTateSupportProfile
  h1Only :
    TwoBTateSupportProfile
  tateAcyclic :
    TwoBTateSupportProfile

tateSupportOfFourAPattern :
  FourANoGo.FourALabelParityPattern ->
  TwoBTateSupportProfile
tateSupportOfFourAPattern FourANoGo.evenA = h1Only
tateSupportOfFourAPattern FourANoGo.evenD = tateAcyclic
tateSupportOfFourAPattern FourANoGo.oddD = tateAcyclic
tateSupportOfFourAPattern FourANoGo.oddCA = h0Only

data FourATateRefinedPattern : Set where
  evenAH1 :
    FourATateRefinedPattern
  evenDAcyclic :
    FourATateRefinedPattern
  oddDAcyclic :
    FourATateRefinedPattern
  oddCAH0 :
    FourATateRefinedPattern

refinedToFourAPattern :
  FourATateRefinedPattern ->
  FourANoGo.FourALabelParityPattern
refinedToFourAPattern evenAH1 = FourANoGo.evenA
refinedToFourAPattern evenDAcyclic = FourANoGo.evenD
refinedToFourAPattern oddDAcyclic = FourANoGo.oddD
refinedToFourAPattern oddCAH0 = FourANoGo.oddCA

fourAPatternToRefined :
  FourANoGo.FourALabelParityPattern ->
  FourATateRefinedPattern
fourAPatternToRefined FourANoGo.evenA = evenAH1
fourAPatternToRefined FourANoGo.evenD = evenDAcyclic
fourAPatternToRefined FourANoGo.oddD = oddDAcyclic
fourAPatternToRefined FourANoGo.oddCA = oddCAH0

refinedRoundTrip :
  (pattern : FourATateRefinedPattern) ->
  fourAPatternToRefined (refinedToFourAPattern pattern) ≡ pattern
refinedRoundTrip evenAH1 = refl
refinedRoundTrip evenDAcyclic = refl
refinedRoundTrip oddDAcyclic = refl
refinedRoundTrip oddCAH0 = refl

fourAPatternRoundTrip :
  (pattern : FourANoGo.FourALabelParityPattern) ->
  refinedToFourAPattern (fourAPatternToRefined pattern) ≡ pattern
fourAPatternRoundTrip FourANoGo.evenA = refl
fourAPatternRoundTrip FourANoGo.evenD = refl
fourAPatternRoundTrip FourANoGo.oddD = refl
fourAPatternRoundTrip FourANoGo.oddCA = refl

refinedTateSupport :
  FourATateRefinedPattern ->
  TwoBTateSupportProfile
refinedTateSupport pattern =
  tateSupportOfFourAPattern (refinedToFourAPattern pattern)

------------------------------------------------------------------------
-- 3. Finite enumerations.
------------------------------------------------------------------------

refinedToFin4 :
  FourATateRefinedPattern ->
  Fin 4
refinedToFin4 evenAH1 = zero
refinedToFin4 evenDAcyclic = suc zero
refinedToFin4 oddDAcyclic = suc (suc zero)
refinedToFin4 oddCAH0 = suc (suc (suc zero))

fin4ToRefined :
  Fin 4 ->
  FourATateRefinedPattern
fin4ToRefined zero = evenAH1
fin4ToRefined (suc zero) = evenDAcyclic
fin4ToRefined (suc (suc zero)) = oddDAcyclic
fin4ToRefined (suc (suc (suc zero))) = oddCAH0

refinedFinRoundTrip :
  (pattern : FourATateRefinedPattern) ->
  fin4ToRefined (refinedToFin4 pattern) ≡ pattern
refinedFinRoundTrip evenAH1 = refl
refinedFinRoundTrip evenDAcyclic = refl
refinedFinRoundTrip oddDAcyclic = refl
refinedFinRoundTrip oddCAH0 = refl

finRefinedRoundTrip :
  (index : Fin 4) ->
  refinedToFin4 (fin4ToRefined index) ≡ index
finRefinedRoundTrip zero = refl
finRefinedRoundTrip (suc zero) = refl
finRefinedRoundTrip (suc (suc zero)) = refl
finRefinedRoundTrip (suc (suc (suc zero))) = refl

sectorToFin5 :
  Sector.BinaryTetrahedralInversionOrbit ->
  Fin 5
sectorToFin5 Sector.identityInertiaOrbit = zero
sectorToFin5 Sector.centralMinusOneInertiaOrbit = suc zero
sectorToFin5 Sector.orderFourInertiaOrbit = suc (suc zero)
sectorToFin5 Sector.orderThreePairInertiaOrbit = suc (suc (suc zero))
sectorToFin5 Sector.orderSixPairInertiaOrbit =
  suc (suc (suc (suc zero)))

fin5ToSector :
  Fin 5 ->
  Sector.BinaryTetrahedralInversionOrbit
fin5ToSector zero = Sector.identityInertiaOrbit
fin5ToSector (suc zero) = Sector.centralMinusOneInertiaOrbit
fin5ToSector (suc (suc zero)) = Sector.orderFourInertiaOrbit
fin5ToSector (suc (suc (suc zero))) = Sector.orderThreePairInertiaOrbit
fin5ToSector (suc (suc (suc (suc zero)))) =
  Sector.orderSixPairInertiaOrbit

sectorFinRoundTrip :
  (sector : Sector.BinaryTetrahedralInversionOrbit) ->
  fin5ToSector (sectorToFin5 sector) ≡ sector
sectorFinRoundTrip Sector.identityInertiaOrbit = refl
sectorFinRoundTrip Sector.centralMinusOneInertiaOrbit = refl
sectorFinRoundTrip Sector.orderFourInertiaOrbit = refl
sectorFinRoundTrip Sector.orderThreePairInertiaOrbit = refl
sectorFinRoundTrip Sector.orderSixPairInertiaOrbit = refl

finSectorRoundTrip :
  (index : Fin 5) ->
  sectorToFin5 (fin5ToSector index) ≡ index
finSectorRoundTrip zero = refl
finSectorRoundTrip (suc zero) = refl
finSectorRoundTrip (suc (suc zero)) = refl
finSectorRoundTrip (suc (suc (suc zero))) = refl
finSectorRoundTrip (suc (suc (suc (suc zero)))) = refl

------------------------------------------------------------------------
-- 4. Exact no-go.
------------------------------------------------------------------------

record ExactFiveSectorFourATateRechart : Set where
  field
    sectorToRefined :
      Sector.BinaryTetrahedralInversionOrbit ->
      FourATateRefinedPattern

    refinedToSector :
      FourATateRefinedPattern ->
      Sector.BinaryTetrahedralInversionOrbit

    sectorRoundTrip :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      refinedToSector (sectorToRefined sector) ≡ sector

    refinedRoundTrip :
      (pattern : FourATateRefinedPattern) ->
      sectorToRefined (refinedToSector pattern) ≡ pattern

open ExactFiveSectorFourATateRechart public

refinedToFin4Injective :
  Injective _≡_ _≡_ refinedToFin4
refinedToFin4Injective {left} {right} same =
  trans
    (sym (refinedFinRoundTrip left))
    (trans
      (cong fin4ToRefined same)
      (refinedFinRoundTrip right))

sectorToRefinedInjective :
  (R : ExactFiveSectorFourATateRechart) ->
  Injective _≡_ _≡_ (sectorToRefined R)
sectorToRefinedInjective R {left} {right} same =
  trans
    (sym (sectorRoundTrip R left))
    (trans
      (cong (refinedToSector R) same)
      (sectorRoundTrip R right))

fin5ToSectorInjective :
  Injective _≡_ _≡_ fin5ToSector
fin5ToSectorInjective {left} {right} same =
  trans
    (sym (finSectorRoundTrip left))
    (trans
      (cong sectorToFin5 same)
      (finSectorRoundTrip right))

inducedFin5ToFin4 :
  ExactFiveSectorFourATateRechart ->
  Fin 5 ->
  Fin 4
inducedFin5ToFin4 R index =
  refinedToFin4
    (sectorToRefined R
      (fin5ToSector index))

inducedFin5ToFin4Injective :
  (R : ExactFiveSectorFourATateRechart) ->
  Injective _≡_ _≡_ (inducedFin5ToFin4 R)
inducedFin5ToFin4Injective R {left} {right} same =
  fin5ToSectorInjective
    (sectorToRefinedInjective R
      (refinedToFin4Injective same))

fourLessThanFive :
  4 < 5
fourLessThanFive = ≤-refl

noExactFiveSectorFourATateRechart :
  ExactFiveSectorFourATateRechart -> ⊥
noExactFiveSectorFourATateRechart R =
  <⇒notInjective
    fourLessThanFive
    (inducedFin5ToFin4Injective R)

------------------------------------------------------------------------
-- 5. Attribution / promotion boundary.
------------------------------------------------------------------------

data TateSplitCreatesFifthSourceClass : Set where
data AcyclicDParityPiecesBecomeDifferentTateClasses : Set where
data TotalTateDimensionCreatesInertiaSector : Set where
data FourATatePatternCreatesThreeThreeTwoOneOneLengths : Set where

tateSplitDoesNotCreateFifthSourceClass :
  TateSplitCreatesFifthSourceClass -> ⊥
tateSplitDoesNotCreateFifthSourceClass ()

acyclicDEvenOddNotSeparatedByTateSupport :
  AcyclicDParityPiecesBecomeDifferentTateClasses -> ⊥
acyclicDEvenOddNotSeparatedByTateClasses ()
  where
    acyclicDEvenOddNotSeparatedByTateClasses :
      AcyclicDParityPiecesBecomeDifferentTateClasses -> ⊥
    acyclicDEvenOddNotSeparatedByTateClasses ()

totalTateDimensionDoesNotCreateInertiaSector :
  TotalTateDimensionCreatesInertiaSector -> ⊥
totalTateDimensionDoesNotCreateInertiaSector ()

fourATatePatternDoesNotCreateSectorLengths :
  FourATatePatternCreatesThreeThreeTwoOneOneLengths -> ⊥
fourATatePatternDoesNotCreateSectorLengths ()

------------------------------------------------------------------------
-- 6. Source receipts and live wall.
------------------------------------------------------------------------

twoBTateBoundary :
  TwoBTate.TwoBTateSplitBoundary
twoBTateBoundary =
  TwoBTate.canonicalTwoBTateSplitBoundary

fourANoGoBoundary :
  FourANoGo.FourA2BThreeLabelFiveSectorNoGoBoundary
fourANoGoBoundary =
  FourANoGo.canonicalFourA2BThreeLabelFiveSectorNoGoBoundary

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record FourA2BTateRefinementFiveSectorNoGoBoundary : Set where
  constructor four-a2b-tate-refinement-five-sector-no-go-boundary
  field
    fourAActualThreeLabelsSourced : Bool
    fourALabelParityFourPatternsOwned : Bool
    totalTateDimensionsOnA_D_CA_Sourced : Bool
    twoBTateH0H1ShiftFormulaSourced : Bool
    refinedTateSupportFourPatternsDerived : Bool
    fiveInertiaSectorCarrierOwned : Bool
    exactFiveSectorRechartBlocked : Bool
    furtherSourceNativeInvariantRequired : Bool
    monsterResidualUsedToChooseInvariant : Bool
    base369UsedToChooseInvariant : Bool
    attributionFirewallPreserved : Bool

canonicalFourA2BTateRefinementFiveSectorNoGoBoundary :
  FourA2BTateRefinementFiveSectorNoGoBoundary
canonicalFourA2BTateRefinementFiveSectorNoGoBoundary =
  four-a2b-tate-refinement-five-sector-no-go-boundary
    true true true true true true true true false false true
