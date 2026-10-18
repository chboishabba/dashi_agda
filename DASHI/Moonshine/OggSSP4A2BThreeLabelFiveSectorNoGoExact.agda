module DASHI.Moonshine.OggSSP4A2BThreeLabelFiveSectorNoGoExact where

------------------------------------------------------------------------
-- 4A -> 2B THREE-LABEL / FOUR-PARITY-PATTERN vs FIVE-SECTOR NO-GO
--
-- EXTERNAL SOURCE: Carnahan--Urano, Section 6.
--
-- Theorem 6.5:
--   for a 4A generator, the integral Moonshine module uses ONLY
--
--     A, D, C^A.
--
-- Lemma 6.4 gives the square-subgroup restrictions:
--
--     A   |_<g^2> = Z
--     D   |_<g^2> = 2 Z[H]
--     C^A |_<g^2> = Z[H] + I,
--
-- where H=<g^2> and I is the rank-one sign module.
--
-- Their degree-parity list further implies, after intersecting with Theorem
-- 6.5, only four source-native label/parity possibilities:
--
--     even/A, even/D, odd/D, odd/C^A.
--
-- DASHI RESULT:
--
-- Neither the three actual 4A labels nor the four label+parity patterns admit
-- an exact two-sided rechart with the FIVE characteristic-2 inertia sectors.
-- Both no-goes are finite pigeonhole theorems.
--
-- Therefore the missing p=2 classifier requires at least one additional
-- source-native coordinate beyond restricted 4A type plus degree parity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (<⇒notInjective)
open import Function.Definitions using (Injective)

import DASHI.Moonshine.OggSSP4A2BIntegralRestrictionRefinementExact as FourA
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. The actual three 4A indecomposables appearing in V^natural_Z.
------------------------------------------------------------------------

data FourAActualIndecomposable : Set where
  moduleA :
    FourAActualIndecomposable
  moduleD :
    FourAActualIndecomposable
  moduleCA :
    FourAActualIndecomposable

data RestrictedTwoBModuleShape : Set where
  restrictedTrivialZ :
    RestrictedTwoBModuleShape
  restrictedDoubleRegularZH :
    RestrictedTwoBModuleShape
  restrictedRegularPlusSign :
    RestrictedTwoBModuleShape

restrictedShape :
  FourAActualIndecomposable ->
  RestrictedTwoBModuleShape
restrictedShape moduleA = restrictedTrivialZ
restrictedShape moduleD = restrictedDoubleRegularZH
restrictedShape moduleCA = restrictedRegularPlusSign

------------------------------------------------------------------------
-- 2. Exact source-supported label/parity carrier.
------------------------------------------------------------------------

data FourALabelParityPattern : Set where
  evenA :
    FourALabelParityPattern
  evenD :
    FourALabelParityPattern
  oddD :
    FourALabelParityPattern
  oddCA :
    FourALabelParityPattern

patternLabel :
  FourALabelParityPattern ->
  FourAActualIndecomposable
patternLabel evenA = moduleA
patternLabel evenD = moduleD
patternLabel oddD = moduleD
patternLabel oddCA = moduleCA

patternParity :
  FourALabelParityPattern ->
  Urano.DegreeParity
patternParity evenA = Urano.evenDegree
patternParity evenD = Urano.evenDegree
patternParity oddD = Urano.oddDegree
patternParity oddCA = Urano.oddDegree

------------------------------------------------------------------------
-- 3. Exact finite enumerations: three labels, four label/parity patterns,
--    five geometric sectors.
------------------------------------------------------------------------

labelToFin3 :
  FourAActualIndecomposable ->
  Fin 3
labelToFin3 moduleA = zero
labelToFin3 moduleD = suc zero
labelToFin3 moduleCA = suc (suc zero)

fin3ToLabel :
  Fin 3 ->
  FourAActualIndecomposable
fin3ToLabel zero = moduleA
fin3ToLabel (suc zero) = moduleD
fin3ToLabel (suc (suc zero)) = moduleCA

labelFinRoundTrip :
  (label : FourAActualIndecomposable) ->
  fin3ToLabel (labelToFin3 label) ≡ label
labelFinRoundTrip moduleA = refl
labelFinRoundTrip moduleD = refl
labelFinRoundTrip moduleCA = refl

finLabelRoundTrip :
  (index : Fin 3) ->
  labelToFin3 (fin3ToLabel index) ≡ index
finLabelRoundTrip zero = refl
finLabelRoundTrip (suc zero) = refl
finLabelRoundTrip (suc (suc zero)) = refl

patternToFin4 :
  FourALabelParityPattern ->
  Fin 4
patternToFin4 evenA = zero
patternToFin4 evenD = suc zero
patternToFin4 oddD = suc (suc zero)
patternToFin4 oddCA = suc (suc (suc zero))

fin4ToPattern :
  Fin 4 ->
  FourALabelParityPattern
fin4ToPattern zero = evenA
fin4ToPattern (suc zero) = evenD
fin4ToPattern (suc (suc zero)) = oddD
fin4ToPattern (suc (suc (suc zero))) = oddCA

patternFinRoundTrip :
  (pattern : FourALabelParityPattern) ->
  fin4ToPattern (patternToFin4 pattern) ≡ pattern
patternFinRoundTrip evenA = refl
patternFinRoundTrip evenD = refl
patternFinRoundTrip oddD = refl
patternFinRoundTrip oddCA = refl

finPatternRoundTrip :
  (index : Fin 4) ->
  patternToFin4 (fin4ToPattern index) ≡ index
finPatternRoundTrip zero = refl
finPatternRoundTrip (suc zero) = refl
finPatternRoundTrip (suc (suc zero)) = refl
finPatternRoundTrip (suc (suc (suc zero))) = refl

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
-- 4. Generic injection helpers.
------------------------------------------------------------------------

labelToFin3Injective :
  Injective _≡_ _≡_ labelToFin3
labelToFin3Injective {left} {right} same =
  trans
    (sym (labelFinRoundTrip left))
    (trans
      (cong fin3ToLabel same)
      (labelFinRoundTrip right))

patternToFin4Injective :
  Injective _≡_ _≡_ patternToFin4
patternToFin4Injective {left} {right} same =
  trans
    (sym (patternFinRoundTrip left))
    (trans
      (cong fin4ToPattern same)
      (patternFinRoundTrip right))

fin5ToSectorInjective :
  Injective _≡_ _≡_ fin5ToSector
fin5ToSectorInjective {left} {right} same =
  trans
    (sym (finSectorRoundTrip left))
    (trans
      (cong sectorToFin5 same)
      (finSectorRoundTrip right))

------------------------------------------------------------------------
-- 5. Three-label no-go.
------------------------------------------------------------------------

record ExactFiveSectorFourALabelRechart : Set where
  field
    sectorToLabel :
      Sector.BinaryTetrahedralInversionOrbit ->
      FourAActualIndecomposable

    labelToSector :
      FourAActualIndecomposable ->
      Sector.BinaryTetrahedralInversionOrbit

    sectorRoundTrip :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      labelToSector (sectorToLabel sector) ≡ sector

    labelRoundTrip :
      (label : FourAActualIndecomposable) ->
      sectorToLabel (labelToSector label) ≡ label

open ExactFiveSectorFourALabelRechart public

sectorToLabelInjective :
  (R : ExactFiveSectorFourALabelRechart) ->
  Injective _≡_ _≡_ (sectorToLabel R)
sectorToLabelInjective R {left} {right} same =
  trans
    (sym (sectorRoundTrip R left))
    (trans
      (cong (labelToSector R) same)
      (sectorRoundTrip R right))

inducedFin5ToFin3 :
  ExactFiveSectorFourALabelRechart ->
  Fin 5 ->
  Fin 3
inducedFin5ToFin3 R index =
  labelToFin3 (sectorToLabel R (fin5ToSector index))

inducedFin5ToFin3Injective :
  (R : ExactFiveSectorFourALabelRechart) ->
  Injective _≡_ _≡_ (inducedFin5ToFin3 R)
inducedFin5ToFin3Injective R {left} {right} same =
  fin5ToSectorInjective
    (sectorToLabelInjective R
      (labelToFin3Injective same))

threeLessThanFive :
  3 < 5
threeLessThanFive = ≤-refl

noExactFiveSectorFourALabelRechart :
  ExactFiveSectorFourALabelRechart -> ⊥
noExactFiveSectorFourALabelRechart R =
  <⇒notInjective
    threeLessThanFive
    (inducedFin5ToFin3Injective R)

------------------------------------------------------------------------
-- 6. Even label+parity remains only four-way.
------------------------------------------------------------------------

record ExactFiveSectorFourAPatternRechart : Set where
  field
    sectorToPattern :
      Sector.BinaryTetrahedralInversionOrbit ->
      FourALabelParityPattern

    patternToSector :
      FourALabelParityPattern ->
      Sector.BinaryTetrahedralInversionOrbit

    sectorRoundTrip :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      patternToSector (sectorToPattern sector) ≡ sector

    patternRoundTrip :
      (pattern : FourALabelParityPattern) ->
      sectorToPattern (patternToSector pattern) ≡ pattern

open ExactFiveSectorFourAPatternRechart public

sectorToPatternInjective :
  (R : ExactFiveSectorFourAPatternRechart) ->
  Injective _≡_ _≡_ (sectorToPattern R)
sectorToPatternInjective R {left} {right} same =
  trans
    (sym (sectorRoundTrip R left))
    (trans
      (cong (patternToSector R) same)
      (sectorRoundTrip R right))

inducedFin5ToFin4 :
  ExactFiveSectorFourAPatternRechart ->
  Fin 5 ->
  Fin 4
inducedFin5ToFin4 R index =
  patternToFin4 (sectorToPattern R (fin5ToSector index))

inducedFin5ToFin4Injective :
  (R : ExactFiveSectorFourAPatternRechart) ->
  Injective _≡_ _≡_ (inducedFin5ToFin4 R)
inducedFin5ToFin4Injective R {left} {right} same =
  fin5ToSectorInjective
    (sectorToPatternInjective R
      (patternToFin4Injective same))

fourLessThanFive :
  4 < 5
fourLessThanFive = ≤-refl

noExactFiveSectorFourAPatternRechart :
  ExactFiveSectorFourAPatternRechart -> ⊥
noExactFiveSectorFourAPatternRechart R =
  <⇒notInjective
    fourLessThanFive
    (inducedFin5ToFin4Injective R)

------------------------------------------------------------------------
-- 7. Source receipts and interpretation.
------------------------------------------------------------------------

fourARestrictionBoundary :
  FourA.FourA2BRestrictionRefinementBoundary
fourARestrictionBoundary =
  FourA.canonicalFourA2BRestrictionRefinementBoundary

data FourALabelAloneClassifiesFiveSectors : Set where
data FourALabelParityClassifiesFiveSectors : Set where
data ThreeIndecomposablesMeanThreeInertiaSectors : Set where
data RestrictionShapesCarryBase369Semantics : Set where

fourALabelAloneDoesNotClassifyFiveSectors :
  FourALabelAloneClassifiesFiveSectors -> ⊥
fourALabelAloneDoesNotClassifyFiveSectors ()

fourALabelParityDoesNotClassifyFiveSectors :
  FourALabelParityClassifiesFiveSectors -> ⊥
fourALabelParityDoesNotClassifyFiveSectors ()

threeIndecomposablesDoNotMeanThreeInertiaSectors :
  ThreeIndecomposablesMeanThreeInertiaSectors -> ⊥
threeIndecomposablesDoNotMeanThreeInertiaSectors ()

restrictionShapesDoNotAcquireBase369Semantics :
  RestrictionShapesCarryBase369Semantics -> ⊥
restrictionShapesDoNotAcquireBase369Semantics ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record FourA2BThreeLabelFiveSectorNoGoBoundary : Set where
  constructor four-a2b-three-label-five-sector-no-go-boundary
  field
    theoremSixFiveThreeActualIndecomposablesSourced : Bool
    lemmaSixFourSquareSubgroupRestrictionsSourced : Bool
    paritySupportIntersectedWithThreeLabels : Bool
    actualFourALabelCarrierHasThreeLabels : Bool
    actualLabelParityCarrierHasFourPatterns : Bool
    fiveInertiaSectorCarrierOwned : Bool
    threeLabelExactRechartBlocked : Bool
    fourPatternExactRechartBlocked : Bool
    furtherIndependentSourceCoordinateRequired : Bool
    monsterResidualUsedToChooseFurtherCoordinate : Bool
    base369UsedToChooseFurtherCoordinate : Bool
    attributionFirewallPreserved : Bool

canonicalFourA2BThreeLabelFiveSectorNoGoBoundary :
  FourA2BThreeLabelFiveSectorNoGoBoundary
canonicalFourA2BThreeLabelFiveSectorNoGoBoundary =
  four-a2b-three-label-five-sector-no-go-boundary
    true true true true true true true true true false false true
