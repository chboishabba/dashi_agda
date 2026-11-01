module DASHI.Moonshine.OggSSPP2UranoParityFiveSectorNoGoExact where

------------------------------------------------------------------------
-- p=2 URANO PARITY/TAG FOUR-vs-FIVE NO-GO
--
-- SOURCE INPUT
--
-- Urano supplies only two parity exclusions:
--
--   odd degree  forbids trivial Z_2,
--   even degree forbids augmentation quotient I_2.
--
-- On the coarse source language
--
--   DegreeParity x {trivial Z_2, I_2, other}
--
-- this leaves FOUR syntactically non-forbidden patterns:
--
--   even/trivial,
--   even/other,
--   odd/I_2,
--   odd/other.
--
-- IMPORTANT:
-- this is a syntactic admissibility carrier.  Urano does NOT claim that all
-- four patterns occur, nor that they exhaust actual indecomposable modules.
--
-- TARGET INPUT
--
-- The p=2 supersingular inertia analysis has FIVE sectors.
--
-- RESULT
--
-- Finite pigeonhole proves there is no exact two-sided rechart from those
-- five sectors to the four coarse Urano parity/tag patterns.
--
-- Therefore the p=2 localization needs at least one further source-native
-- invariant beyond the currently sourced parity/tag language.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (<⇒notInjective)
open import Function.Definitions using (Injective)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact coarse non-forbidden source-pattern carrier.
------------------------------------------------------------------------

data UranoCoarseAdmissiblePattern : Set where
  evenTrivialPattern :
    UranoCoarseAdmissiblePattern

  evenOtherPattern :
    UranoCoarseAdmissiblePattern

  oddAugmentationPattern :
    UranoCoarseAdmissiblePattern

  oddOtherPattern :
    UranoCoarseAdmissiblePattern

patternParity :
  UranoCoarseAdmissiblePattern ->
  Urano.DegreeParity
patternParity evenTrivialPattern = Urano.evenDegree
patternParity evenOtherPattern = Urano.evenDegree
patternParity oddAugmentationPattern = Urano.oddDegree
patternParity oddOtherPattern = Urano.oddDegree

patternTag :
  UranoCoarseAdmissiblePattern ->
  Urano.TwoBModuleTag
patternTag evenTrivialPattern = Urano.trivialZ2
patternTag evenOtherPattern = Urano.otherIntegralModuleTag
patternTag oddAugmentationPattern = Urano.augmentationQuotientI2
patternTag oddOtherPattern = Urano.otherIntegralModuleTag

patternIsNotForbidden :
  (pattern : UranoCoarseAdmissiblePattern) ->
  Urano.TwoBSourceForbidden
    (patternParity pattern)
    (patternTag pattern)
  ->
  ⊥
patternIsNotForbidden evenTrivialPattern ()
patternIsNotForbidden evenOtherPattern ()
patternIsNotForbidden oddAugmentationPattern ()
patternIsNotForbidden oddOtherPattern ()

------------------------------------------------------------------------
-- 2. Exact finite enumerations.
------------------------------------------------------------------------

patternToFin4 :
  UranoCoarseAdmissiblePattern ->
  Fin 4
patternToFin4 evenTrivialPattern = zero
patternToFin4 evenOtherPattern = suc zero
patternToFin4 oddAugmentationPattern = suc (suc zero)
patternToFin4 oddOtherPattern = suc (suc (suc zero))

fin4ToPattern :
  Fin 4 ->
  UranoCoarseAdmissiblePattern
fin4ToPattern zero = evenTrivialPattern
fin4ToPattern (suc zero) = evenOtherPattern
fin4ToPattern (suc (suc zero)) = oddAugmentationPattern
fin4ToPattern (suc (suc (suc zero))) = oddOtherPattern

patternFinRoundTrip :
  (pattern : UranoCoarseAdmissiblePattern) ->
  fin4ToPattern (patternToFin4 pattern) ≡ pattern
patternFinRoundTrip evenTrivialPattern = refl
patternFinRoundTrip evenOtherPattern = refl
patternFinRoundTrip oddAugmentationPattern = refl
patternFinRoundTrip oddOtherPattern = refl

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
-- 3. Hypothetical exact rechart.
------------------------------------------------------------------------

record ExactFiveSectorUranoPatternRechart : Set where
  field
    sectorToPattern :
      Sector.BinaryTetrahedralInversionOrbit ->
      UranoCoarseAdmissiblePattern

    patternToSector :
      UranoCoarseAdmissiblePattern ->
      Sector.BinaryTetrahedralInversionOrbit

    sectorRoundTrip :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      patternToSector (sectorToPattern sector) ≡ sector

    patternRoundTrip :
      (pattern : UranoCoarseAdmissiblePattern) ->
      sectorToPattern (patternToSector pattern) ≡ pattern

open ExactFiveSectorUranoPatternRechart public

------------------------------------------------------------------------
-- 4. A rechart would induce an injection Fin 5 -> Fin 4.
------------------------------------------------------------------------

patternToFin4Injective :
  Injective _≡_ _≡_ patternToFin4
patternToFin4Injective {left} {right} same =
  trans
    (sym (patternFinRoundTrip left))
    (trans
      (cong fin4ToPattern same)
      (patternFinRoundTrip right))

sectorToPatternInjective :
  (R : ExactFiveSectorUranoPatternRechart) ->
  Injective _≡_ _≡_ (sectorToPattern R)
sectorToPatternInjective R {left} {right} same =
  trans
    (sym (sectorRoundTrip R left))
    (trans
      (cong (patternToSector R) same)
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
  ExactFiveSectorUranoPatternRechart ->
  Fin 5 ->
  Fin 4
inducedFin5ToFin4 R index =
  patternToFin4
    (sectorToPattern R
      (fin5ToSector index))

inducedFin5ToFin4Injective :
  (R : ExactFiveSectorUranoPatternRechart) ->
  Injective _≡_ _≡_ (inducedFin5ToFin4 R)
inducedFin5ToFin4Injective R {left} {right} same =
  fin5ToSectorInjective
    (sectorToPatternInjective R
      (patternToFin4Injective same))

fourLessThanFive :
  4 < 5
fourLessThanFive = ≤-refl

noExactFiveSectorUranoPatternRechart :
  ExactFiveSectorUranoPatternRechart -> ⊥
noExactFiveSectorUranoPatternRechart R =
  <⇒notInjective
    fourLessThanFive
    (inducedFin5ToFin4Injective R)

------------------------------------------------------------------------
-- 5. Interpretation / attribution boundary.
------------------------------------------------------------------------

data FourPatternsAllOccurInMoonshine : Set where
data UranoParityLanguageAlreadyContainsFiveSectorInvariant : Set where
data FiveSectorGeometryDeterminesMissingSourceInvariant : Set where
data MonsterResidualTenDeterminesMissingSourceInvariant : Set where

sourceDoesNotClaimAllFourPatternsOccur :
  FourPatternsAllOccurInMoonshine -> ⊥
sourceDoesNotClaimAllFourPatternsOccur ()

uranoParityLanguageDoesNotAlreadyContainFiveSectorInvariant :
  UranoParityLanguageAlreadyContainsFiveSectorInvariant -> ⊥
uranoParityLanguageDoesNotAlreadyContainFiveSectorInvariant ()

geometryDoesNotManufactureMissingSourceInvariant :
  FiveSectorGeometryDeterminesMissingSourceInvariant -> ⊥
geometryDoesNotManufactureMissingSourceInvariant ()

monsterResidualDoesNotManufactureMissingSourceInvariant :
  MonsterResidualTenDeterminesMissingSourceInvariant -> ⊥
monsterResidualDoesNotManufactureMissingSourceInvariant ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2UranoParityFiveSectorNoGoBoundary : Set where
  constructor p2-urano-parity-five-sector-no-go-boundary
  field
    uranoParityExclusionsSourced : Bool
    coarseNonForbiddenPatternCarrierHasFourLabels : Bool
    fiveInertiaSectorCarrierOwned : Bool
    exactFourAndFiveEnumerationsConstructed : Bool
    exactTwoSidedRechartBlockedByPigeonhole : Bool
    allFourPatternsAssertedToOccur : Bool
    extraSourceNativeInvariantRequired : Bool
    monsterResidualUsedToDefineMissingInvariant : Bool
    attributionFirewallPreserved : Bool

canonicalP2UranoParityFiveSectorNoGoBoundary :
  P2UranoParityFiveSectorNoGoBoundary
canonicalP2UranoParityFiveSectorNoGoBoundary =
  p2-urano-parity-five-sector-no-go-boundary
    true true true true true false true false true
