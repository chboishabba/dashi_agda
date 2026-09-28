module DASHI.Moonshine.OggSSPSmallPrimeArichetaIgusaBadLevelExtensionExact where

------------------------------------------------------------------------
-- ARICHETA x IGUSA BAD-LEVEL EXTENSION
--
-- PURPOSE
--
-- The strongest source-backed localization of the small-prime wall is the
-- intersection of TWO independently open p|N extensions:
--
--   (A) Aricheta:
--       supersingular level structure <-> Monster-centralizer Fricke data is
--       proved for p not dividing N; Remark 3.5 explicitly asks for the p|N
--       extension.
--
--   (B) Kobin--Zureick-Brown / Katz--Mazur:
--       p|N wild modular geometry should be treated through the Igusa p-power
--       tower; the 2025 wild-stack paper explicitly leaves the comparison of
--       that Igusa geometry with its wild root-stack presentation undeveloped.
--
-- The 2B and 3B lanes are exactly diagonal:
--
--       p=2, N=2
--       p=3, N=3.
--
-- DASHI CONTRIBUTION
--
-- Require ONE bad-level object to inhabit both extension problems.  This is
-- strictly geometric/recognitional and deliberately does NOT contain the final
-- 10/2 valuation authority: after this comparison is built, the same object
-- must still acquire the corrected q-expansion/divisor valuation and
-- twisted/generalized-moonshine trace authority.
--
-- ATTRIBUTION FIREWALL
--
-- Aricheta owns the off-diagonal centralizer theorem and open p|N question.
-- Kobin--Zureick-Brown own the wild-stack results and proposed-but-unrealized
-- Igusa strategy at p|N.
-- Katz--Mazur own the classical Igusa/p-power-level geometry.
-- DASHI owns only this intersection requirement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallPrimeArichetaBadLevelDiagonalCutsetExact as Aricheta
import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact as Igusa
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Same-object bad-level extension.
------------------------------------------------------------------------

record ArichetaIgusaBadLevelExtensionAuthority : Set₁ where
  field
    arichetaExtension :
      Aricheta.BadLevelArichetaCentralizerExtensionAuthority

    p2IgusaComparison :
      Igusa.BadLevelIgusaRootStackComparison Igusa.pTwo

    p3IgusaComparison :
      Igusa.BadLevelIgusaRootStackComparison Igusa.pThree

    BadLevelObject :
      Set

    p2BadLevelObject :
      BadLevelObject

    p3BadLevelObject :
      BadLevelObject

    toArichetaObject :
      BadLevelObject ->
      Aricheta.BadLevelObject arichetaExtension

    toP2IgusaPrimeLevelObject :
      BadLevelObject ->
      Igusa.IgusaPrimeLevelObject p2IgusaComparison

    toP2IgusaPrimeSquareObject :
      BadLevelObject ->
      Igusa.IgusaPrimeSquareObject p2IgusaComparison

    toP2WildLocalObject :
      BadLevelObject ->
      Igusa.WildLocalObject p2IgusaComparison

    toP3IgusaPrimeLevelObject :
      BadLevelObject ->
      Igusa.IgusaPrimeLevelObject p3IgusaComparison

    toP3IgusaPrimeSquareObject :
      BadLevelObject ->
      Igusa.IgusaPrimeSquareObject p3IgusaComparison

    toP3WildLocalObject :
      BadLevelObject ->
      Igusa.WildLocalObject p3IgusaComparison

    p2SameObjectMapsToArichetaAndIgusa :
      Bool
    p2SameObjectMapsToArichetaAndIgusaIsTrue :
      p2SameObjectMapsToArichetaAndIgusa ≡ true

    p3SameObjectMapsToArichetaAndIgusa :
      Bool
    p3SameObjectMapsToArichetaAndIgusaIsTrue :
      p3SameObjectMapsToArichetaAndIgusa ≡ true

    igusaRootStackComparisonPaysBadLevelGeometry :
      Bool
    igusaRootStackComparisonPaysBadLevelGeometryIsTrue :
      igusaRootStackComparisonPaysBadLevelGeometry ≡ true

    arichetaCentralizerRecognitionUsesSameBadLevelGeometry :
      Bool
    arichetaCentralizerRecognitionUsesSameBadLevelGeometryIsTrue :
      arichetaCentralizerRecognitionUsesSameBadLevelGeometry ≡ true

    p2FrickeCompatibilityAgrees :
      Bool
    p2FrickeCompatibilityAgreesIsTrue :
      p2FrickeCompatibilityAgrees ≡ true

    p3FrickeCompatibilityAgrees :
      Bool
    p3FrickeCompatibilityAgreesIsTrue :
      p3FrickeCompatibilityAgrees ≡ true

    constructionIndependentOfTargetTenTwo :
      Bool
    constructionIndependentOfTargetTenTwoIsTrue :
      constructionIndependentOfTargetTenTwo ≡ true

open ArichetaIgusaBadLevelExtensionAuthority public

------------------------------------------------------------------------
-- 2. Projection adapters.
------------------------------------------------------------------------

asArichetaExtension :
  ArichetaIgusaBadLevelExtensionAuthority ->
  Aricheta.BadLevelArichetaCentralizerExtensionAuthority
asArichetaExtension =
  arichetaExtension

asP2IgusaComparison :
  ArichetaIgusaBadLevelExtensionAuthority ->
  Igusa.BadLevelIgusaRootStackComparison Igusa.pTwo
asP2IgusaComparison =
  p2IgusaComparison

asP3IgusaComparison :
  ArichetaIgusaBadLevelExtensionAuthority ->
  Igusa.BadLevelIgusaRootStackComparison Igusa.pThree
asP3IgusaComparison =
  p3IgusaComparison

------------------------------------------------------------------------
-- 3. Source-scope firewalls.
------------------------------------------------------------------------

data ArichetaOffDiagonalTheoremConstructsIntersection : Set where
data KZBWildStackPaperConstructsIntersection : Set where
data KatzMazurIgusaGeometryConstructsMonsterCentralizerBridge : Set where
data SeparateBadLevelSolutionsAutomaticallySameObject : Set where
data SameObjectExtensionAutomaticallyProvesValuationTenTwo : Set where

arichetaOffDiagonalDoesNotConstructIntersection :
  ArichetaOffDiagonalTheoremConstructsIntersection -> ⊥
arichetaOffDiagonalDoesNotConstructIntersection ()

kzbWildStackPaperDoesNotConstructIntersection :
  KZBWildStackPaperConstructsIntersection -> ⊥
kzbWildStackPaperDoesNotConstructIntersection ()

katzMazurDoesNotConstructMonsterCentralizerBridge :
  KatzMazurIgusaGeometryConstructsMonsterCentralizerBridge -> ⊥
katzMazurDoesNotConstructMonsterCentralizerBridge ()

separateBadLevelSolutionsDoNotAutomaticallyCoincide :
  SeparateBadLevelSolutionsAutomaticallySameObject -> ⊥
separateBadLevelSolutionsDoNotAutomaticallyCoincide ()

sameObjectExtensionDoesNotAutomaticallyProveValuation :
  SameObjectExtensionAutomaticallyProvesValuationTenTwo -> ⊥
sameObjectExtensionDoesNotAutomaticallyProveValuation ()

------------------------------------------------------------------------
-- 4. Live theorem wall.
------------------------------------------------------------------------

data ArichetaIgusaBadLevelExtensionAuthorityInhabited : Set where

arichetaIgusaBadLevelExtensionStillOpen :
  ArichetaIgusaBadLevelExtensionAuthorityInhabited -> ⊥
arichetaIgusaBadLevelExtensionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record ArichetaIgusaBadLevelExtensionBoundary : Set where
  constructor aricheta-igusa-bad-level-extension-boundary
  field
    arichetaOffDiagonalBridgeSourced : Bool
    arichetaPdividesNExtensionOpen : Bool
    kzbBadLevelNeedsMoreCareSourced : Bool
    kzbIgusaStrategySuggested : Bool
    kzbIgusaRootStackComparisonUnrealized : Bool
    katzMazurIgusaGeometryAvailable : Bool
    sameObjectIntersectionRequired : Bool
    badLevelFrickeCompatibilityRequired : Bool
    targetIndependentConstructionRequired : Bool
    valuationTenTwoStillSeparatePayment : Bool
    authorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalArichetaIgusaBadLevelExtensionBoundary :
  ArichetaIgusaBadLevelExtensionBoundary
canonicalArichetaIgusaBadLevelExtensionBoundary =
  aricheta-igusa-bad-level-extension-boundary
    true true true true true true
    true true true true false true
