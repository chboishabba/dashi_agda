module DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact where

------------------------------------------------------------------------
-- WILD-LAYER x LOCAL-SECTOR PRODUCT CANDIDATE
--
-- EXTERNAL WILD-STACK INPUT
--
-- Kobin--Zureick-Brown, Proposition 2.9:
--
--   p=3:
--     X(1)^rig is ONE Artin--Schreier root stack over a tame square-root stack
--     at j=0.
--
--   p=2:
--     X(1)^rig is obtained by a SEQUENCE OF TWO Artin--Schreier root stacks
--     over a tame cube-root stack at j=0.
--
-- INDEPENDENT LOCAL-SECTOR INPUT
--
--   p=2:
--     five loop-reversal orbits of binary-tetrahedral inertia.
--
--   p=3:
--     two Deligne--Rapoport local-incidence C2 orbits:
--       node, branch-pair.
--
-- DASHI CROSS-MODULE CANDIDATE
--
-- Apply the SAME structural rule at both primes:
--
--   correction multiplicity
--     = number of wild Artin--Schreier layers
--       x number of preferred local sectors.
--
-- Then:
--
--   p=2 : 2 x 5 = 10,
--   p=3 : 1 x 2 =  2.
--
-- This is the first candidate in this lane with one uniform FORM across both
-- wild primes whose two inputs are independently defined before consulting the
-- Monster exponent.
--
-- FIREWALL
--
-- Nothing here proves that one wild layer contributes one copy of every local
-- sector to a Hauptmodul/Monster valuation.  That multiplicity theorem is the
-- missing analytic bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Inertia
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Local
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Wild layer counts from the sourced local root-stack presentations.
------------------------------------------------------------------------

data WildPrime : Set where
  wildTwo wildThree : WildPrime

artinSchreierLayerCount :
  WildPrime ->
  Nat
artinSchreierLayerCount wildTwo = 2
artinSchreierLayerCount wildThree = 1

p2HasTwoWildLayers :
  artinSchreierLayerCount wildTwo ≡ 2
p2HasTwoWildLayers = refl

p3HasOneWildLayer :
  artinSchreierLayerCount wildThree ≡ 1
p3HasOneWildLayer = refl

------------------------------------------------------------------------
-- 2. Preferred local-sector ranks from independently constructed carriers.
------------------------------------------------------------------------

localSectorRank :
  WildPrime ->
  Nat
localSectorRank wildTwo = 5
localSectorRank wildThree = 2

p2LocalSectorRankIsFive :
  localSectorRank wildTwo ≡ 5
p2LocalSectorRankIsFive = refl

p3LocalSectorRankIsTwo :
  localSectorRank wildThree ≡ 2
p3LocalSectorRankIsTwo = refl

------------------------------------------------------------------------
-- 3. Uniform structural product.
------------------------------------------------------------------------

wildLayerSectorProduct :
  WildPrime ->
  Nat
wildLayerSectorProduct prime =
  artinSchreierLayerCount prime
  * localSectorRank prime

p2WildLayerSectorProductIsTen :
  wildLayerSectorProduct wildTwo ≡ 10
p2WildLayerSectorProductIsTen = refl

p3WildLayerSectorProductIsTwo :
  wildLayerSectorProduct wildThree ≡ 2
p3WildLayerSectorProductIsTwo = refl

p2ProductMatchesMonsterBridgeGap :
  wildLayerSectorProduct wildTwo
  ≡ Bridge.p2BridgeGap
p2ProductMatchesMonsterBridgeGap = refl

p3ProductMatchesMonsterBridgeGap :
  wildLayerSectorProduct wildThree
  ≡ Bridge.p3BridgeGap
p3ProductMatchesMonsterBridgeGap = refl

------------------------------------------------------------------------
-- 4. Typed carrier witnesses keep the factor counts tied to their geometry.
------------------------------------------------------------------------

data P2FiveSectorWitness : Set where
  p2IdentitySector :
    P2FiveSectorWitness
  p2CentralMinusOneSector :
    P2FiveSectorWitness
  p2OrderFourSector :
    P2FiveSectorWitness
  p2OrderThreePairSector :
    P2FiveSectorWitness
  p2OrderSixPairSector :
    P2FiveSectorWitness

data P3TwoSectorWitness : Set where
  p3NodeSector :
    P3TwoSectorWitness
  p3BranchPairSector :
    P3TwoSectorWitness

p2WitnessToInertiaOrbit :
  P2FiveSectorWitness ->
  P2Inertia.BinaryTetrahedralInversionOrbit
p2WitnessToInertiaOrbit p2IdentitySector =
  P2Inertia.identityInertiaOrbit
p2WitnessToInertiaOrbit p2CentralMinusOneSector =
  P2Inertia.centralMinusOneInertiaOrbit
p2WitnessToInertiaOrbit p2OrderFourSector =
  P2Inertia.orderFourInertiaOrbit
p2WitnessToInertiaOrbit p2OrderThreePairSector =
  P2Inertia.orderThreePairInertiaOrbit
p2WitnessToInertiaOrbit p2OrderSixPairSector =
  P2Inertia.orderSixPairInertiaOrbit

p3WitnessToLocalOrbit :
  P3TwoSectorWitness ->
  P3Local.P3LocalOrbit
p3WitnessToLocalOrbit p3NodeSector =
  P3Local.nodeOrbit
p3WitnessToLocalOrbit p3BranchPairSector =
  P3Local.branchOrbit

------------------------------------------------------------------------
-- 5. The actual missing theorem: layer-sector multiplicity -> valuation.
------------------------------------------------------------------------

record WildLayerSectorValuationAuthority : Set₁ where
  field
    LocalAnalyticContribution : Set

    p2Contribution :
      LocalAnalyticContribution

    p3Contribution :
      LocalAnalyticContribution

    valuationMultiplicity :
      WildPrime ->
      LocalAnalyticContribution ->
      Nat

    p2MultiplicityIsLayerSectorProduct :
      valuationMultiplicity wildTwo p2Contribution
      ≡ wildLayerSectorProduct wildTwo

    p3MultiplicityIsLayerSectorProduct :
      valuationMultiplicity wildThree p3Contribution
      ≡ wildLayerSectorProduct wildThree

    contributionDefinedFromWildLocalGeometry :
      Bool
    contributionDefinedFromWildLocalGeometryIsTrue :
      contributionDefinedFromWildLocalGeometry ≡ true

    oneCopyPerLayerPerSectorTheorem :
      Bool
    oneCopyPerLayerPerSectorTheoremIsTrue :
      oneCopyPerLayerPerSectorTheorem ≡ true

    contributionRefinesBothDuncanSwisherDescriptions :
      Bool
    contributionRefinesBothDuncanSwisherDescriptionsIsTrue :
      contributionRefinesBothDuncanSwisherDescriptions ≡ true

    proofIndependentOfMonsterTargetGap :
      Bool
    proofIndependentOfMonsterTargetGapIsTrue :
      proofIndependentOfMonsterTargetGap ≡ true

open WildLayerSectorValuationAuthority public

------------------------------------------------------------------------
-- 6. No fake promotion.
------------------------------------------------------------------------

data ProductCountIsPadicValuation : Set where
data RootStackLayerCountCreatesMultiplicityTheorem : Set where
data SectorRankCreatesMultiplicityTheorem : Set where
data ExactTenTwoMatchCreatesWildLayerAuthority : Set where
data KobinZureickBrownProvedMonsterCorrection : Set where

productCountIsNotPromotedToPadicValuation :
  ProductCountIsPadicValuation -> ⊥
productCountIsNotPromotedToPadicValuation ()

layerCountDoesNotCreateMultiplicityTheorem :
  RootStackLayerCountCreatesMultiplicityTheorem -> ⊥
layerCountDoesNotCreateMultiplicityTheorem ()

sectorRankDoesNotCreateMultiplicityTheorem :
  SectorRankCreatesMultiplicityTheorem -> ⊥
sectorRankDoesNotCreateMultiplicityTheorem ()

exactMatchDoesNotCreateWildLayerAuthority :
  ExactTenTwoMatchCreatesWildLayerAuthority -> ⊥
exactMatchDoesNotCreateWildLayerAuthority ()

kobinzureickBrownNotCreditedWithMonsterCorrection :
  KobinZureickBrownProvedMonsterCorrection -> ⊥
kobinzureickBrownNotCreditedWithMonsterCorrection ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record WildLayerSectorProductBoundary : Set where
  constructor wild-layer-sector-product-boundary
  field
    p2TwoArtinSchreierLayersSourced : Bool
    p3OneArtinSchreierLayerSourced : Bool
    p2FiveLocalSectorsIndependentlyGrounded : Bool
    p3TwoLocalSectorsIndependentlyGrounded : Bool
    sameProductRuleUsedAtBothPrimes : Bool
    p2ProductTenExact : Bool
    p3ProductTwoExact : Bool
    productsMatchMonsterBridgeGaps : Bool
    valuationAuthoritySpecified : Bool
    oneCopyPerLayerPerSectorTheoremProved : Bool
    analyticValuationAuthorityInhabited : Bool
    sourceCreditedWithMonsterCorrection : Bool
    attributionFirewallPreserved : Bool

canonicalWildLayerSectorProductBoundary :
  WildLayerSectorProductBoundary
canonicalWildLayerSectorProductBoundary =
  wild-layer-sector-product-boundary
    true true true true true true true true true false false false true
