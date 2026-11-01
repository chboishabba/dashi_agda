module DASHI.Physics.Closure.ShimuraTowerSpatialLatticeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Shimura tower spatial lattice receipt.
--
-- Level zero is the original three-lane seed labelling: one CM point in
-- each of the 3, 4, and 7 lanes.  Level k refines each lane by the modular
-- cover X0(3^k), X0(4^k), X0(7^k).  The spatial sites at level k are CM
-- points of X0(3^k) x X0(4^k) x X0(7^k), with count
-- psi(3^k) * psi(4^k) * psi(7^k).  At k=1 this is 4 * 6 * 8 = 192.

data ShimuraTowerSpatialLatticeStatus : Set where
  shimuraTowerSpatialLatticeDefinedNoClay :
    ShimuraTowerSpatialLatticeStatus

data ShimuraTowerLane : Set where
  lane3 :
    ShimuraTowerLane

  lane4 :
    ShimuraTowerLane

  lane7 :
    ShimuraTowerLane

canonicalShimuraTowerLanes : List ShimuraTowerLane
canonicalShimuraTowerLanes =
  lane3
  ∷ lane4
  ∷ lane7
  ∷ []

data ShimuraTowerModularCurve : Set where
  X0-3^_ :
    Nat →
    ShimuraTowerModularCurve

  X0-4^_ :
    Nat →
    ShimuraTowerModularCurve

  X0-7^_ :
    Nat →
    ShimuraTowerModularCurve

levelOneShimuraTowerFactors : List ShimuraTowerModularCurve
levelOneShimuraTowerFactors =
  X0-3^ 1
  ∷ X0-4^ 1
  ∷ X0-7^ 1
  ∷ []

data ShimuraTowerSeedSite : Set where
  seedCM3 :
    ShimuraTowerSeedSite

  seedCM4 :
    ShimuraTowerSeedSite

  seedCM7 :
    ShimuraTowerSeedSite

canonicalShimuraTowerSeedSites : List ShimuraTowerSeedSite
canonicalShimuraTowerSeedSites =
  seedCM3
  ∷ seedCM4
  ∷ seedCM7
  ∷ []

data YMSpatialRefinementFromShimuraTowerStatus : Set where
  inhabitedCandidate :
    YMSpatialRefinementFromShimuraTowerStatus

data ShimuraTowerSpatialLatticeStep : Set where
  retainSeedThreeHeegnerLaneLabels :
    ShimuraTowerSpatialLatticeStep

  replaceLane3ByX0-3^kCMPoints :
    ShimuraTowerSpatialLatticeStep

  replaceLane4ByX0-4^kCMPoints :
    ShimuraTowerSpatialLatticeStep

  replaceLane7ByX0-7^kCMPoints :
    ShimuraTowerSpatialLatticeStep

  takeProductOfThreeLaneCovers :
    ShimuraTowerSpatialLatticeStep

  recordNoClayPromotion :
    ShimuraTowerSpatialLatticeStep

canonicalShimuraTowerSpatialLatticeSteps :
  List ShimuraTowerSpatialLatticeStep
canonicalShimuraTowerSpatialLatticeSteps =
  retainSeedThreeHeegnerLaneLabels
  ∷ replaceLane3ByX0-3^kCMPoints
  ∷ replaceLane4ByX0-4^kCMPoints
  ∷ replaceLane7ByX0-7^kCMPoints
  ∷ takeProductOfThreeLaneCovers
  ∷ recordNoClayPromotion
  ∷ []

data ShimuraTowerSpatialLatticePromotion : Set where

shimuraTowerSpatialLatticePromotionImpossibleHere :
  ShimuraTowerSpatialLatticePromotion →
  ⊥
shimuraTowerSpatialLatticePromotionImpossibleHere ()

psi3Power : Nat → Nat
psi3Power zero =
  1
psi3Power (suc zero) =
  4
psi3Power (suc (suc k)) =
  3 * psi3Power (suc k)

psi4Power : Nat → Nat
psi4Power zero =
  1
psi4Power (suc zero) =
  6
psi4Power (suc (suc k)) =
  4 * psi4Power (suc k)

psi7Power : Nat → Nat
psi7Power zero =
  1
psi7Power (suc zero) =
  8
psi7Power (suc (suc k)) =
  7 * psi7Power (suc k)

shimuraTowerSiteCountAtLevel : Nat → Nat
shimuraTowerSiteCountAtLevel k =
  psi3Power k * psi4Power k * psi7Power k

shimuraTowerLevelKSiteStatement : String
shimuraTowerLevelKSiteStatement =
  "At level k, spatial sites are CM points of X0(3^k) x X0(4^k) x X0(7^k)."

shimuraTowerSiteCountStatement : String
shimuraTowerSiteCountStatement =
  "siteCountAtLevelK k = psi(3^k) * psi(4^k) * psi(7^k); at k=1 this is 4 * 6 * 8 = 192."

shimuraTowerSeedStatement : String
shimuraTowerSeedStatement =
  "The original three Heegner sites are level-0 seed labels with one CM point per lane; at level k each lane refines by its modular cover."

shimuraTowerRefinementStatement : String
shimuraTowerRefinementStatement =
  "The Shimura tower gives an inhabited candidate spatial refinement mechanism for the Yang-Mills carrier lattice, but no Clay Yang-Mills promotion is made here."

record ShimuraTowerSpatialLatticeReceipt : Setω where
  field
    status :
      ShimuraTowerSpatialLatticeStatus

    shimuraTowerDefined :
      Bool

    shimuraTowerDefinedIsTrue :
      shimuraTowerDefined ≡ true

    levelK :
      Nat

    modularFactorsAtLevelK :
      List ShimuraTowerModularCurve

    modularFactorsAtLevelKAreLevelOneCanonical :
      levelK ≡ 1 →
      modularFactorsAtLevelK ≡ levelOneShimuraTowerFactors

    spatialSitesAreCMPointsOfProduct :
      Bool

    spatialSitesAreCMPointsOfProductIsTrue :
      spatialSitesAreCMPointsOfProduct ≡ true

    siteCountAtLevelK :
      Nat

    siteCountAtLevelKIsPsiProduct :
      siteCountAtLevelK ≡
      psi3Power levelK * psi4Power levelK * psi7Power levelK

    levelOnePsi3 :
      psi3Power 1 ≡ 4

    levelOnePsi4 :
      psi4Power 1 ≡ 6

    levelOnePsi7 :
      psi7Power 1 ≡ 8

    levelOneSiteCount :
      siteCountAtLevelK ≡ 192

    seedSites :
      List ShimuraTowerSeedSite

    seedSitesAreCanonical :
      seedSites ≡ canonicalShimuraTowerSeedSites

    seedSiteCountPerLane :
      Nat

    seedSiteCountPerLaneIsOne :
      seedSiteCountPerLane ≡ 1

    originalThreeHeegnerSitesAreLevelZeroSeedLabels :
      Bool

    originalThreeHeegnerSitesAreLevelZeroSeedLabelsIsTrue :
      originalThreeHeegnerSitesAreLevelZeroSeedLabels ≡ true

    lanes :
      List ShimuraTowerLane

    lanesAreCanonical :
      lanes ≡ canonicalShimuraTowerLanes

    eachLaneRefinesByCover :
      Bool

    eachLaneRefinesByCoverIsTrue :
      eachLaneRefinesByCover ≡ true

    spatialLatticeRefinable :
      Bool

    spatialLatticeRefinableIsTrue :
      spatialLatticeRefinable ≡ true

    ymSpatialRefinementFromShimuraTower :
      YMSpatialRefinementFromShimuraTowerStatus

    ymSpatialRefinementFromShimuraTowerIsInhabitedCandidate :
      ymSpatialRefinementFromShimuraTower ≡ inhabitedCandidate

    levelKSiteStatement :
      String

    levelKSiteStatementIsCanonical :
      levelKSiteStatement ≡ shimuraTowerLevelKSiteStatement

    siteCountStatement :
      String

    siteCountStatementIsCanonical :
      siteCountStatement ≡ shimuraTowerSiteCountStatement

    seedStatement :
      String

    seedStatementIsCanonical :
      seedStatement ≡ shimuraTowerSeedStatement

    refinementStatement :
      String

    refinementStatementIsCanonical :
      refinementStatement ≡ shimuraTowerRefinementStatement

    Clay :
      Bool

    ClayIsFalse :
      Clay ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    steps :
      List ShimuraTowerSpatialLatticeStep

    stepsAreCanonical :
      steps ≡ canonicalShimuraTowerSpatialLatticeSteps

    promotionFlags :
      List ShimuraTowerSpatialLatticePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ShimuraTowerSpatialLatticeReceipt public

canonicalShimuraTowerSpatialLatticeReceipt :
  ShimuraTowerSpatialLatticeReceipt
canonicalShimuraTowerSpatialLatticeReceipt =
  record
    { status =
        shimuraTowerSpatialLatticeDefinedNoClay
    ; shimuraTowerDefined =
        true
    ; shimuraTowerDefinedIsTrue =
        refl
    ; levelK =
        1
    ; modularFactorsAtLevelK =
        levelOneShimuraTowerFactors
    ; modularFactorsAtLevelKAreLevelOneCanonical =
        λ _ → refl
    ; spatialSitesAreCMPointsOfProduct =
        true
    ; spatialSitesAreCMPointsOfProductIsTrue =
        refl
    ; siteCountAtLevelK =
        shimuraTowerSiteCountAtLevel 1
    ; siteCountAtLevelKIsPsiProduct =
        refl
    ; levelOnePsi3 =
        refl
    ; levelOnePsi4 =
        refl
    ; levelOnePsi7 =
        refl
    ; levelOneSiteCount =
        refl
    ; seedSites =
        canonicalShimuraTowerSeedSites
    ; seedSitesAreCanonical =
        refl
    ; seedSiteCountPerLane =
        1
    ; seedSiteCountPerLaneIsOne =
        refl
    ; originalThreeHeegnerSitesAreLevelZeroSeedLabels =
        true
    ; originalThreeHeegnerSitesAreLevelZeroSeedLabelsIsTrue =
        refl
    ; lanes =
        canonicalShimuraTowerLanes
    ; lanesAreCanonical =
        refl
    ; eachLaneRefinesByCover =
        true
    ; eachLaneRefinesByCoverIsTrue =
        refl
    ; spatialLatticeRefinable =
        true
    ; spatialLatticeRefinableIsTrue =
        refl
    ; ymSpatialRefinementFromShimuraTower =
        inhabitedCandidate
    ; ymSpatialRefinementFromShimuraTowerIsInhabitedCandidate =
        refl
    ; levelKSiteStatement =
        shimuraTowerLevelKSiteStatement
    ; levelKSiteStatementIsCanonical =
        refl
    ; siteCountStatement =
        shimuraTowerSiteCountStatement
    ; siteCountStatementIsCanonical =
        refl
    ; seedStatement =
        shimuraTowerSeedStatement
    ; seedStatementIsCanonical =
        refl
    ; refinementStatement =
        shimuraTowerRefinementStatement
    ; refinementStatementIsCanonical =
        refl
    ; Clay =
        false
    ; ClayIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; steps =
        canonicalShimuraTowerSpatialLatticeSteps
    ; stepsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B1 defines the Shimura tower spatial lattice over the 3, 4, and 7 lanes"
        ∷ "Level k sites are CM points on X0(3^k) x X0(4^k) x X0(7^k)"
        ∷ "Level 1 records psi counts 4, 6, 8 and total site count 192"
        ∷ "The k=0 three-Heegner object is retained as seed labelling, not as a terminal rigid obstruction"
        ∷ "This is an inhabited candidate YM spatial-refinement mechanism; Clay promotion remains false"
        ∷ []
    }

shimuraTowerRecordsLevelOneSiteCount192 :
  siteCountAtLevelK canonicalShimuraTowerSpatialLatticeReceipt ≡ 192
shimuraTowerRecordsLevelOneSiteCount192 =
  refl

shimuraTowerKeepsClayFalse :
  clayYangMillsPromoted canonicalShimuraTowerSpatialLatticeReceipt
    ≡ false
shimuraTowerKeepsClayFalse =
  refl
