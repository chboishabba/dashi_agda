module DASHI.Physics.Closure.BruhatTitsProductTreeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

data ProductTreeReceiptStatus : Set where
  bruhatTitsProductTreeRecordedNoClayPromotion :
    ProductTreeReceiptStatus

data BruhatTitsTreeLane : Set where
  T3Lane :
    BruhatTitsTreeLane

  T2Lane :
    BruhatTitsTreeLane

  T7Lane :
    BruhatTitsTreeLane

canonicalBruhatTitsTreeLanes : List BruhatTitsTreeLane
canonicalBruhatTitsTreeLanes =
  T3Lane
  ∷ T2Lane
  ∷ T7Lane
  ∷ []

data ProductTreeSpatialCarrier : Set where
  T3xT2xT7Carrier :
    ProductTreeSpatialCarrier

data PAdicContinuumCarrier : Set where
  Q3xQ2xQ7Continuum :
    PAdicContinuumCarrier

data ProductTreeGeometryFact : Set where
  T3FourRegular :
    ProductTreeGeometryFact

  T2ThreeRegular :
    ProductTreeGeometryFact

  T7EightRegular :
    ProductTreeGeometryFact

  T3DeltaZeroGromovHyperbolic :
    ProductTreeGeometryFact

  T2DeltaZeroGromovHyperbolic :
    ProductTreeGeometryFact

  T7DeltaZeroGromovHyperbolic :
    ProductTreeGeometryFact

canonicalProductTreeGeometryFacts :
  List ProductTreeGeometryFact
canonicalProductTreeGeometryFacts =
  T3FourRegular
  ∷ T2ThreeRegular
  ∷ T7EightRegular
  ∷ T3DeltaZeroGromovHyperbolic
  ∷ T2DeltaZeroGromovHyperbolic
  ∷ T7DeltaZeroGromovHyperbolic
  ∷ []

data ProductTreeWilsonAuthority : Set where
  gubser2017PAdicAdSCFTAuthority :
    ProductTreeWilsonAuthority

canonicalProductTreeWilsonAuthorities :
  List ProductTreeWilsonAuthority
canonicalProductTreeWilsonAuthorities =
  gubser2017PAdicAdSCFTAuthority
  ∷ []

data ProductTreePromotion : Set where

productTreePromotionImpossibleHere :
  ProductTreePromotion →
  ⊥
productTreePromotionImpossibleHere ()

pAdicSpatialCarrierLabel : String
pAdicSpatialCarrierLabel =
  "Bruhat-Tits product tree T3 x T2 x T7 as p-adic spatial carrier"

continuumDepthLimitLabel : String
continuumDepthLimitLabel =
  "continuum/depth limit gives Q3 x Q2 x Q7 p-adic spatial continuum"

gubser2017AuthorityLabel : String
gubser2017AuthorityLabel =
  "Gubser et al. 2017 p-adic AdS/CFT Bruhat-Tits tree authority for inhabitable reflection-positive Wilson-action bookkeeping"

record BruhatTitsProductTreeReceipt : Setω where
  field
    status :
      ProductTreeReceiptStatus

    spatialCarrier :
      ProductTreeSpatialCarrier

    spatialCarrierLabel :
      String

    spatialCarrierLabelIsCanonical :
      spatialCarrierLabel ≡ pAdicSpatialCarrierLabel

    lanes :
      List BruhatTitsTreeLane

    lanesAreCanonical :
      lanes ≡ canonicalBruhatTitsTreeLanes

    T3Regularity :
      Nat

    T3RegularityIsFour :
      T3Regularity ≡ 4

    T2Regularity :
      Nat

    T2RegularityIsThree :
      T2Regularity ≡ 3

    T7Regularity :
      Nat

    T7RegularityIsEight :
      T7Regularity ≡ 8

    eachTreeDeltaZeroHyperbolic :
      Bool

    eachTreeDeltaZeroHyperbolicIsTrue :
      eachTreeDeltaZeroHyperbolic ≡ true

    eachTreeGromovFlat :
      Bool

    eachTreeGromovFlatIsTrue :
      eachTreeGromovFlat ≡ true

    geometryFacts :
      List ProductTreeGeometryFact

    geometryFactsAreCanonical :
      geometryFacts ≡ canonicalProductTreeGeometryFacts

    wilsonActionOnProductTreeInhabitable :
      Bool

    wilsonActionOnProductTreeInhabitableIsTrue :
      wilsonActionOnProductTreeInhabitable ≡ true

    reflectionPositivityInhabitable :
      Bool

    reflectionPositivityInhabitableIsTrue :
      reflectionPositivityInhabitable ≡ true

    wilsonAuthority :
      String

    wilsonAuthorityIsCanonical :
      wilsonAuthority ≡ gubser2017AuthorityLabel

    wilsonAuthorities :
      List ProductTreeWilsonAuthority

    wilsonAuthoritiesAreCanonical :
      wilsonAuthorities ≡ canonicalProductTreeWilsonAuthorities

    continuumCarrier :
      PAdicContinuumCarrier

    continuumDepthLimit :
      String

    continuumDepthLimitIsCanonical :
      continuumDepthLimit ≡ continuumDepthLimitLabel

    treeIsNotArchimedeanFlat :
      Bool

    treeIsNotArchimedeanFlatIsTrue :
      treeIsNotArchimedeanFlat ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List ProductTreePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open BruhatTitsProductTreeReceipt public

canonicalBruhatTitsProductTreeReceipt :
  BruhatTitsProductTreeReceipt
canonicalBruhatTitsProductTreeReceipt =
  record
    { status =
        bruhatTitsProductTreeRecordedNoClayPromotion
    ; spatialCarrier =
        T3xT2xT7Carrier
    ; spatialCarrierLabel =
        pAdicSpatialCarrierLabel
    ; spatialCarrierLabelIsCanonical =
        refl
    ; lanes =
        canonicalBruhatTitsTreeLanes
    ; lanesAreCanonical =
        refl
    ; T3Regularity =
        4
    ; T3RegularityIsFour =
        refl
    ; T2Regularity =
        3
    ; T2RegularityIsThree =
        refl
    ; T7Regularity =
        8
    ; T7RegularityIsEight =
        refl
    ; eachTreeDeltaZeroHyperbolic =
        true
    ; eachTreeDeltaZeroHyperbolicIsTrue =
        refl
    ; eachTreeGromovFlat =
        true
    ; eachTreeGromovFlatIsTrue =
        refl
    ; geometryFacts =
        canonicalProductTreeGeometryFacts
    ; geometryFactsAreCanonical =
        refl
    ; wilsonActionOnProductTreeInhabitable =
        true
    ; wilsonActionOnProductTreeInhabitableIsTrue =
        refl
    ; reflectionPositivityInhabitable =
        true
    ; reflectionPositivityInhabitableIsTrue =
        refl
    ; wilsonAuthority =
        gubser2017AuthorityLabel
    ; wilsonAuthorityIsCanonical =
        refl
    ; wilsonAuthorities =
        canonicalProductTreeWilsonAuthorities
    ; wilsonAuthoritiesAreCanonical =
        refl
    ; continuumCarrier =
        Q3xQ2xQ7Continuum
    ; continuumDepthLimit =
        continuumDepthLimitLabel
    ; continuumDepthLimitIsCanonical =
        refl
    ; treeIsNotArchimedeanFlat =
        true
    ; treeIsNotArchimedeanFlatIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records T3 x T2 x T7 as a Bruhat-Tits p-adic spatial product-tree carrier"
        ∷ "Each T_p is recorded as (p+1)-regular and delta=0 Gromov-hyperbolic/flat"
        ∷ "Wilson-action reflection positivity is recorded as inhabitable under the Gubser2017 authority label"
        ∷ "The depth limit is recorded as Q3 x Q2 x Q7, with non-Archimedean flatness separated from Archimedean flatness"
        ∷ "No Clay Yang-Mills or terminal promotion is introduced"
        ∷ []
    }

bruhatTitsProductTreeRecorded :
  spatialCarrier canonicalBruhatTitsProductTreeReceipt
  ≡
  T3xT2xT7Carrier
bruhatTitsProductTreeRecorded =
  refl

treeIsNotArchimedeanFlatRecorded :
  treeIsNotArchimedeanFlat canonicalBruhatTitsProductTreeReceipt
  ≡
  true
treeIsNotArchimedeanFlatRecorded =
  refl

bruhatTitsProductTreeKeepsClayFalse :
  clayYangMillsPromoted canonicalBruhatTitsProductTreeReceipt
  ≡
  false
bruhatTitsProductTreeKeepsClayFalse =
  refl

bruhatTitsProductTreeKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalBruhatTitsProductTreeReceipt
  ≡
  false
bruhatTitsProductTreeKeepsTerminalFalse =
  refl
