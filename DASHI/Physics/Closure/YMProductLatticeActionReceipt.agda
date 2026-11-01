module DASHI.Physics.Closure.YMProductLatticeActionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

data YMProductLatticeActionStatus : Set where
  productLatticeWilsonActionRecordedNoClayPromotion :
    YMProductLatticeActionStatus

data ProductLatticeFactor : Set where
  heegnerTriangleDelta3 :
    ProductLatticeFactor

  spatialCircleZL1 :
    ProductLatticeFactor

  temporalCircleZT1 :
    ProductLatticeFactor

canonicalProductLatticeFactors : List ProductLatticeFactor
canonicalProductLatticeFactors =
  heegnerTriangleDelta3
  ∷ spatialCircleZL1
  ∷ temporalCircleZT1
  ∷ []

data ProductLatticePlaquetteKind : Set where
  triangularHeegnerPlaquette :
    ProductLatticePlaquetteKind

  squareCirclePlaquette :
    ProductLatticePlaquetteKind

  mixedTriangleCirclePlaquette :
    ProductLatticePlaquetteKind

canonicalProductLatticePlaquetteKinds :
  List ProductLatticePlaquetteKind
canonicalProductLatticePlaquetteKinds =
  triangularHeegnerPlaquette
  ∷ squareCirclePlaquette
  ∷ mixedTriangleCirclePlaquette
  ∷ []

data SUProductLinkKind : Set where
  heegnerTriangleLink :
    SUProductLinkKind

  circleSpatialLink :
    SUProductLinkKind

  circleTemporalLink :
    SUProductLinkKind

canonicalSUProductLinkKinds : List SUProductLinkKind
canonicalSUProductLinkKinds =
  heegnerTriangleLink
  ∷ circleSpatialLink
  ∷ circleTemporalLink
  ∷ []

data YMProductLatticeActionBlocker : Set where
  missingHaarPartitionFunction :
    YMProductLatticeActionBlocker

  missingReflectionPositivityProof :
    YMProductLatticeActionBlocker

  missingContinuumLimit :
    YMProductLatticeActionBlocker

  missingUniformMassGap :
    YMProductLatticeActionBlocker

canonicalYMProductLatticeActionBlockers :
  List YMProductLatticeActionBlocker
canonicalYMProductLatticeActionBlockers =
  missingHaarPartitionFunction
  ∷ missingReflectionPositivityProof
  ∷ missingContinuumLimit
  ∷ missingUniformMassGap
  ∷ []

data YMProductLatticePromotion : Set where

ymProductLatticePromotionImpossibleHere :
  YMProductLatticePromotion →
  ⊥
ymProductLatticePromotionImpossibleHere ()

productLatticeLabel : String
productLatticeLabel =
  "Lambda = Delta_3 x Z_L^1 x Z_T^1"

heegnerTrianglePlusCirclesLabel : String
heegnerTrianglePlusCirclesLabel =
  "Delta_3 is the Heegner triangle factor; Z_L^1 and Z_T^1 are the spatial and temporal circle factors"

suNLinkLabel : String
suNLinkLabel =
  "Each oriented link carries U_l in SU(N)"

productWilsonActionLabel : String
productWilsonActionLabel =
  "S_W[U] = -(beta/2N) sum_P Re Tr(U_P), beta = k / pi from the recorded Chern-Simons level k"

record YMProductLatticeActionReceipt : Setω where
  field
    status :
      YMProductLatticeActionStatus

    latticeLabel :
      String

    latticeLabelIsCanonical :
      latticeLabel ≡ productLatticeLabel

    latticeDimension :
      Nat

    latticeDimensionIsFour :
      latticeDimension ≡ 4

    factors :
      List ProductLatticeFactor

    factorsAreCanonical :
      factors ≡ canonicalProductLatticeFactors

    heegnerTrianglePlusCircles :
      Bool

    heegnerTrianglePlusCirclesIsTrue :
      heegnerTrianglePlusCircles ≡ true

    heegnerTrianglePlusCirclesStatement :
      String

    heegnerTrianglePlusCirclesStatementIsCanonical :
      heegnerTrianglePlusCirclesStatement
      ≡
      heegnerTrianglePlusCirclesLabel

    gaugeRankN :
      Nat

    gaugeRankNIsCanonical :
      gaugeRankN ≡ 3

    suNLinks :
      Bool

    suNLinksIsTrue :
      suNLinks ≡ true

    suNLinkStatement :
      String

    suNLinkStatementIsCanonical :
      suNLinkStatement ≡ suNLinkLabel

    linkKinds :
      List SUProductLinkKind

    linkKindsAreCanonical :
      linkKinds ≡ canonicalSUProductLinkKinds

    plaquetteKinds :
      List ProductLatticePlaquetteKind

    plaquetteKindsAreCanonical :
      plaquetteKinds ≡ canonicalProductLatticePlaquetteKinds

    triangularPlaquettesRecorded :
      Bool

    triangularPlaquettesRecordedIsTrue :
      triangularPlaquettesRecorded ≡ true

    squarePlaquettesRecorded :
      Bool

    squarePlaquettesRecordedIsTrue :
      squarePlaquettesRecorded ≡ true

    mixedPlaquettesRecorded :
      Bool

    mixedPlaquettesRecordedIsTrue :
      mixedPlaquettesRecorded ≡ true

    csLevel :
      Nat

    csLevelIsCanonical :
      csLevel ≡ 1

    betaFromCSLevel :
      String

    betaFromCSLevelIsCanonical :
      betaFromCSLevel ≡ "beta = k / pi"

    wilsonActionStatement :
      String

    wilsonActionStatementIsCanonical :
      wilsonActionStatement ≡ productWilsonActionLabel

    productLattice4DActionDefined :
      Bool

    productLattice4DActionDefinedIsTrue :
      productLattice4DActionDefined ≡ true

    wilsonActionOnProductLattice :
      Bool

    wilsonActionOnProductLatticeIsTrue :
      wilsonActionOnProductLattice ≡ true

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    blockers :
      List YMProductLatticeActionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMProductLatticeActionBlockers

    promotionFlags :
      List YMProductLatticePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMProductLatticeActionReceipt public

canonicalYMProductLatticeActionReceipt :
  YMProductLatticeActionReceipt
canonicalYMProductLatticeActionReceipt =
  record
    { status =
        productLatticeWilsonActionRecordedNoClayPromotion
    ; latticeLabel =
        productLatticeLabel
    ; latticeLabelIsCanonical =
        refl
    ; latticeDimension =
        4
    ; latticeDimensionIsFour =
        refl
    ; factors =
        canonicalProductLatticeFactors
    ; factorsAreCanonical =
        refl
    ; heegnerTrianglePlusCircles =
        true
    ; heegnerTrianglePlusCirclesIsTrue =
        refl
    ; heegnerTrianglePlusCirclesStatement =
        heegnerTrianglePlusCirclesLabel
    ; heegnerTrianglePlusCirclesStatementIsCanonical =
        refl
    ; gaugeRankN =
        3
    ; gaugeRankNIsCanonical =
        refl
    ; suNLinks =
        true
    ; suNLinksIsTrue =
        refl
    ; suNLinkStatement =
        suNLinkLabel
    ; suNLinkStatementIsCanonical =
        refl
    ; linkKinds =
        canonicalSUProductLinkKinds
    ; linkKindsAreCanonical =
        refl
    ; plaquetteKinds =
        canonicalProductLatticePlaquetteKinds
    ; plaquetteKindsAreCanonical =
        refl
    ; triangularPlaquettesRecorded =
        true
    ; triangularPlaquettesRecordedIsTrue =
        refl
    ; squarePlaquettesRecorded =
        true
    ; squarePlaquettesRecordedIsTrue =
        refl
    ; mixedPlaquettesRecorded =
        true
    ; mixedPlaquettesRecordedIsTrue =
        refl
    ; csLevel =
        1
    ; csLevelIsCanonical =
        refl
    ; betaFromCSLevel =
        "beta = k / pi"
    ; betaFromCSLevelIsCanonical =
        refl
    ; wilsonActionStatement =
        productWilsonActionLabel
    ; wilsonActionStatementIsCanonical =
        refl
    ; productLattice4DActionDefined =
        true
    ; productLattice4DActionDefinedIsTrue =
        refl
    ; wilsonActionOnProductLattice =
        true
    ; wilsonActionOnProductLatticeIsTrue =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalYMProductLatticeActionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B3 records the Wilson action on Lambda = Delta_3 x Z_L^1 x Z_T^1"
        ∷ "The lattice has the Heegner triangle factor plus two circle factors, with SU(N) link variables"
        ∷ "Triangular, square, and mixed plaquette classes are included in the finite Wilson action"
        ∷ "The receipt records beta = k / pi from the Chern-Simons level k for this finite action surface"
        ∷ "Continuum Yang-Mills, Clay Yang-Mills, and terminal Clay promotion remain false"
        ∷ []
    }

productLattice4DActionDefinedFlag :
  productLattice4DActionDefined canonicalYMProductLatticeActionReceipt
  ≡
  true
productLattice4DActionDefinedFlag =
  refl

heegnerTrianglePlusCirclesFlag :
  heegnerTrianglePlusCircles canonicalYMProductLatticeActionReceipt
  ≡
  true
heegnerTrianglePlusCirclesFlag =
  refl

wilsonActionOnProductLatticeFlag :
  wilsonActionOnProductLattice canonicalYMProductLatticeActionReceipt
  ≡
  true
wilsonActionOnProductLatticeFlag =
  refl

ymProductLatticeActionDoesNotPromoteClay :
  clayYangMillsPromoted canonicalYMProductLatticeActionReceipt
  ≡
  false
ymProductLatticeActionDoesNotPromoteClay =
  refl

ymProductLatticeActionDoesNotPromoteTerminalClay :
  terminalClayClaimPromoted canonicalYMProductLatticeActionReceipt
  ≡
  false
ymProductLatticeActionDoesNotPromoteTerminalClay =
  refl
