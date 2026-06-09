module DASHI.Physics.Closure.CarrierStateVariableMappingReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Carrier state variable mapping receipt.
--
-- This receipt records the Paper-1-style carrier state tuple
--
--   x = (a, nu, tau, d, ell, r)
--
-- as finite bookkeeping only.
--
--   a   : refinement address / Bruhat-Tits braid position
--   nu  : FactorVec, fifteen exponent lanes, split as 7+7+1
--   tau : ternary sign, observer/carry lane
--   d   : depth j, with j+1 implicit in the atom edge
--   ell : active lane among SSP lanes
--   r   : residual / unabsorbed carry / defect not discarded
--
-- The j-and-j+1 reading is recorded by making every atom an edge
-- (depth , depth+1).  This module does not prove a Paper 1 theorem, does not
-- close Gate 3, and does not promote any Clay claim.

data CarrierStateVariableMappingStatus : Set where
  paperOneCarrierTupleRecordedAsBookkeeping :
    CarrierStateVariableMappingStatus

data RefinementAddress : Set where
  refinementAddressBTBraidPosition :
    RefinementAddress

data FactorLaneBlock : Set where
  firstSeptetExponentLanes :
    FactorLaneBlock

  secondSeptetExponentLanes :
    FactorLaneBlock

  spareObserverCarryLane :
    FactorLaneBlock

canonicalFactorLaneBlocks :
  List FactorLaneBlock
canonicalFactorLaneBlocks =
  firstSeptetExponentLanes
  ∷ secondSeptetExponentLanes
  ∷ spareObserverCarryLane
  ∷ []

data FactorLaneCount : Set where
  sevenPlusSevenPlusOneGivesFifteen :
    FactorLaneCount

data TernarySign : Set where
  negativeCarry :
    TernarySign

  neutralCarry :
    TernarySign

  positiveCarry :
    TernarySign

canonicalTernarySigns :
  List TernarySign
canonicalTernarySigns =
  negativeCarry
  ∷ neutralCarry
  ∷ positiveCarry
  ∷ []

data TernarySignRole : Set where
  observerCarryLane :
    TernarySignRole

data SSPLane : Set where
  p2Lane :
    SSPLane

  p3Lane :
    SSPLane

  p5Lane :
    SSPLane

  p7Lane :
    SSPLane

  p11Lane :
    SSPLane

  p13Lane :
    SSPLane

  p17Lane :
    SSPLane

  p19Lane :
    SSPLane

  p23Lane :
    SSPLane

  p29Lane :
    SSPLane

  p31Lane :
    SSPLane

  p41Lane :
    SSPLane

  p47Lane :
    SSPLane

  p59Lane :
    SSPLane

  p71Lane :
    SSPLane

canonicalSSPLanes :
  List SSPLane
canonicalSSPLanes =
  p2Lane
  ∷ p3Lane
  ∷ p5Lane
  ∷ p7Lane
  ∷ p11Lane
  ∷ p13Lane
  ∷ p17Lane
  ∷ p19Lane
  ∷ p23Lane
  ∷ p29Lane
  ∷ p31Lane
  ∷ p41Lane
  ∷ p47Lane
  ∷ p59Lane
  ∷ p71Lane
  ∷ []

data ResidualRole : Set where
  residualUnabsorbedCarryDefectNotDiscarded :
    ResidualRole

record FactorVec : Set where
  constructor factorVec
  field
    laneBlocks :
      List FactorLaneBlock

    laneCount :
      FactorLaneCount

    factorVecSummary :
      String

record AtomEdge : Set where
  constructor atomEdge
  field
    depth :
      Nat

    nextDepth :
      Nat

    nextDepthIsDepthPlusOne :
      nextDepth ≡ suc depth

edgeFromDepth :
  Nat →
  AtomEdge
edgeFromDepth j =
  atomEdge j (suc j) refl

canonicalDepth :
  Nat
canonicalDepth =
  zero

canonicalAtomEdge :
  AtomEdge
canonicalAtomEdge =
  edgeFromDepth canonicalDepth

data CarrierTupleCoordinate : Set where
  aCoordinate :
    CarrierTupleCoordinate

  nuCoordinate :
    CarrierTupleCoordinate

  tauCoordinate :
    CarrierTupleCoordinate

  dCoordinate :
    CarrierTupleCoordinate

  ellCoordinate :
    CarrierTupleCoordinate

  rCoordinate :
    CarrierTupleCoordinate

canonicalCarrierTupleCoordinates :
  List CarrierTupleCoordinate
canonicalCarrierTupleCoordinates =
  aCoordinate
  ∷ nuCoordinate
  ∷ tauCoordinate
  ∷ dCoordinate
  ∷ ellCoordinate
  ∷ rCoordinate
  ∷ []

data CarrierTupleReading : Set where
  xEqualsACommaNuCommaTauCommaDCommaEllCommaR :
    CarrierTupleReading

data CarrierStateNonClaim : Set where
  noPaperOneTheoremProof :
    CarrierStateNonClaim

  noGate3Closure :
    CarrierStateNonClaim

  noClayPromotion :
    CarrierStateNonClaim

canonicalCarrierStateNonClaims :
  List CarrierStateNonClaim
canonicalCarrierStateNonClaims =
  noPaperOneTheoremProof
  ∷ noGate3Closure
  ∷ noClayPromotion
  ∷ []

data CarrierStatePromotion : Set where

carrierStatePromotionImpossibleHere :
  CarrierStatePromotion →
  ⊥
carrierStatePromotionImpossibleHere ()

record CarrierStateTuple : Set where
  constructor carrierStateTuple
  field
    a :
      RefinementAddress

    nu :
      FactorVec

    tau :
      TernarySign

    d :
      Nat

    atomEdgeAtD :
      AtomEdge

    atomEdgeDepthIsD :
      AtomEdge.depth atomEdgeAtD ≡ d

    atomEdgeNextIsDPlusOne :
      AtomEdge.nextDepth atomEdgeAtD ≡ suc d

    ell :
      SSPLane

    r :
      ResidualRole

CarrierStateTupleShape : Set
CarrierStateTupleShape =
  RefinementAddress × FactorVec × TernarySign × Nat × SSPLane × ResidualRole

asTupleShape :
  CarrierStateTuple →
  CarrierStateTupleShape
asTupleShape x =
  CarrierStateTuple.a x ,
  CarrierStateTuple.nu x ,
  CarrierStateTuple.tau x ,
  CarrierStateTuple.d x ,
  CarrierStateTuple.ell x ,
  CarrierStateTuple.r x

record CarrierStateVariableMappingReceipt : Set where
  field
    status :
      CarrierStateVariableMappingStatus

    tupleReading :
      CarrierTupleReading

    carrierState :
      CarrierStateTuple

    tupleCoordinates :
      List CarrierTupleCoordinate

    tupleCoordinatesAreCanonical :
      tupleCoordinates ≡ canonicalCarrierTupleCoordinates

    factorLaneBlocks :
      List FactorLaneBlock

    factorLaneBlocksAreSevenSevenOne :
      factorLaneBlocks ≡ canonicalFactorLaneBlocks

    factorLaneCount :
      FactorLaneCount

    factorLaneCountIsFifteen :
      factorLaneCount ≡ sevenPlusSevenPlusOneGivesFifteen

    ternarySigns :
      List TernarySign

    ternarySignsAreCanonical :
      ternarySigns ≡ canonicalTernarySigns

    ternarySignRole :
      TernarySignRole

    activeLaneUniverse :
      List SSPLane

    activeLaneUniverseIsCanonical :
      activeLaneUniverse ≡ canonicalSSPLanes

    depthEdge :
      AtomEdge

    depthEdgeIsCarrierAtomEdge :
      depthEdge ≡ CarrierStateTuple.atomEdgeAtD carrierState

    everyAtomIsDepthAndDepthPlusOne :
      AtomEdge.nextDepth depthEdge ≡ suc (AtomEdge.depth depthEdge)

    residualRole :
      ResidualRole

    residualRoleIsUnabsorbedCarryDefect :
      residualRole ≡ residualUnabsorbedCarryDefectNotDiscarded

    bookkeepingOnly :
      Bool

    bookkeepingOnlyIsTrue :
      bookkeepingOnly ≡ true

    paperOneTheoremPromoted :
      Bool

    paperOneTheoremPromotedIsFalse :
      paperOneTheoremPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    nonClaims :
      List CarrierStateNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalCarrierStateNonClaims

    receiptBoundary :
      List String

canonicalFactorVec :
  FactorVec
canonicalFactorVec =
  factorVec
    canonicalFactorLaneBlocks
    sevenPlusSevenPlusOneGivesFifteen
    "nu is FactorVec: fifteen exponent lanes split as 7+7+1."

canonicalCarrierState :
  CarrierStateTuple
canonicalCarrierState =
  carrierStateTuple
    refinementAddressBTBraidPosition
    canonicalFactorVec
    neutralCarry
    canonicalDepth
    canonicalAtomEdge
    refl
    refl
    p2Lane
    residualUnabsorbedCarryDefectNotDiscarded

canonicalCarrierStateVariableMappingReceipt :
  CarrierStateVariableMappingReceipt
canonicalCarrierStateVariableMappingReceipt =
  record
    { status =
        paperOneCarrierTupleRecordedAsBookkeeping
    ; tupleReading =
        xEqualsACommaNuCommaTauCommaDCommaEllCommaR
    ; carrierState =
        canonicalCarrierState
    ; tupleCoordinates =
        canonicalCarrierTupleCoordinates
    ; tupleCoordinatesAreCanonical =
        refl
    ; factorLaneBlocks =
        canonicalFactorLaneBlocks
    ; factorLaneBlocksAreSevenSevenOne =
        refl
    ; factorLaneCount =
        sevenPlusSevenPlusOneGivesFifteen
    ; factorLaneCountIsFifteen =
        refl
    ; ternarySigns =
        canonicalTernarySigns
    ; ternarySignsAreCanonical =
        refl
    ; ternarySignRole =
        observerCarryLane
    ; activeLaneUniverse =
        canonicalSSPLanes
    ; activeLaneUniverseIsCanonical =
        refl
    ; depthEdge =
        canonicalAtomEdge
    ; depthEdgeIsCarrierAtomEdge =
        refl
    ; everyAtomIsDepthAndDepthPlusOne =
        refl
    ; residualRole =
        residualUnabsorbedCarryDefectNotDiscarded
    ; residualRoleIsUnabsorbedCarryDefect =
        refl
    ; bookkeepingOnly =
        true
    ; bookkeepingOnlyIsTrue =
        refl
    ; paperOneTheoremPromoted =
        false
    ; paperOneTheoremPromotedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; nonClaims =
        canonicalCarrierStateNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; receiptBoundary =
        "x is recorded as the carrier state tuple (a, nu, tau, d, ell, r)."
        ∷ "a is the refinement address / Bruhat-Tits braid position."
        ∷ "nu is the FactorVec bookkeeping surface with fifteen exponent lanes split 7+7+1."
        ∷ "tau is a ternary sign used as observer/carry lane."
        ∷ "d is depth j, and the atom edge records both j and j+1."
        ∷ "ell is the active lane among the fifteen SSP lanes."
        ∷ "r is the residual: unabsorbed carry or defect, explicitly not discarded."
        ∷ "This is bookkeeping only: no Paper 1 theorem proof, no Gate 3 closure, and no Clay promotion."
        ∷ []
    }

canonicalStateTupleShape :
  CarrierStateTupleShape
canonicalStateTupleShape =
  asTupleShape canonicalCarrierState

canonicalStateDepthEdgeNextIsOne :
  AtomEdge.nextDepth canonicalAtomEdge ≡ suc canonicalDepth
canonicalStateDepthEdgeNextIsOne =
  refl

canonicalReceiptKeepsPaperOneTheoremFalse :
  CarrierStateVariableMappingReceipt.paperOneTheoremPromoted
    canonicalCarrierStateVariableMappingReceipt ≡ false
canonicalReceiptKeepsPaperOneTheoremFalse =
  refl

canonicalReceiptKeepsGate3False :
  CarrierStateVariableMappingReceipt.gate3Closed
    canonicalCarrierStateVariableMappingReceipt ≡ false
canonicalReceiptKeepsGate3False =
  refl

canonicalReceiptKeepsClayFalse :
  CarrierStateVariableMappingReceipt.clayPromoted
    canonicalCarrierStateVariableMappingReceipt ≡ false
canonicalReceiptKeepsClayFalse =
  refl
