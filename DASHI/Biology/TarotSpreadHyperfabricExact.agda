module DASHI.Biology.TarotSpreadHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.TarotSemanticKernelExact as Semantic
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Reasoning.TypedHyperfabricCore as Fabric

------------------------------------------------------------------------
-- A spread is a typed relational layout, not merely an ordered card list.
------------------------------------------------------------------------

data PositionId : Set where
  positionId : Nat → PositionId

data SpreadRole : Set where
  inheritanceRole presentConstraintRole possibleDevelopmentRole : SpreadRole
  resourceRole obstacleRole actionRole consequenceRole synthesisRole : SpreadRole
  customRole : String → SpreadRole

data StructuralScale : Set where
  inheritedScale presentScale emergingScale atemporalScale : StructuralScale

record SpreadPosition : Set where
  constructor spreadPosition
  field
    positionIdentity : PositionId
    positionRole : SpreadRole
    positionScale : StructuralScale
    positionLabel : String

open SpreadPosition public

data RelationType : Set where
  precedes supports obstructs qualifies contrastsWith developsInto : RelationType

record SpreadRelation : Set where
  constructor spreadRelation
  field
    relationSource : PositionId
    relationTarget : PositionId
    relationKind : RelationType
    relationResidual : Residual.ResidualLevel
    relationProvenance : List String
    relationSalience : Nat

open SpreadRelation public

------------------------------------------------------------------------
-- Draw-without-replacement carrier.
------------------------------------------------------------------------

record DrawnCard : Set where
  constructor drawnCard
  field
    drawIndex : Nat
    drawnToken : Tarot.CardToken

open DrawnCard public

data IndexAbsent (index : Nat) : List DrawnCard → Set where
  absentNil : IndexAbsent index []
  absentCons :
    ∀ {draw rest} →
    ¬ (index ≡ drawIndex draw) →
    IndexAbsent index rest →
    IndexAbsent index (draw ∷ rest)

data DistinctDraws : List DrawnCard → Set where
  distinctNil : DistinctDraws []
  distinctCons :
    ∀ {draw rest} →
    IndexAbsent (drawIndex draw) rest →
    DistinctDraws rest →
    DistinctDraws (draw ∷ rest)

record TarotLayout : Set where
  constructor tarotLayout
  field
    layoutDraws : List DrawnCard
    drawIndicesArePairwiseDistinct : DistinctDraws layoutDraws
    layoutReceipt : String

open TarotLayout public

foolDraw : DrawnCard
foolDraw =
  drawnCard 0
    (Tarot.cardToken
      (Tarot.major Tarot.theFool)
      Tarot.uprightOrientation
      Tarot.riderWaiteSmith
      ("cliff" ∷ "small bundle" ∷ "open sky" ∷ []))

hermitDraw : DrawnCard
hermitDraw =
  drawnCard 9
    (Tarot.cardToken
      (Tarot.major Tarot.theHermit)
      Tarot.uprightOrientation
      Tarot.riderWaiteSmith
      ("lantern" ∷ "mountain" ∷ "solitary figure" ∷ []))

towerDraw : DrawnCard
towerDraw =
  drawnCard 16
    (Tarot.cardToken
      (Tarot.major Tarot.theTower)
      Tarot.reversedOrientation
      Tarot.riderWaiteSmith
      ("lightning" ∷ "falling crown" ∷ "ruptured structure" ∷ []))

canonicalThreeDrawsAreDistinct :
  DistinctDraws (foolDraw ∷ hermitDraw ∷ towerDraw ∷ [])
canonicalThreeDrawsAreDistinct =
  distinctCons
    (absentCons (λ ()) (absentCons (λ ()) absentNil))
    (distinctCons
      (absentCons (λ ()) absentNil)
      (distinctCons absentNil distinctNil))

canonicalThreeCardLayout : TarotLayout
canonicalThreeCardLayout =
  tarotLayout
    (foolDraw ∷ hermitDraw ∷ towerDraw ∷ [])
    canonicalThreeDrawsAreDistinct
    "three-card Rider--Waite--Smith layout with distinct stable indices"

------------------------------------------------------------------------
-- Local stalks and relational transport.
------------------------------------------------------------------------

record LocalReading : Set where
  constructor localReading
  field
    localPosition : SpreadPosition
    localDraw : DrawnCard
    localMeaning : Semantic.CardMeaning
    localQuestion : String
    localContext : String
    localReceipt : String

open LocalReading public

record RelationalReading : Set where
  constructor relationalReading
  field
    transportedLocal : LocalReading
    transportedBy : RelationType
    retainedResidual : Residual.ResidualLevel
    transportReceipt : String

open RelationalReading public

data SpreadIncidence
    (vertex : PositionId)
    (edge : SpreadRelation) : Set where
  sourceMembership :
    vertex ≡ relationSource edge →
    SpreadIncidence vertex edge
  targetMembership :
    vertex ≡ relationTarget edge →
    SpreadIncidence vertex edge

restrictReading :
  ∀ {vertex edge} →
  SpreadIncidence vertex edge →
  LocalReading →
  RelationalReading
restrictReading {edge = edge} (sourceMembership _) reading =
  relationalReading
    reading
    (relationKind edge)
    (relationResidual edge)
    "source-position meaning transported to spread relation"
restrictReading {edge = edge} (targetMembership _) reading =
  relationalReading
    reading
    (relationKind edge)
    (relationResidual edge)
    "target-position meaning transported to spread relation"

tarotSpreadFabric : Fabric.TypedHyperfabric PositionId SpreadRelation
tarotSpreadFabric = record
  { Fabric.vertexStalk = λ _ → LocalReading
  ; Fabric.edgeStalk = λ _ → RelationalReading
  ; Fabric.incidence = SpreadIncidence
  ; Fabric.restrict = restrictReading
  ; Fabric.edgeProvenance = relationProvenance
  ; Fabric.edgeSalience = relationSalience
  ; Fabric.fabricLabel =
      "tarot spread as a typed semantic hyperfabric"
  }

------------------------------------------------------------------------
-- Canonical inheritance / present constraint / possible development spread.
------------------------------------------------------------------------

inheritancePosition presentPosition developmentPosition : SpreadPosition
inheritancePosition =
  spreadPosition (positionId 0) inheritanceRole inheritedScale "inheritance"
presentPosition =
  spreadPosition (positionId 1) presentConstraintRole presentScale "present constraint"
developmentPosition =
  spreadPosition
    (positionId 2)
    possibleDevelopmentRole
    emergingScale
    "possible development"

inheritanceToPresent presentToDevelopment : SpreadRelation
inheritanceToPresent =
  spreadRelation
    (positionId 0)
    (positionId 1)
    qualifies
    Residual.partial
    ("spread-role edge" ∷ "inheritance qualifies present constraint" ∷ [])
    2
presentToDevelopment =
  spreadRelation
    (positionId 1)
    (positionId 2)
    developsInto
    Residual.partial
    ("spread-role edge" ∷ "present constraint bounds possible development" ∷ [])
    3

canonicalQuestion : String
canonicalQuestion = "What inheritance, present constraint, and possible development should be examined?"

inheritanceReading presentReading developmentReading : LocalReading
inheritanceReading =
  localReading
    inheritancePosition
    foolDraw
    (Semantic.meaning (Tarot.major Tarot.theFool))
    canonicalQuestion
    "situated reflective reading"
    "card plus role plus question plus context"
presentReading =
  localReading
    presentPosition
    hermitDraw
    (Semantic.meaning (Tarot.major Tarot.theHermit))
    canonicalQuestion
    "situated reflective reading"
    "card plus role plus question plus context"
developmentReading =
  localReading
    developmentPosition
    towerDraw
    (Semantic.meaning (Tarot.major Tarot.theTower))
    canonicalQuestion
    "situated reflective reading"
    "card plus role plus question plus context"

canonicalTransportRetainsResidual :
  retainedResidual
    (restrictReading
      {vertex = positionId 1}
      {edge = presentToDevelopment}
      (sourceMembership refl)
      presentReading)
  ≡ Residual.partial
canonicalTransportRetainsResidual = refl

canonicalSpreadObstruction :
  Fabric.HyperfabricObstruction
    {Residual = Residual.ResidualLevel}
    tarotSpreadFabric
canonicalSpreadObstruction = record
  { Fabric.obstructedEdge = presentToDevelopment
  ; Fabric.residual = Residual.partial
  ; Fabric.obstructionProvenance =
      "withdrawal/action tension"
      ∷ "different time scales remain possible"
      ∷ []
  ; Fabric.obstructionReceipt =
      "coherent reading may retain rather than erase relational tension"
  }

record TarotSpreadBoundary : Set where
  constructor tarotSpreadBoundary
  field
    layoutUsesDistinctDrawIndices : Bool
    finalPositionIsFixedFuture : Bool
    spreadRelationCanRetainResidual : Bool
    obstructionAutomaticallyDiagnosesQuerent : Bool

canonicalTarotSpreadBoundary : TarotSpreadBoundary
canonicalTarotSpreadBoundary =
  tarotSpreadBoundary true false true false
