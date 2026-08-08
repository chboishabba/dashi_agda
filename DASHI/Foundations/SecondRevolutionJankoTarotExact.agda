module DASHI.Foundations.SecondRevolutionJankoTarotExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotV2CorrespondenceExact as JMD

------------------------------------------------------------------------
-- The second revolution is dual-addressed.  Each global index 11..14 is both
-- 10 plus a fresh local offset and 9 plus a post-system offset.  The Janko and
-- Arcana labels are source-faithful index maps, not identities of carriers.
------------------------------------------------------------------------

data JankoIndex : Set where
  janko1 janko2 janko3 janko4 : JankoIndex

localOffset : JankoIndex → Nat
localOffset janko1 = 1
localOffset janko2 = 2
localOffset janko3 = 3
localOffset janko4 = 4

globalAddress : JankoIndex → Nat
globalAddress janko1 = 11
globalAddress janko2 = 12
globalAddress janko3 = 13
globalAddress janko4 = 14

globalIsTenPlusLocalOffset :
  (index : JankoIndex) →
  10 + localOffset index ≡ globalAddress index
globalIsTenPlusLocalOffset janko1 = refl
globalIsTenPlusLocalOffset janko2 = refl
globalIsTenPlusLocalOffset janko3 = refl
globalIsTenPlusLocalOffset janko4 = refl

globalIsNinePlusLocalSuccessor :
  (index : JankoIndex) →
  9 + (1 + localOffset index) ≡ globalAddress index
globalIsNinePlusLocalSuccessor janko1 = refl
globalIsNinePlusLocalSuccessor janko2 = refl
globalIsNinePlusLocalSuccessor janko3 = refl
globalIsNinePlusLocalSuccessor janko4 = refl

jankoGroup : JankoIndex → Sporadic.SporadicGroup
jankoGroup janko1 = Sporadic.J1
jankoGroup janko2 = Sporadic.J2
jankoGroup janko3 = Sporadic.J3
jankoGroup janko4 = Sporadic.J4

jankoArcana : JankoIndex → Tarot.MajorArcana
jankoArcana janko1 = Tarot.justice
jankoArcana janko2 = Tarot.theHangedMan
jankoArcana janko3 = Tarot.death
jankoArcana janko4 = Tarot.temperance

record DualRevolutionAddress : Set where
  constructor dualRevolutionAddress
  field
    index : JankoIndex
    global : Nat
    carryRelativeOffset : Nat
    systemRelativeOffset : Nat
    globalExact : global ≡ globalAddress index
    carryOffsetExact : carryRelativeOffset ≡ localOffset index
    carryChart : 10 + carryRelativeOffset ≡ global
    systemChart : 9 + systemRelativeOffset ≡ global
    systemOffsetIsCarrySuccessor :
      systemRelativeOffset ≡ 1 + carryRelativeOffset

open DualRevolutionAddress public

address11 : DualRevolutionAddress
address11 = dualRevolutionAddress janko1 11 1 2 refl refl refl refl refl

address12 : DualRevolutionAddress
address12 = dualRevolutionAddress janko2 12 2 3 refl refl refl refl refl

address13 : DualRevolutionAddress
address13 = dualRevolutionAddress janko3 13 3 4 refl refl refl refl refl

address14 : DualRevolutionAddress
address14 = dualRevolutionAddress janko4 14 4 5 refl refl refl refl refl

------------------------------------------------------------------------
-- Source-faithful compatibility with the JMD poster.
------------------------------------------------------------------------

j1PosterCompatibility :
  JMD.arcana (JMD.jmdV2Assignment (jankoGroup janko1))
  ≡ Sporadic.some (jankoArcana janko1)
j1PosterCompatibility = refl

j2PosterCompatibility :
  JMD.arcana (JMD.jmdV2Assignment (jankoGroup janko2))
  ≡ Sporadic.some (jankoArcana janko2)
j2PosterCompatibility = refl

j3PosterCompatibility :
  JMD.arcana (JMD.jmdV2Assignment (jankoGroup janko3))
  ≡ Sporadic.some (jankoArcana janko3)
j3PosterCompatibility = refl

j4PosterCompatibility :
  JMD.arcana (JMD.jmdV2Assignment (jankoGroup janko4))
  ≡ Sporadic.some (jankoArcana janko4)
j4PosterCompatibility = refl

------------------------------------------------------------------------
-- Structural and mythic projections are separate records.  The structural
-- chart is exact arithmetic; the prose remains a declared symbolic lens.
------------------------------------------------------------------------

record RevolutionStructuralReading : Set where
  constructor revolutionStructuralReading
  field
    address : DualRevolutionAddress
    carryRelativeRole : String
    systemRelativeRole : String

justiceStructuralReading : RevolutionStructuralReading
justiceStructuralReading =
  revolutionStructuralReading address11
    "fresh witness attached to a carried ten-bundle"
    "second coordinate beyond completed systemic nine"

hangedStructuralReading : RevolutionStructuralReading
hangedStructuralReading =
  revolutionStructuralReading address12
    "renewed relation at the promoted scale"
    "new post-system local closure"

deathStructuralReading : RevolutionStructuralReading
deathStructuralReading =
  revolutionStructuralReading address13
    "new triadic closure after the carry"
    "counterframe exposed beyond the old system"

temperanceStructuralReading : RevolutionStructuralReading
temperanceStructuralReading =
  revolutionStructuralReading address14
    "tetralemma retained at the promoted scale"
    "decision and mediation gate beyond systemic closure"

record SoftMythicProjection : Set where
  constructor softMythicProjection
  field
    index : JankoIndex
    structuralReading : RevolutionStructuralReading
    narrative : String
    sourceOrdinalFact : Bool
    sourceOrdinalFactIsTrue : sourceOrdinalFact ≡ true
    groupTheoryForcesNarrative : Bool
    groupTheoryForcesNarrativeIsFalse : groupTheoryForcesNarrative ≡ false

jankoMythicProjection : JankoIndex → SoftMythicProjection
jankoMythicProjection janko1 =
  softMythicProjection janko1 justiceStructuralReading
    "Justice: a fresh witness asks the carried system to account for itself."
    true refl false refl
jankoMythicProjection janko2 =
  softMythicProjection janko2 hangedStructuralReading
    "Hanged Man: relation is suspended and reoriented within a new closure."
    true refl false refl
jankoMythicProjection janko3 =
  softMythicProjection janko3 deathStructuralReading
    "Death: a new closure exposes the counterframe of the previous totality."
    true refl false refl
jankoMythicProjection janko4 =
  softMythicProjection janko4 temperanceStructuralReading
    "Temperance: counterpositions are mediated without claiming terminal synthesis."
    true refl false refl

record JankoStageBridgeBoundary : Set where
  constructor jankoStageBridgeBoundary
  field
    tenPlusNIndexRuleExact : Bool
    tenPlusNIndexRuleExactIsTrue : tenPlusNIndexRuleExact ≡ true
    carryChartWitness :
      (index : JankoIndex) →
      10 + localOffset index ≡ globalAddress index
    ninePlusSuccessorRuleExact : Bool
    ninePlusSuccessorRuleExactIsTrue : ninePlusSuccessorRuleExact ≡ true
    systemChartWitness :
      (index : JankoIndex) →
      9 + (1 + localOffset index) ≡ globalAddress index
    stageCarrierIdentifiedWithJankoGroup : Bool
    stageCarrierIdentifiedWithJankoGroupIsFalse :
      stageCarrierIdentifiedWithJankoGroup ≡ false
    tarotNarrativeForcedByGroupTheory : Bool
    tarotNarrativeForcedByGroupTheoryIsFalse :
      tarotNarrativeForcedByGroupTheory ≡ false

canonicalJankoStageBridgeBoundary : JankoStageBridgeBoundary
canonicalJankoStageBridgeBoundary =
  jankoStageBridgeBoundary
    true refl globalIsTenPlusLocalOffset
    true refl globalIsNinePlusLocalSuccessor
    false refl
    false refl
