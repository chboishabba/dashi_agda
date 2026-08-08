module DASHI.Biology.JMDSporadicTarotV2Regression where

open import DASHI.Core.Prelude

import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotV2CorrespondenceExact as JMD

m11FoolRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.M11)
  ≡ Sporadic.some Tarot.theFool
m11FoolRegression = refl

co1HierophantRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.Co1)
  ≡ Sporadic.some Tarot.theHierophant
co1HierophantRegression = refl

j1JusticeRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.J1)
  ≡ Sporadic.some Tarot.justice
j1JusticeRegression = refl

monsterWorldRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.Monster)
  ≡ Sporadic.some Tarot.theWorld
monsterWorldRegression = refl

fi22OmissionRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.Fi22)
  ≡ Sporadic.none
fi22OmissionRegression = refl

haradaNortonOmissionRegression :
  JMD.arcana (JMD.jmdV2Assignment Sporadic.HN)
  ≡ Sporadic.none
haradaNortonOmissionRegression = refl

co4StrengthRegression :
  JMD.SyntheticPosterAssignment.arcana JMD.co4StrengthAssignment
  ≡ Tarot.strength
co4StrengthRegression = refl

co4NoReferentRegression :
  Sporadic.conwayCardReferent Sporadic.Co4SyntheticCard ≡ Sporadic.none
co4NoReferentRegression = JMD.co4StillHasNoMathematicalReferent

actualInventoryAccountingRegression :
  JMD.assignedActualGroupCount + JMD.omittedActualGroupCount ≡ 26
actualInventoryAccountingRegression = JMD.actualInventoryAccounting

posterCardCountRegression : JMD.posterCardCount ≡ 22
posterCardCountRegression = JMD.posterCardCountIsTwentyTwo

boundaryRegression : JMD.JMDV2CorrespondenceBoundary
boundaryRegression = JMD.canonicalJMDV2CorrespondenceBoundary
