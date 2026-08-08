module DASHI.Biology.JMDSporadicTarotOrdinalTotalisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotV2CorrespondenceExact as JMD
open JMD.TotalisedCorrespondence

------------------------------------------------------------------------
-- Sources and authority scope
--
-- J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker, R. A. Wilson,
-- Atlas of Finite Groups, Oxford University Press, 1985,
-- ISBN 0-19-853199-0; no DOI assigned.
--
-- R. T. Curtis, Natural Constructions of the Mathieu Groups,
-- Mathematical Proceedings of the Cambridge Philosophical Society 106
-- (1989), 423-429, DOI 10.1017/S0305004100068158.
--
-- The eponyms and conventional abbreviations are mathematical nomenclature.
-- JMD's Arcana allocation and the totalisation below are separately typed
-- symbolic correspondences.
------------------------------------------------------------------------

record SporadicNameRecord : Set where
  constructor sporadicNameRecord
  field
    abbreviation : String
    conventionalName : String
    namedFor : String
    naturalPermutationDegree : Sporadic.Optional Nat

open SporadicNameRecord public

sporadicName : Sporadic.SporadicGroup → SporadicNameRecord
sporadicName Sporadic.M11 = sporadicNameRecord "M11" "Mathieu group M11" "Emile Mathieu" (Sporadic.some 11)
sporadicName Sporadic.M12 = sporadicNameRecord "M12" "Mathieu group M12" "Emile Mathieu" (Sporadic.some 12)
sporadicName Sporadic.M22 = sporadicNameRecord "M22" "Mathieu group M22" "Emile Mathieu" (Sporadic.some 22)
sporadicName Sporadic.M23 = sporadicNameRecord "M23" "Mathieu group M23" "Emile Mathieu" (Sporadic.some 23)
sporadicName Sporadic.M24 = sporadicNameRecord "M24" "Mathieu group M24" "Emile Mathieu" (Sporadic.some 24)
sporadicName Sporadic.J1 = sporadicNameRecord "J1" "first Janko group" "Zvonimir Janko" Sporadic.none
sporadicName Sporadic.J2 = sporadicNameRecord "J2" "Hall-Janko group" "Zvonimir Janko" Sporadic.none
sporadicName Sporadic.J3 = sporadicNameRecord "J3" "third Janko group" "Zvonimir Janko" Sporadic.none
sporadicName Sporadic.J4 = sporadicNameRecord "J4" "fourth Janko group" "Zvonimir Janko" Sporadic.none
sporadicName Sporadic.HS = sporadicNameRecord "HS" "Higman-Sims group" "Donald Higman and Charles Sims" Sporadic.none
sporadicName Sporadic.McL = sporadicNameRecord "McL" "McLaughlin group" "Jack McLaughlin" Sporadic.none
sporadicName Sporadic.Suz = sporadicNameRecord "Suz" "sporadic Suzuki group" "Michio Suzuki" Sporadic.none
sporadicName Sporadic.Co1 = sporadicNameRecord "Co1" "first Conway group" "John Conway" Sporadic.none
sporadicName Sporadic.Co2 = sporadicNameRecord "Co2" "second Conway group" "John Conway" Sporadic.none
sporadicName Sporadic.Co3 = sporadicNameRecord "Co3" "third Conway group" "John Conway" Sporadic.none
sporadicName Sporadic.Fi22 = sporadicNameRecord "Fi22" "Fischer group Fi22" "Bernd Fischer" Sporadic.none
sporadicName Sporadic.Fi23 = sporadicNameRecord "Fi23" "Fischer group Fi23" "Bernd Fischer" Sporadic.none
sporadicName Sporadic.Fi24Prime = sporadicNameRecord "Fi24'" "simple Fischer group Fi24-prime" "Bernd Fischer" Sporadic.none
sporadicName Sporadic.He = sporadicNameRecord "He" "Held group" "Dieter Held" Sporadic.none
sporadicName Sporadic.HN = sporadicNameRecord "HN" "Harada-Norton group" "Koichiro Harada and Simon Norton" Sporadic.none
sporadicName Sporadic.Th = sporadicNameRecord "Th" "Thompson group" "John G. Thompson" Sporadic.none
sporadicName Sporadic.BabyMonster = sporadicNameRecord "B" "Baby Monster" "standard descriptive name" Sporadic.none
sporadicName Sporadic.Monster = sporadicNameRecord "M" "Fischer-Griess Monster" "Bernd Fischer and Robert Griess" Sporadic.none
sporadicName Sporadic.ONean = sporadicNameRecord "O'N" "O'Nan group" "Michael O'Nan" Sporadic.none
sporadicName Sporadic.Ru = sporadicNameRecord "Ru" "Rudvalis group" "Arunas Rudvalis" Sporadic.none
sporadicName Sporadic.Ly = sporadicNameRecord "Ly" "Lyons group" "Richard Lyons" Sporadic.none

mathieuDegreeRegression :
  naturalPermutationDegree (sporadicName Sporadic.M24) ≡ Sporadic.some 24
mathieuDegreeRegression = refl

data PosterBlock : Set where
  mathieuBlock conwayBlock hsMcLBlock jankoBlock terminalBlock omittedBlock : PosterBlock

posterBlock : Sporadic.SporadicGroup → PosterBlock
posterBlock Sporadic.M11 = mathieuBlock
posterBlock Sporadic.M12 = mathieuBlock
posterBlock Sporadic.M22 = mathieuBlock
posterBlock Sporadic.M23 = mathieuBlock
posterBlock Sporadic.M24 = mathieuBlock
posterBlock Sporadic.Co1 = conwayBlock
posterBlock Sporadic.Co2 = conwayBlock
posterBlock Sporadic.Co3 = conwayBlock
posterBlock Sporadic.HS = hsMcLBlock
posterBlock Sporadic.McL = hsMcLBlock
posterBlock Sporadic.J1 = jankoBlock
posterBlock Sporadic.J2 = jankoBlock
posterBlock Sporadic.J3 = jankoBlock
posterBlock Sporadic.J4 = jankoBlock
posterBlock Sporadic.Ru = terminalBlock
posterBlock Sporadic.Suz = terminalBlock
posterBlock Sporadic.ONean = terminalBlock
posterBlock Sporadic.Ly = terminalBlock
posterBlock Sporadic.Th = terminalBlock
posterBlock Sporadic.BabyMonster = terminalBlock
posterBlock Sporadic.Monster = terminalBlock
posterBlock _ = omittedBlock

posterOrdinal : Sporadic.SporadicGroup → Sporadic.Optional Nat
posterOrdinal Sporadic.M11 = Sporadic.some 0
posterOrdinal Sporadic.M12 = Sporadic.some 1
posterOrdinal Sporadic.M22 = Sporadic.some 2
posterOrdinal Sporadic.M23 = Sporadic.some 3
posterOrdinal Sporadic.M24 = Sporadic.some 4
posterOrdinal Sporadic.Co1 = Sporadic.some 5
posterOrdinal Sporadic.Co2 = Sporadic.some 6
posterOrdinal Sporadic.Co3 = Sporadic.some 7
posterOrdinal Sporadic.HS = Sporadic.some 9
posterOrdinal Sporadic.McL = Sporadic.some 10
posterOrdinal Sporadic.J1 = Sporadic.some 11
posterOrdinal Sporadic.J2 = Sporadic.some 12
posterOrdinal Sporadic.J3 = Sporadic.some 13
posterOrdinal Sporadic.J4 = Sporadic.some 14
posterOrdinal Sporadic.Ru = Sporadic.some 15
posterOrdinal Sporadic.Suz = Sporadic.some 16
posterOrdinal Sporadic.ONean = Sporadic.some 17
posterOrdinal Sporadic.Ly = Sporadic.some 18
posterOrdinal Sporadic.Th = Sporadic.some 19
posterOrdinal Sporadic.BabyMonster = Sporadic.some 20
posterOrdinal Sporadic.Monster = Sporadic.some 21
posterOrdinal _ = Sporadic.none

mathieuOrdinalBlockExact :
  posterOrdinal Sporadic.M11 ≡ Sporadic.some 0
  × posterOrdinal Sporadic.M12 ≡ Sporadic.some 1
  × posterOrdinal Sporadic.M22 ≡ Sporadic.some 2
  × posterOrdinal Sporadic.M23 ≡ Sporadic.some 3
  × posterOrdinal Sporadic.M24 ≡ Sporadic.some 4
mathieuOrdinalBlockExact = refl , refl , refl , refl , refl

jankoOrdinalBlockExact :
  posterOrdinal Sporadic.J1 ≡ Sporadic.some 11
  × posterOrdinal Sporadic.J2 ≡ Sporadic.some 12
  × posterOrdinal Sporadic.J3 ≡ Sporadic.some 13
  × posterOrdinal Sporadic.J4 ≡ Sporadic.some 14
jankoOrdinalBlockExact = refl , refl , refl , refl

syntheticCo4FillsOrdinalEight :
  Tarot.majorIndex
    (JMD.SyntheticPosterAssignment.arcana JMD.co4StrengthAssignment)
  ≡ 8
syntheticCo4FillsOrdinalEight = refl

data FitStrength : Set where
  noFit weakFit moderateFit strongFit maximalFit : FitStrength

record CorrespondenceScore : Set where
  constructor correspondenceScore
  field
    ordinalFit familyFit mathematicalFit narrativeFit : FitStrength

open CorrespondenceScore public

jmdScore : Sporadic.SporadicGroup → CorrespondenceScore
jmdScore Sporadic.M11 = correspondenceScore strongFit strongFit moderateFit strongFit
jmdScore Sporadic.M22 = correspondenceScore strongFit strongFit moderateFit strongFit
jmdScore Sporadic.M24 = correspondenceScore strongFit strongFit moderateFit strongFit
jmdScore Sporadic.Co1 = correspondenceScore strongFit strongFit moderateFit strongFit
jmdScore Sporadic.J1 = correspondenceScore maximalFit strongFit weakFit moderateFit
jmdScore Sporadic.J2 = correspondenceScore maximalFit strongFit weakFit moderateFit
jmdScore Sporadic.J3 = correspondenceScore maximalFit strongFit weakFit moderateFit
jmdScore Sporadic.J4 = correspondenceScore maximalFit strongFit weakFit moderateFit
jmdScore Sporadic.BabyMonster = correspondenceScore strongFit strongFit moderateFit strongFit
jmdScore Sporadic.Monster = correspondenceScore maximalFit strongFit moderateFit maximalFit
jmdScore g with JMD.status (JMD.jmdV2Assignment g)
... | JMD.assigned = correspondenceScore strongFit strongFit weakFit moderateFit
... | JMD.omitted = correspondenceScore noFit noFit noFit noFit

jankoScoreIsOrdinalFirst :
  ordinalFit (jmdScore Sporadic.J3) ≡ maximalFit
  × mathematicalFit (jmdScore Sporadic.J3) ≡ weakFit
jankoScoreIsOrdinalFirst = refl , refl

familyCompressionAssignment : Sporadic.SporadicGroup → Tarot.MajorArcana
familyCompressionAssignment Sporadic.Fi22 = Tarot.strength
familyCompressionAssignment Sporadic.Fi23 = Tarot.judgement
familyCompressionAssignment Sporadic.Fi24Prime = Tarot.theWorld
familyCompressionAssignment Sporadic.He = Tarot.theTower
familyCompressionAssignment Sporadic.HN = Tarot.theSun
familyCompressionAssignment g with JMD.arcana (JMD.jmdV2Assignment g)
... | Sporadic.some a = a
... | Sporadic.none = Tarot.strength

familyCompressionTotalisation : JMD.TotalisedCorrespondence
familyCompressionTotalisation = record
  { assignArcana = familyCompressionAssignment
  ; preservesM11 = refl
  ; preservesM12 = refl
  ; preservesM22 = refl
  ; preservesM23 = refl
  ; preservesM24 = refl
  ; preservesCo1 = refl
  ; preservesCo2 = refl
  ; preservesCo3 = refl
  ; preservesHS = refl
  ; preservesMcL = refl
  ; preservesJ1 = refl
  ; preservesJ2 = refl
  ; preservesJ3 = refl
  ; preservesJ4 = refl
  ; preservesRu = refl
  ; preservesSuz = refl
  ; preservesONean = refl
  ; preservesLy = refl
  ; preservesTh = refl
  ; preservesBabyMonster = refl
  ; preservesMonster = refl
  ; fi22Rationale = "Fi22 occupies Strength as the first actual Monster-section replacement for the poster's synthetic block-completion Co4 label."
  ; fi23Rationale = "Fi23 shares Judgement with the Baby Monster under an explicitly declared Monster-section compression fibre."
  ; fi24PrimeRationale = "Fi24-prime shares The World with the Monster as the terminal Fischer-family member in this declared compression policy."
  ; heldRationale = "Held shares The Tower with Suz as a declared exceptional-transition fibre; this is symbolic rather than a group-theoretic identity."
  ; haradaNortonRationale = "Harada-Norton shares The Sun with Thompson as a declared late Monster-section illumination fibre."
  ; fi22Authority = Sporadic.declaredSymbolicAuthority
  ; fi23Authority = Sporadic.declaredSymbolicAuthority
  ; fi24PrimeAuthority = Sporadic.declaredSymbolicAuthority
  ; heldAuthority = Sporadic.declaredSymbolicAuthority
  ; haradaNortonAuthority = Sporadic.declaredSymbolicAuthority
  }

fi22FillsActualStrengthSlot :
  familyCompressionAssignment Sporadic.Fi22 ≡ Tarot.strength
fi22FillsActualStrengthSlot = refl

fi23BabyMonsterCollision :
  familyCompressionAssignment Sporadic.Fi23
  ≡ familyCompressionAssignment Sporadic.BabyMonster
fi23BabyMonsterCollision = refl

fi24MonsterCollision :
  familyCompressionAssignment Sporadic.Fi24Prime
  ≡ familyCompressionAssignment Sporadic.Monster
fi24MonsterCollision = refl

heldSuzCollision :
  familyCompressionAssignment Sporadic.He
  ≡ familyCompressionAssignment Sporadic.Suz
heldSuzCollision = refl

haradaNortonThompsonCollision :
  familyCompressionAssignment Sporadic.HN
  ≡ familyCompressionAssignment Sporadic.Th
haradaNortonThompsonCollision = refl

record TotalisationAuthorityBoundary : Set where
  constructor totalisationAuthorityBoundary
  field
    totalMapNowConstructed : Bool
    totalMapNowConstructedIsTrue : totalMapNowConstructed ≡ true
    totalMapIsSourceForced : Bool
    totalMapIsSourceForcedIsFalse : totalMapIsSourceForced ≡ false
    totalMapIsUnique : Bool
    totalMapIsUniqueIsFalse : totalMapIsUnique ≡ false
    collisionsExplicit : Bool
    collisionsExplicitIsTrue : collisionsExplicit ≡ true
    symbolicRationalesPromotedToGroupTheorems : Bool
    symbolicRationalesPromotedToGroupTheoremsIsFalse :
      symbolicRationalesPromotedToGroupTheorems ≡ false

canonicalTotalisationAuthorityBoundary : TotalisationAuthorityBoundary
canonicalTotalisationAuthorityBoundary =
  totalisationAuthorityBoundary true refl false refl false refl true refl false refl
