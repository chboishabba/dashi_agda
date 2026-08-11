module DASHI.Biology.JMDSporadicTarotV2CorrespondenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot

------------------------------------------------------------------------
-- Source-faithful transcription of JMD's displayed
-- "Math Sporadic Group + Kaballah Tarot v2" poster.
--
-- The poster has twenty-two Arcana slots, twenty-one actual sporadic-group
-- labels, and one synthetic Co4 label.  Five actual sporadic groups are not
-- displayed.  They remain explicit omissions; no aesthetic assignment is
-- invented for them.
------------------------------------------------------------------------

data PosterAuthority : Set where
  displayedGroupAssignment : PosterAuthority
  displayedSyntheticAssignment : PosterAuthority
  displayedOmission : PosterAuthority

data AssignmentStatus : Set where
  assigned : AssignmentStatus
  omitted : AssignmentStatus

record SourceFaithfulAssignment : Set where
  constructor sourceFaithfulAssignment
  field
    arcana : Sporadic.Optional Tarot.MajorArcana
    status : AssignmentStatus
    rationale : String
    authority : PosterAuthority

open SourceFaithfulAssignment public

jmdV2Assignment : Sporadic.SporadicGroup → SourceFaithfulAssignment
jmdV2Assignment Sporadic.M11 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theFool) assigned
    "Poster card 0 labels M11 as The Fool: smallest sporadic, beginnings and potential."
    displayedGroupAssignment
jmdV2Assignment Sporadic.M12 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theMagician) assigned
    "Poster card I labels M12 as The Magician: symmetry harnessed into manifestation."
    displayedGroupAssignment
jmdV2Assignment Sporadic.M22 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theHighPriestess) assigned
    "Poster card II labels M22 as The High Priestess: hidden symmetry and the 22-point action."
    displayedGroupAssignment
jmdV2Assignment Sporadic.M23 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theEmpress) assigned
    "Poster card III labels M23 as The Empress: generative abundance and 23-point symmetry."
    displayedGroupAssignment
jmdV2Assignment Sporadic.M24 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theEmperor) assigned
    "Poster card IV labels M24 as The Emperor: order, rule and the largest Mathieu group."
    displayedGroupAssignment

jmdV2Assignment Sporadic.J2 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theHangedMan) assigned
    "Poster card XII labels J2 as The Hanged Man: changed perspective and relation to J1."
    displayedGroupAssignment
jmdV2Assignment Sporadic.HS =
  sourceFaithfulAssignment (Sporadic.some Tarot.theHermit) assigned
    "Poster card IX labels HS as The Hermit: solitary search and hidden mathematical chambers."
    displayedGroupAssignment
jmdV2Assignment Sporadic.McL =
  sourceFaithfulAssignment (Sporadic.some Tarot.wheelOfFortune) assigned
    "Poster card X labels McL as Wheel of Fortune: cycles and turning mathematical wheels."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Suz =
  sourceFaithfulAssignment (Sporadic.some Tarot.theTower) assigned
    "Poster card XVI labels Suz as The Tower: sudden upheaval and revelation through destruction."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Co1 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theHierophant) assigned
    "Poster card V labels Co1 as The Hierophant: transmitted structure and Leech-lattice knowledge."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Co2 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theLovers) assigned
    "Poster card VI labels Co2 as The Lovers: harmony, choice and relational symmetry."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Co3 =
  sourceFaithfulAssignment (Sporadic.some Tarot.theChariot) assigned
    "Poster card VII labels Co3 as The Chariot: directed motion through a space of possibilities."
    displayedGroupAssignment

jmdV2Assignment Sporadic.Fi22 =
  sourceFaithfulAssignment Sporadic.none omitted
    "Fi22 is one of the five actual sporadic groups omitted from the displayed v2 poster."
    displayedOmission
jmdV2Assignment Sporadic.Fi23 =
  sourceFaithfulAssignment Sporadic.none omitted
    "Fi23 is one of the five actual sporadic groups omitted from the displayed v2 poster."
    displayedOmission
jmdV2Assignment Sporadic.Fi24Prime =
  sourceFaithfulAssignment Sporadic.none omitted
    "Fi24-prime is one of the five actual sporadic groups omitted from the displayed v2 poster."
    displayedOmission
jmdV2Assignment Sporadic.He =
  sourceFaithfulAssignment Sporadic.none omitted
    "Held is one of the five actual sporadic groups omitted from the displayed v2 poster."
    displayedOmission
jmdV2Assignment Sporadic.HN =
  sourceFaithfulAssignment Sporadic.none omitted
    "Harada-Norton is one of the five actual sporadic groups omitted from the displayed v2 poster."
    displayedOmission
jmdV2Assignment Sporadic.Th =
  sourceFaithfulAssignment (Sporadic.some Tarot.theSun) assigned
    "Poster card XIX labels Th as The Sun: illumination, clarity and truth revealed."
    displayedGroupAssignment
jmdV2Assignment Sporadic.BabyMonster =
  sourceFaithfulAssignment (Sporadic.some Tarot.judgement) assigned
    "Poster card XX labels the Baby Monster as Judgement: awakening and relation to the Monster."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Monster =
  sourceFaithfulAssignment (Sporadic.some Tarot.theWorld) assigned
    "Poster card XXI labels the Monster as The World: completion, unity and total symmetry."
    displayedGroupAssignment

jmdV2Assignment Sporadic.J1 =
  sourceFaithfulAssignment (Sporadic.some Tarot.justice) assigned
    "Poster card XI labels J1 as Justice: balance, law and a small but profound structure."
    displayedGroupAssignment
jmdV2Assignment Sporadic.J3 =
  sourceFaithfulAssignment (Sporadic.some Tarot.death) assigned
    "Poster card XIII labels J3 as Death: endings and transformation beyond form."
    displayedGroupAssignment
jmdV2Assignment Sporadic.J4 =
  sourceFaithfulAssignment (Sporadic.some Tarot.temperance) assigned
    "Poster card XIV labels J4 as Temperance: balance and mixing opposites into harmony."
    displayedGroupAssignment
jmdV2Assignment Sporadic.ONean =
  sourceFaithfulAssignment (Sporadic.some Tarot.theStar) assigned
    "Poster card XVII labels O'Nan as The Star: hope and guidance from distant symmetries."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Ru =
  sourceFaithfulAssignment (Sporadic.some Tarot.theDevil) assigned
    "Poster card XV labels Ru as The Devil: bondage to structure and the shadow of symmetry."
    displayedGroupAssignment
jmdV2Assignment Sporadic.Ly =
  sourceFaithfulAssignment (Sporadic.some Tarot.theMoon) assigned
    "Poster card XVIII labels Ly as The Moon: intuition, dreams and the unseen tide."
    displayedGroupAssignment

------------------------------------------------------------------------
-- The synthetic Co4 card occupies Strength in the poster but has no sporadic
-- Conway referent.  Its symbolic assignment is represented in a separate type.
------------------------------------------------------------------------

record SyntheticPosterAssignment : Set where
  constructor syntheticPosterAssignment
  field
    label : Sporadic.ConwayCardLabel
    arcana : Tarot.MajorArcana
    rationale : String
    authority : PosterAuthority

open SyntheticPosterAssignment public

co4StrengthAssignment : SyntheticPosterAssignment
co4StrengthAssignment =
  syntheticPosterAssignment Sporadic.Co4SyntheticCard Tarot.strength
    "Poster card VIII labels synthetic Co4 as Strength; the mathematical ledger retains no Conway-sporadic referent."
    displayedSyntheticAssignment

co4StillHasNoMathematicalReferent :
  Sporadic.conwayCardReferent Sporadic.Co4SyntheticCard ≡ Sporadic.none
co4StillHasNoMathematicalReferent = Sporadic.co4HasNoConwaySporadicReferent

------------------------------------------------------------------------
-- Exact source accounting.
------------------------------------------------------------------------

assignedActualGroupCount : Nat
assignedActualGroupCount = 21

omittedActualGroupCount : Nat
omittedActualGroupCount = 5

syntheticCardCount : Nat
syntheticCardCount = 1

posterCardCount : Nat
posterCardCount = assignedActualGroupCount + syntheticCardCount

actualInventoryAccounting : assignedActualGroupCount + omittedActualGroupCount ≡ 26
actualInventoryAccounting = refl

posterCardCountIsTwentyTwo : posterCardCount ≡ 22
posterCardCountIsTwentyTwo = refl

------------------------------------------------------------------------
-- A genuine total Phi : S26 -> A22 is a separate completion object.  It must
-- extend every displayed actual-group assignment and explicitly fill the five
-- source omissions.  Source faithfulness alone cannot construct it.
------------------------------------------------------------------------

record TotalisedCorrespondence : Set where
  constructor totalisedCorrespondence
  field
    assignArcana : Sporadic.SporadicGroup → Tarot.MajorArcana

    preservesM11 : assignArcana Sporadic.M11 ≡ Tarot.theFool
    preservesM12 : assignArcana Sporadic.M12 ≡ Tarot.theMagician
    preservesM22 : assignArcana Sporadic.M22 ≡ Tarot.theHighPriestess
    preservesM23 : assignArcana Sporadic.M23 ≡ Tarot.theEmpress
    preservesM24 : assignArcana Sporadic.M24 ≡ Tarot.theEmperor
    preservesCo1 : assignArcana Sporadic.Co1 ≡ Tarot.theHierophant
    preservesCo2 : assignArcana Sporadic.Co2 ≡ Tarot.theLovers
    preservesCo3 : assignArcana Sporadic.Co3 ≡ Tarot.theChariot
    preservesHS : assignArcana Sporadic.HS ≡ Tarot.theHermit
    preservesMcL : assignArcana Sporadic.McL ≡ Tarot.wheelOfFortune
    preservesJ1 : assignArcana Sporadic.J1 ≡ Tarot.justice
    preservesJ2 : assignArcana Sporadic.J2 ≡ Tarot.theHangedMan
    preservesJ3 : assignArcana Sporadic.J3 ≡ Tarot.death
    preservesJ4 : assignArcana Sporadic.J4 ≡ Tarot.temperance
    preservesRu : assignArcana Sporadic.Ru ≡ Tarot.theDevil
    preservesSuz : assignArcana Sporadic.Suz ≡ Tarot.theTower
    preservesONean : assignArcana Sporadic.ONean ≡ Tarot.theStar
    preservesLy : assignArcana Sporadic.Ly ≡ Tarot.theMoon
    preservesTh : assignArcana Sporadic.Th ≡ Tarot.theSun
    preservesBabyMonster : assignArcana Sporadic.BabyMonster ≡ Tarot.judgement
    preservesMonster : assignArcana Sporadic.Monster ≡ Tarot.theWorld

    fi22Rationale : String
    fi23Rationale : String
    fi24PrimeRationale : String
    heldRationale : String
    haradaNortonRationale : String

    fi22Authority : Sporadic.CorrespondenceAuthority
    fi23Authority : Sporadic.CorrespondenceAuthority
    fi24PrimeAuthority : Sporadic.CorrespondenceAuthority
    heldAuthority : Sporadic.CorrespondenceAuthority
    haradaNortonAuthority : Sporadic.CorrespondenceAuthority

record JMDV2CorrespondenceBoundary : Set where
  constructor jmdV2CorrespondenceBoundary
  field
    posterSuppliesTotalS26ToA22Map : Bool
    posterSuppliesTotalS26ToA22MapIsFalse :
      posterSuppliesTotalS26ToA22Map ≡ false

    syntheticCo4CreatesSporadicGroup : Bool
    syntheticCo4CreatesSporadicGroupIsFalse :
      syntheticCo4CreatesSporadicGroup ≡ false

    omittedGroupsMayBeAssignedWithoutRationale : Bool
    omittedGroupsMayBeAssignedWithoutRationaleIsFalse :
      omittedGroupsMayBeAssignedWithoutRationale ≡ false

    sourceFaithfulPartialRuleProvided : Bool
    sourceFaithfulPartialRuleProvidedIsTrue :
      sourceFaithfulPartialRuleProvided ≡ true

open JMDV2CorrespondenceBoundary public

canonicalJMDV2CorrespondenceBoundary : JMDV2CorrespondenceBoundary
canonicalJMDV2CorrespondenceBoundary =
  jmdV2CorrespondenceBoundary false refl false refl false refl true refl
