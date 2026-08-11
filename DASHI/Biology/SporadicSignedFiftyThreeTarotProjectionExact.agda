module DASHI.Biology.SporadicSignedFiftyThreeTarotProjectionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact as Candidate
import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotOrdinalTotalisationExact as Total

------------------------------------------------------------------------
-- The previously formalised 53 candidate has one fixed point and twenty-six
-- binary fibres.  This module constructs the corresponding carrier directly
-- over the actual 26-element SporadicGroup type:
--
--   1_star + SporadicGroup x C2.
--
-- It remains a candidate presentation of the repository's ReducedMode53 until
-- an explicit equivalence and intertwiner are supplied.
------------------------------------------------------------------------

SporadicSigned53 : Set
SporadicSigned53 = ⊤ ⊎ (Sporadic.SporadicGroup × Candidate.BinaryFibre)

SignedSporadic52 : Set
SignedSporadic52 = Sporadic.SporadicGroup × Candidate.BinaryFibre

sporadicLabelCount : Nat
sporadicLabelCount = Sporadic.sporadicInventoryCount

polarityCount : Nat
polarityCount = Candidate.binaryFibreCount

signedSporadicDimension : Nat
signedSporadicDimension = sporadicLabelCount * polarityCount

sporadicSignedDimension : Nat
sporadicSignedDimension = 1 + signedSporadicDimension

signedSporadicDimensionIsFiftyTwo : signedSporadicDimension ≡ 52
signedSporadicDimensionIsFiftyTwo = refl

sporadicSignedDimensionIsFiftyThree : sporadicSignedDimension ≡ 53
sporadicSignedDimensionIsFiftyThree = refl

sporadicSignedDimensionMatchesCandidate :
  sporadicSignedDimension ≡ Candidate.candidateR53Dimension
sporadicSignedDimensionMatchesCandidate = refl

sporadicSignedFixedPoint : SporadicSigned53
sporadicSignedFixedPoint = inj₁ tt

sporadicSignedState :
  Sporadic.SporadicGroup → Candidate.BinaryFibre → SporadicSigned53
sporadicSignedState group polarity = inj₂ (group , polarity)

sporadicSignedInvolution : SporadicSigned53 → SporadicSigned53
sporadicSignedInvolution (inj₁ tt) = inj₁ tt
sporadicSignedInvolution (inj₂ (group , polarity)) =
  inj₂ (group , Candidate.flipBinaryFibre polarity)

sporadicSignedInvolutionIsInvolutive :
  (state : SporadicSigned53) →
  sporadicSignedInvolution (sporadicSignedInvolution state) ≡ state
sporadicSignedInvolutionIsInvolutive (inj₁ tt) = refl
sporadicSignedInvolutionIsInvolutive (inj₂ (group , polarity))
  with Candidate.flipBinaryFibreInvolutive polarity
... | refl = refl

sporadicSignedFixedPointIsFixed :
  sporadicSignedInvolution sporadicSignedFixedPoint ≡ sporadicSignedFixedPoint
sporadicSignedFixedPointIsFixed = refl

------------------------------------------------------------------------
-- Independent projections retain the group label, binary fibre, and its
-- several observer vocabularies.  The observer codomains remain distinct.
------------------------------------------------------------------------

groupProjection : SporadicSigned53 → Sporadic.Optional Sporadic.SporadicGroup
groupProjection (inj₁ tt) = Sporadic.none
groupProjection (inj₂ (group , polarity)) = Sporadic.some group

polarityProjection :
  SporadicSigned53 → Sporadic.Optional Candidate.BinaryFibre
polarityProjection (inj₁ tt) = Sporadic.none
polarityProjection (inj₂ (group , polarity)) = Sporadic.some polarity

record SignedSporadicObservers : Set where
  constructor signedSporadicObservers
  field
    group : Sporadic.SporadicGroup
    fibre : Candidate.BinaryFibre
    sign : Candidate.SignObservation
    transport : Candidate.TransportObservation
    tarotPolarity : Candidate.TarotPolarityObservation
    orientation : Candidate.OrientationObservation
    signExact : sign ≡ Candidate.observeSign fibre
    transportExact : transport ≡ Candidate.observeTransport fibre
    tarotPolarityExact : tarotPolarity ≡ Candidate.observeTarotPolarity fibre
    orientationExact : orientation ≡ Candidate.observeOrientation fibre

open SignedSporadicObservers public

observeSignedSporadic :
  Sporadic.SporadicGroup → Candidate.BinaryFibre → SignedSporadicObservers
observeSignedSporadic group fibre =
  signedSporadicObservers
    group fibre
    (Candidate.observeSign fibre)
    (Candidate.observeTransport fibre)
    (Candidate.observeTarotPolarity fibre)
    (Candidate.observeOrientation fibre)
    refl refl refl refl

------------------------------------------------------------------------
-- The 22-card deck is downstream of the signed 53 carrier.  The centre card
-- is an explicit parameter; no traditional or source-forced centre is assumed.
-- The two polarities of one group share a card while retaining distinct light /
-- shadow observations.
------------------------------------------------------------------------

arcanaProjectionWithCentre :
  Tarot.MajorArcana → SporadicSigned53 → Tarot.MajorArcana
arcanaProjectionWithCentre centre (inj₁ tt) = centre
arcanaProjectionWithCentre centre (inj₂ (group , polarity)) =
  Total.familyCompressionAssignment group

canonicalArcanaProjection : SporadicSigned53 → Tarot.MajorArcana
canonicalArcanaProjection = arcanaProjectionWithCentre Tarot.theWorld

record SignedTarotReading : Set where
  constructor signedTarotReading
  field
    state : SporadicSigned53
    card : Tarot.MajorArcana
    group : Sporadic.Optional Sporadic.SporadicGroup
    polarity : Sporadic.Optional Candidate.TarotPolarityObservation
    cardExact : card ≡ canonicalArcanaProjection state

open SignedTarotReading public

readSignedTarot : SporadicSigned53 → SignedTarotReading
readSignedTarot (inj₁ tt) =
  signedTarotReading
    (inj₁ tt)
    Tarot.theWorld
    Sporadic.none
    Sporadic.none
    refl
readSignedTarot (inj₂ (group , fibre)) =
  signedTarotReading
    (inj₂ (group , fibre))
    (Total.familyCompressionAssignment group)
    (Sporadic.some group)
    (Sporadic.some (Candidate.observeTarotPolarity fibre))
    refl

polaritiesShareArcana :
  (group : Sporadic.SporadicGroup) →
  canonicalArcanaProjection
    (sporadicSignedState group Candidate.positiveFibre)
  ≡
  canonicalArcanaProjection
    (sporadicSignedState group Candidate.negativeFibre)
polaritiesShareArcana group = refl

polaritiesRetainDistinctTarotObservation :
  (group : Sporadic.SporadicGroup) →
  SignedTarotReading.polarity
    (readSignedTarot
      (sporadicSignedState group Candidate.positiveFibre))
  ≡ Sporadic.some Candidate.lightAspectObservation
  ×
  SignedTarotReading.polarity
    (readSignedTarot
      (sporadicSignedState group Candidate.negativeFibre))
  ≡ Sporadic.some Candidate.shadowAspectObservation
polaritiesRetainDistinctTarotObservation group = refl , refl

------------------------------------------------------------------------
-- The extra mean/global line gives the 54-carrier chart used by the existing
-- Moonshine arithmetic.  These are cardinal ledgers, not module isomorphisms.
------------------------------------------------------------------------

SporadicSigned54 : Set
SporadicSigned54 = ⊤ ⊎ SporadicSigned53

sporadicSigned54Dimension : Nat
sporadicSigned54Dimension = 1 + sporadicSignedDimension

sporadicSigned54DimensionIsFiftyFour : sporadicSigned54Dimension ≡ 54
sporadicSigned54DimensionIsFiftyFour = refl

fiftyFourAnatomy : 1 + (1 + 26 * 2) ≡ 54
fiftyFourAnatomy = refl

fiftyThreeAnatomy : 1 + 26 * 2 ≡ 53
fiftyThreeAnatomy = refl

monsterBulkPlusSignedCandidate : 196830 + (1 + 26 * 2) ≡ 196883
monsterBulkPlusSignedCandidate = refl

moonshineBulkPlusMeanAndSignedCandidate :
  196830 + (1 + (1 + 26 * 2)) ≡ 196884
moonshineBulkPlusMeanAndSignedCandidate = refl

------------------------------------------------------------------------
-- Representation-theoretic dimension ledger suggested by
--
--   1_star + P26 + (P26 tensor sign)
--   = 1_star + 1 + sign + V25 + (V25 tensor sign).
--
-- No vector spaces, S26 action, sign character, or decomposition is promoted
-- from the dimension equations alone.
------------------------------------------------------------------------

permutationModuleDimension : Nat
permutationModuleDimension = 26

standardModuleDimension : Nat
standardModuleDimension = 25

signedPermutationLinearisationDimension : Nat
signedPermutationLinearisationDimension =
  1 + permutationModuleDimension + permutationModuleDimension

signedPermutationLinearisationDimensionIsFiftyThree :
  signedPermutationLinearisationDimension ≡ 53
signedPermutationLinearisationDimensionIsFiftyThree = refl

candidateIrrepDimensionLedger : 1 + 1 + 1 + 25 + 25 ≡ 53
candidateIrrepDimensionLedger = refl

------------------------------------------------------------------------
-- Twenty-two Kabbalistic/Hebrew path slots are retained only as an index
-- carrier.  The supplied poster does not provide a complete letter/path map.
------------------------------------------------------------------------

KabbalisticPath22 : Set
KabbalisticPath22 = Sporadic.Arcana22

record KabbalisticPathBoundary : Set where
  constructor kabbalisticPathBoundary
  field
    pathSlotCount : Nat
    pathSlotCountIsTwentyTwo : pathSlotCount ≡ 22
    completeHebrewLetterAssignmentSupplied : Bool
    completeHebrewLetterAssignmentSuppliedIsFalse :
      completeHebrewLetterAssignmentSupplied ≡ false
    treeOfLifeIncidenceSupplied : Bool
    treeOfLifeIncidenceSuppliedIsFalse : treeOfLifeIncidenceSupplied ≡ false

canonicalKabbalisticPathBoundary : KabbalisticPathBoundary
canonicalKabbalisticPathBoundary =
  kabbalisticPathBoundary 22 refl false refl false refl

record SporadicSignedFiftyThreeBoundary : Set where
  constructor sporadicSignedFiftyThreeBoundary
  field
    sporadicSignedCarrierConstructed : Bool
    sporadicSignedCarrierConstructedIsTrue :
      sporadicSignedCarrierConstructed ≡ true
    actualReducedMode53EquivalenceConstructed : Bool
    actualReducedMode53EquivalenceConstructedIsFalse :
      actualReducedMode53EquivalenceConstructed ≡ false
    s26RepresentationConstructed : Bool
    s26RepresentationConstructedIsFalse :
      s26RepresentationConstructed ≡ false
    signTwistedModuleConstructed : Bool
    signTwistedModuleConstructedIsFalse :
      signTwistedModuleConstructed ≡ false
    monsterIntertwinerConstructed : Bool
    monsterIntertwinerConstructedIsFalse :
      monsterIntertwinerConstructed ≡ false
    tarotProjectionIsGroupTheoreticQuotient : Bool
    tarotProjectionIsGroupTheoreticQuotientIsFalse :
      tarotProjectionIsGroupTheoreticQuotient ≡ false
    distinguishedCentreIsModularVacuum : Bool
    distinguishedCentreIsModularVacuumIsFalse :
      distinguishedCentreIsModularVacuum ≡ false

canonicalSporadicSignedFiftyThreeBoundary :
  SporadicSignedFiftyThreeBoundary
canonicalSporadicSignedFiftyThreeBoundary =
  sporadicSignedFiftyThreeBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
