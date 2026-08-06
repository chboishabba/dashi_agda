module DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced

------------------------------------------------------------------------
-- Arithmetic candidate only:
--
--   53 = 1 + 26 * 2.
--
-- The construction below is a concrete 53-element candidate C2-set with one
-- fixed point and twenty-six binary fibres.  It is not identified with the
-- repository's actual ReducedMode53 carrier until an explicit equivalence and
-- intertwining law are supplied.  In particular, its twenty-six orbit labels
-- are not called sporadic groups by cardinality alone.
------------------------------------------------------------------------

data BinaryFibre : Set where
  positiveFibre : BinaryFibre
  negativeFibre : BinaryFibre

flipBinaryFibre : BinaryFibre → BinaryFibre
flipBinaryFibre positiveFibre = negativeFibre
flipBinaryFibre negativeFibre = positiveFibre

flipBinaryFibreInvolutive :
  (polarity : BinaryFibre) →
  flipBinaryFibre (flipBinaryFibre polarity) ≡ polarity
flipBinaryFibreInvolutive positiveFibre = refl
flipBinaryFibreInvolutive negativeFibre = refl

positiveAndNegativeDistinct :
  positiveFibre ≡ negativeFibre → ⊥
positiveAndNegativeDistinct ()

OrbitIndex26 : Set
OrbitIndex26 = Fin 26

CandidateR53 : Set
CandidateR53 = ⊤ ⊎ (OrbitIndex26 × BinaryFibre)

fixedPointCount : Nat
fixedPointCount = 1

orbitIndexCount : Nat
orbitIndexCount = 26

binaryFibreCount : Nat
binaryFibreCount = 2

candidateR53Dimension : Nat
candidateR53Dimension =
  fixedPointCount + orbitIndexCount * binaryFibreCount

candidateR53DimensionIsFiftyThree : candidateR53Dimension ≡ 53
candidateR53DimensionIsFiftyThree = refl

candidateDimensionMatchesReducedDimension :
  candidateR53Dimension ≡ Reduced.reducedDimension
candidateDimensionMatchesReducedDimension = refl

candidateInvolution : CandidateR53 → CandidateR53
candidateInvolution (inj₁ tt) = inj₁ tt
candidateInvolution (inj₂ (index , polarity)) =
  inj₂ (index , flipBinaryFibre polarity)

candidateInvolutionIsInvolutive :
  (state : CandidateR53) →
  candidateInvolution (candidateInvolution state) ≡ state
candidateInvolutionIsInvolutive (inj₁ tt) = refl
candidateInvolutionIsInvolutive (inj₂ (index , polarity))
  with flipBinaryFibreInvolutive polarity
... | refl = refl

candidateFixedPoint : CandidateR53
candidateFixedPoint = inj₁ tt

candidateFixedPointIsFixed :
  candidateInvolution candidateFixedPoint ≡ candidateFixedPoint
candidateFixedPointIsFixed = refl

positiveOrbitStateIsNotFixed :
  (index : OrbitIndex26) →
  candidateInvolution (inj₂ (index , positiveFibre))
  ≡ inj₂ (index , positiveFibre)
  → ⊥
positiveOrbitStateIsNotFixed index ()

negativeOrbitStateIsNotFixed :
  (index : OrbitIndex26) →
  candidateInvolution (inj₂ (index , negativeFibre))
  ≡ inj₂ (index , negativeFibre)
  → ⊥
negativeOrbitStateIsNotFixed index ()

orbitProjection : OrbitIndex26 × BinaryFibre → OrbitIndex26
orbitProjection (index , polarity) = index

positiveAndNegativeShareOrbitIndex :
  (index : OrbitIndex26) →
  orbitProjection (index , positiveFibre)
  ≡ orbitProjection (index , negativeFibre)
positiveAndNegativeShareOrbitIndex index = refl

------------------------------------------------------------------------
-- The same binary fibre may be observed in different vocabularies.  These are
-- typed observers with distinct codomains, not claims that parity, direction,
-- Tarot light/shadow and orientation are literally the same semantics.
------------------------------------------------------------------------

data SignObservation : Set where
  evenLikeObservation : SignObservation
  oddLikeObservation : SignObservation

data TransportObservation : Set where
  directTransportObservation : TransportObservation
  inverseTransportObservation : TransportObservation

data TarotPolarityObservation : Set where
  lightAspectObservation : TarotPolarityObservation
  shadowAspectObservation : TarotPolarityObservation

data OrientationObservation : Set where
  positiveOrientationObservation : OrientationObservation
  negativeOrientationObservation : OrientationObservation

observeSign : BinaryFibre → SignObservation
observeSign positiveFibre = evenLikeObservation
observeSign negativeFibre = oddLikeObservation

observeTransport : BinaryFibre → TransportObservation
observeTransport positiveFibre = directTransportObservation
observeTransport negativeFibre = inverseTransportObservation

observeTarotPolarity : BinaryFibre → TarotPolarityObservation
observeTarotPolarity positiveFibre = lightAspectObservation
observeTarotPolarity negativeFibre = shadowAspectObservation

observeOrientation : BinaryFibre → OrientationObservation
observeOrientation positiveFibre = positiveOrientationObservation
observeOrientation negativeFibre = negativeOrientationObservation

positiveObserverBundle :
  observeSign positiveFibre ≡ evenLikeObservation
  × observeTransport positiveFibre ≡ directTransportObservation
  × observeTarotPolarity positiveFibre ≡ lightAspectObservation
  × observeOrientation positiveFibre ≡ positiveOrientationObservation
positiveObserverBundle = refl , refl , refl , refl

negativeObserverBundle :
  observeSign negativeFibre ≡ oddLikeObservation
  × observeTransport negativeFibre ≡ inverseTransportObservation
  × observeTarotPolarity negativeFibre ≡ shadowAspectObservation
  × observeOrientation negativeFibre ≡ negativeOrientationObservation
negativeObserverBundle = refl , refl , refl , refl

------------------------------------------------------------------------
-- Promotion obligations.  The current repo proves the 53-dimensional reduced
-- carrier and the arithmetic candidate count.  It does not yet supply the
-- equivalence between them, a canonical quotient, sporadic labels, an S26
-- action, a sign character or a Monster intertwiner.
------------------------------------------------------------------------

record ReducedCandidateEquivalence : Set where
  constructor reducedCandidateEquivalence
  field
    encode : Reduced.ReducedMode53 → CandidateR53
    decode : CandidateR53 → Reduced.ReducedMode53
    decodeEncode :
      (mode : Reduced.ReducedMode53) → decode (encode mode) ≡ mode
    encodeDecode :
      (state : CandidateR53) → encode (decode state) ≡ state

record ReducedInvolutionWitness : Set where
  constructor reducedInvolutionWitness
  field
    equivalence : ReducedCandidateEquivalence
    reducedInvolution : Reduced.ReducedMode53 → Reduced.ReducedMode53
    intertwines :
      (mode : Reduced.ReducedMode53) →
      ReducedCandidateEquivalence.encode equivalence
        (reducedInvolution mode)
      ≡
      candidateInvolution
        (ReducedCandidateEquivalence.encode equivalence mode)

record OrbitLabellingWitness (Label : Set) : Set where
  constructor orbitLabellingWitness
  field
    labelOrbit : OrbitIndex26 → Label
    recoverOrbit : Label → OrbitIndex26
    recoverAfterLabel :
      (index : OrbitIndex26) → recoverOrbit (labelOrbit index) ≡ index
    labelAfterRecover :
      (label : Label) → labelOrbit (recoverOrbit label) ≡ label

record ReducedFiftyThreeOrbitBoundary : Set where
  constructor reducedFiftyThreeOrbitBoundary
  field
    arithmeticIdentityConstructsReducedEquivalence : Bool
    arithmeticIdentityConstructsReducedEquivalenceIsFalse :
      arithmeticIdentityConstructsReducedEquivalence ≡ false

    oneFixedPointCandidateLabelsSporadicGroups : Bool
    oneFixedPointCandidateLabelsSporadicGroupsIsFalse :
      oneFixedPointCandidateLabelsSporadicGroups ≡ false

    multipleC2ObserversHaveIdenticalSemantics : Bool
    multipleC2ObserversHaveIdenticalSemanticsIsFalse :
      multipleC2ObserversHaveIdenticalSemantics ≡ false

    symmetricGroupActionConstructed : Bool
    symmetricGroupActionConstructedIsFalse :
      symmetricGroupActionConstructed ≡ false

    signTwistedRepresentationConstructed : Bool
    signTwistedRepresentationConstructedIsFalse :
      signTwistedRepresentationConstructed ≡ false

    monsterIntertwinerConstructed : Bool
    monsterIntertwinerConstructedIsFalse :
      monsterIntertwinerConstructed ≡ false

open ReducedFiftyThreeOrbitBoundary public

canonicalReducedFiftyThreeOrbitBoundary : ReducedFiftyThreeOrbitBoundary
canonicalReducedFiftyThreeOrbitBoundary =
  reducedFiftyThreeOrbitBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
