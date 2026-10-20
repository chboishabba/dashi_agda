module DASHI.Physics.Plasma.Phase243ConsumerDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54

------------------------------------------------------------------------
-- CONSUMER DESCENT THROUGH CORE54
--
-- The finite quotient is only physically useful when the declared consumer is
-- constant on each Core54 fibre.  Rather than assume that constancy, derive it
-- from exact invariance under the already-paid phase advance + inversion action.
--
-- A canonical action word sends every Core243 state to the chosen representative
-- of its Core54 class.  Therefore any phase-invariant consumer equals its value
-- on the representative, hence is fibre-constant.  The repository's generic
-- sectioned-projection / consumer-descent theorem then constructs an explicit
-- factorization through Core54.
------------------------------------------------------------------------

data PhaseActionWord : Set where
  identityWord : PhaseActionWord
  advanceWord : PhaseActionWord
  advanceTwiceWord : PhaseActionWord
  inverseWord : PhaseActionWord
  advanceAfterInverseWord : PhaseActionWord
  advanceTwiceAfterInverseWord : PhaseActionWord

applyWord : PhaseActionWord → Rook.Core243 → Rook.Core243
applyWord identityWord x = x
applyWord advanceWord x = Rook.advanceCore x
applyWord advanceTwiceWord x = Rook.advanceCore (Rook.advanceCore x)
applyWord inverseWord x = Rook.inverseCore x
applyWord advanceAfterInverseWord x = Rook.advanceCore (Rook.inverseCore x)
applyWord advanceTwiceAfterInverseWord x =
  Rook.advanceCore (Rook.advanceCore (Rook.inverseCore x))

normalizationWord : C3.C3Phase → C3.C3Phase → PhaseActionWord
normalizationWord C3.phase0 C3.phase0 = identityWord
normalizationWord C3.phase0 C3.phase1 = identityWord
normalizationWord C3.phase0 C3.phase2 = inverseWord
normalizationWord C3.phase1 C3.phase0 = advanceAfterInverseWord
normalizationWord C3.phase1 C3.phase1 = advanceTwiceWord
normalizationWord C3.phase1 C3.phase2 = advanceTwiceWord
normalizationWord C3.phase2 C3.phase0 = advanceWord
normalizationWord C3.phase2 C3.phase1 = advanceTwiceAfterInverseWord
normalizationWord C3.phase2 C3.phase2 = advanceWord

normalizationHitsRepresentative : (x : Rook.Core243) →
  applyWord
    (normalizationWord (Rook.phaseLeft x) (Rook.phaseRight x))
    x
  ≡ Q54.representativeCore (Q54.quotientCore x)
normalizationHitsRepresentative (Rook.core243 k u v C3.phase0 C3.phase0) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase0 C3.phase1) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase0 C3.phase2) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase1 C3.phase0) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase1 C3.phase1) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase1 C3.phase2) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase2 C3.phase0) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase2 C3.phase1) = refl
normalizationHitsRepresentative (Rook.core243 k u v C3.phase2 C3.phase2) = refl

------------------------------------------------------------------------
-- Consumer invariance and normalization.
------------------------------------------------------------------------

record PhaseInvariantConsumer (Outcome : Set) : Set₁ where
  constructor phase-invariant-consumer
  field
    consumer : Rook.Core243 → Outcome
    advanceInvariant : (x : Rook.Core243) →
      consumer (Rook.advanceCore x) ≡ consumer x
    inverseInvariant : (x : Rook.Core243) →
      consumer (Rook.inverseCore x) ≡ consumer x
    invariantReference : String

open PhaseInvariantConsumer public

wordInvariant :
  ∀ {Outcome : Set} →
  (c : PhaseInvariantConsumer Outcome) →
  (word : PhaseActionWord) →
  (x : Rook.Core243) →
  consumer c (applyWord word x) ≡ consumer c x
wordInvariant c identityWord x = refl
wordInvariant c advanceWord x = advanceInvariant c x
wordInvariant c advanceTwiceWord x =
  trans
    (advanceInvariant c (Rook.advanceCore x))
    (advanceInvariant c x)
wordInvariant c inverseWord x = inverseInvariant c x
wordInvariant c advanceAfterInverseWord x =
  trans
    (advanceInvariant c (Rook.inverseCore x))
    (inverseInvariant c x)
wordInvariant c advanceTwiceAfterInverseWord x =
  trans
    (advanceInvariant c (Rook.advanceCore (Rook.inverseCore x)))
    (trans
      (advanceInvariant c (Rook.inverseCore x))
      (inverseInvariant c x))

consumerEqualsRepresentative :
  ∀ {Outcome : Set} →
  (c : PhaseInvariantConsumer Outcome) →
  (x : Rook.Core243) →
  consumer c x
  ≡ consumer c (Q54.representativeCore (Q54.quotientCore x))
consumerEqualsRepresentative c x =
  trans
    (sym
      (wordInvariant c
        (normalizationWord (Rook.phaseLeft x) (Rook.phaseRight x))
        x))
    (cong (consumer c) (normalizationHitsRepresentative x))

phaseInvariantConsumerFibreConstant :
  ∀ {Outcome : Set} →
  (c : PhaseInvariantConsumer Outcome) →
  Descent.FibreConstantFor Q54.quotientCore (consumer c)
phaseInvariantConsumerFibreConstant c left right sameQuotient =
  trans
    (consumerEqualsRepresentative c left)
    (trans
      (cong
        (λ q → consumer c (Q54.representativeCore q))
        sameQuotient)
      (sym (consumerEqualsRepresentative c right)))

------------------------------------------------------------------------
-- Core54 is a sectioned projection, so fibre constancy constructs descent.
------------------------------------------------------------------------

core54SectionedProjection :
  Sectioned.SectionedProjection Rook.Core243 Q54.Core54
core54SectionedProjection =
  Sectioned.sectionedProjection
    Q54.quotientCore
    Q54.representativeCore
    Q54.quotientRepresentativeRoundTrip

phaseInvariantConsumerIsCore54Sufficient :
  ∀ {Outcome : Set} →
  (c : PhaseInvariantConsumer Outcome) →
  Descent.ConsumerSufficient Q54.quotientCore (consumer c)
phaseInvariantConsumerIsCore54Sufficient c =
  Descent.fibreConstantIsConsumerSufficient
    (phaseInvariantConsumerFibreConstant c)

phaseInvariantConsumerFactorsThroughCore54 :
  ∀ {Outcome : Set} →
  (c : PhaseInvariantConsumer Outcome) →
  Descent.FactorsThrough Q54.quotientCore (consumer c)
phaseInvariantConsumerFactorsThroughCore54 c =
  Descent.sectionedFibreConstantFactors
    core54SectionedProjection
    (consumer c)
    (phaseInvariantConsumerFibreConstant c)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Phase243ConsumerDescentBoundary : Set where
  constructor phase243-consumer-descent-boundary
  field
    phaseInvariantConsumerDescendsToCore54 : Bool
    phaseInvariantConsumerDescendsToCore54IsTrue :
      phaseInvariantConsumerDescendsToCore54 ≡ true
    arbitraryConsumerDescendsToCore54 : Bool
    arbitraryConsumerDescendsToCore54IsFalse :
      arbitraryConsumerDescendsToCore54 ≡ false
    representativeSectionRecoversFinePhaseState : Bool
    representativeSectionRecoversFinePhaseStateIsFalse :
      representativeSectionRecoversFinePhaseState ≡ false
    quotientDescentUsesCanonicalCoreConsumerTheory : Bool
    quotientDescentUsesCanonicalCoreConsumerTheoryIsTrue :
      quotientDescentUsesCanonicalCoreConsumerTheory ≡ true

canonicalPhase243ConsumerDescentBoundary : Phase243ConsumerDescentBoundary
canonicalPhase243ConsumerDescentBoundary =
  phase243-consumer-descent-boundary
    true refl
    false refl
    false refl
    true refl
