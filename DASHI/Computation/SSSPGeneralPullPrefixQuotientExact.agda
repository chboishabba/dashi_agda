module DASHI.Computation.SSSPGeneralPullPrefixQuotientExact where

-- General theorem shape for Pull(M): the consumer-visible result is a prefix
-- observation, while permutations/refinements inside the unexposed tail are
-- residual information.  The theorem is parameterised by the actual prefix
-- and tail carriers so it can be instantiated by concrete BMSSP data without
-- pretending that this owner reimplements the paper's ordered-set data
-- structure.

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Bool using (Bool; false; true)

------------------------------------------------------------------------
-- 1. Prefix/tail factorisation.
------------------------------------------------------------------------

record PullPrefixFactorisation : Set₁ where
  constructor pullPrefixFactorisation
  field
    FullState Prefix TailCode : Set
    encodePrefix : FullState → Prefix
    encodeTail : FullState → TailCode
    rebuild : Prefix → TailCode → FullState

    rebuildEncode :
      (x : FullState) → rebuild (encodePrefix x) (encodeTail x) ≡ x

open PullPrefixFactorisation public

------------------------------------------------------------------------
-- 2. Tail symmetry invisible to Pull(M).
------------------------------------------------------------------------

record TailSymmetryQuotient (F : PullPrefixFactorisation) : Set₁ where
  constructor tailSymmetryQuotient
  field
    Symmetry : Set
    identity : Symmetry
    compose : Symmetry → Symmetry → Symmetry
    actTail : Symmetry → TailCode F → TailCode F

    identityActs :
      (t : TailCode F) → actTail identity t ≡ t

    actionComposes :
      (g h : Symmetry) (t : TailCode F) →
      actTail (compose g h) t ≡ actTail g (actTail h t)

open TailSymmetryQuotient public

actFull :
  {F : PullPrefixFactorisation} →
  TailSymmetryQuotient F →
  Symmetry →
  FullState F →
  FullState F
actFull {F} Q g x =
  rebuild F (encodePrefix F x) (actTail Q g (encodeTail F x))

-- Pull observes only the prefix.  Therefore every tail action is invisible by
-- construction, regardless of how many internal linear extensions the tail
-- contains.
pullObservation :
  (F : PullPrefixFactorisation) → FullState F → Prefix F
pullObservation F = encodePrefix F

record PullTailInvariance
  (F : PullPrefixFactorisation)
  (Q : TailSymmetryQuotient F) : Set₁ where
  constructor pullTailInvariance
  field
    prefixPreservedByTailAction :
      (g : Symmetry Q) (x : FullState F) →
      pullObservation F (actFull Q g x) ≡ pullObservation F x

open PullTailInvariance public

------------------------------------------------------------------------
-- 3. Generic consumer descent through the prefix quotient.
------------------------------------------------------------------------

record PrefixConsumer (F : PullPrefixFactorisation) : Set₁ where
  constructor prefixConsumer
  field
    Output : Set
    consumePrefix : Prefix F → Output

open PrefixConsumer public

consumeFull :
  {F : PullPrefixFactorisation} →
  PrefixConsumer F → FullState F → Output
consumeFull {F} C x = consumePrefix C (encodePrefix F x)

consumerIgnoresTailGivenSamePrefix :
  {F : PullPrefixFactorisation} →
  (C : PrefixConsumer F) →
  {x y : FullState F} →
  encodePrefix F x ≡ encodePrefix F y →
  consumeFull C x ≡ consumeFull C y
consumerIgnoresTailGivenSamePrefix C eq = cong (consumePrefix C) eq

------------------------------------------------------------------------
-- 4. BIDI boundary.
--
-- Forward: Pull(M) may discard tail orientation from its observation.
-- Reverse: the full state is reconstructible only when a tail code is retained.
-- Thus prefix projection is not declared lossless by itself.
------------------------------------------------------------------------

record GeneralPullBoundary : Set where
  constructor generalPullBoundary
  field
    prefixCanBeConsumerSufficient : Bool
    prefixCanBeConsumerSufficientIsTrue :
      prefixCanBeConsumerSufficient ≡ true
    tailMustBeRetainedForFullReconstruction : Bool
    tailMustBeRetainedForFullReconstructionIsTrue :
      tailMustBeRetainedForFullReconstruction ≡ true
    pullRequiresGlobalTailTotalisation : Bool
    pullRequiresGlobalTailTotalisationIsFalse :
      pullRequiresGlobalTailTotalisation ≡ false

canonicalGeneralPullBoundary : GeneralPullBoundary
canonicalGeneralPullBoundary =
  generalPullBoundary true refl true refl false refl
