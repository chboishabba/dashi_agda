module DASHI.Cognition.PNF.X369ConsumerSufficientCompressionNoGoExact where

------------------------------------------------------------------------
-- P0: FULL-CHANNEL GAUGE IS NOT A COMPRESSION NO-GO
--
-- Reuses the existing deterministic consumer-sufficiency order from
-- DASHI.Core.ConsumerDescentMinimalObserverExact.
--
-- All theorems in this file are finite/structural. They do not assert
-- a learned neural C3 action, entropy bound, model quality gain, or
-- executable codec performance. No quantizer/semantic identification
-- is inferred from a coordinate number.
--
-- The exact 3-channel integer polynomial lives in the existing
-- X369OriginalDirectedTriadC3PolynomialCandidate owner. Do not duplicate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact as Grok
import DASHI.Cognition.PNF.GrokkingEquivarianceDefectGeometryExact as Task
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

sym : ∀ {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl equal = equal

cong : ∀ {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- P0a: explicit inverse coordinate transport on an entire 3-channel
-- state. In particular every full-channel linear readout has a
-- transported head: the head class does not get larger just by a
-- fixed cyclic permutation. This theorem works for ALL heads, not
-- only linear ones. It says nothing about constrained/quantized heads.
------------------------------------------------------------------------

record Triple (A : Set) : Set where
  constructor triple
  field
    first second third : A
open Triple public

rotate : ∀ {A : Set} → Triple A → Triple A
rotate (triple a b c) = triple b c a

unrotate : ∀ {A : Set} → Triple A → Triple A
unrotate (triple a b c) = triple c a b

rotateUnrotate : ∀ {A : Set} (t : Triple A) →
  rotate (unrotate t) ≡ t
rotateUnrotate (triple a b c) = refl

unrotateRotate : ∀ {A : Set} (t : Triple A) →
  unrotate (rotate t) ≡ t
unrotateRotate (triple a b c) = refl

rotateCubed : ∀ {A : Set} (t : Triple A) →
  rotate (rotate (rotate t)) ≡ t
rotateCubed (triple a b c) = refl

transportHeadToRotated :
  ∀ {A B : Set} → (Triple A → B) → Triple A → B
transportHeadToRotated head t = head (unrotate t)

transportHeadFromRotated :
  ∀ {A B : Set} → (Triple A → B) → Triple A → B
transportHeadFromRotated head t = head (rotate t)

rotatedFullHeadSameConsumer :
  ∀ {A B : Set} (head : Triple A → B) (t : Triple A) →
  transportHeadToRotated head (rotate t) ≡ head t
rotatedFullHeadSameConsumer head t rewrite unrotateRotate t = refl

reverseRotatedFullHeadSameConsumer :
  ∀ {A B : Set} (head : Triple A → B) (t : Triple A) →
  transportHeadFromRotated head (unrotate t) ≡ head t
reverseRotatedFullHeadSameConsumer head t rewrite rotateUnrotate t = refl

transportHeadRoundTrip :
  ∀ {A B : Set} (head : Triple A → B) (t : Triple A) →
  transportHeadFromRotated (transportHeadToRotated head) t ≡ head t
transportHeadRoundTrip head t rewrite unrotateRotate t = refl

transportHeadInverseRoundTrip :
  ∀ {A B : Set} (head : Triple A → B) (t : Triple A) →
  transportHeadToRotated (transportHeadFromRotated head) t ≡ head t
transportHeadInverseRoundTrip head t rewrite rotateUnrotate t = refl

------------------------------------------------------------------------
-- P0b: exact but NON-INJECTIVE codec preserving a typed C3 consumer.
-- An irrelevant Bool tag can be discarded while the three-valued
-- phase and its action remain fully available.
-- This is a concrete counterexample to the false claim that
-- consumer sufficiency requires lossless raw-state reconstruction.
------------------------------------------------------------------------

Phase : Set
Phase = Wheel.DepthWheelPhase

record TaggedPhase : Set where
  constructor tagged
  field
    consumerPhase : Phase
    irrelevantTag : Bool
open TaggedPhase public

phaseCodec : TaggedPhase → Phase
phaseCodec = consumerPhase

phaseConsumer : TaggedPhase → Phase
phaseConsumer = consumerPhase

codecSufficientForPhase :
  Descent.ConsumerSufficient phaseCodec phaseConsumer
codecSufficientForPhase left right sameCode = sameCode

sameCompressedDifferentRaw :
  phaseCodec (tagged Wheel.phase-0 true)
  ≡ phaseCodec (tagged Wheel.phase-0 false)
sameCompressedDifferentRaw = refl

rawWitnessesNotEqual :
  tagged Wheel.phase-0 true ≡ tagged Wheel.phase-0 false → ⊥
rawWitnessesNotEqual ()

advanceTag : TaggedPhase → TaggedPhase
advanceTag (tagged p b) = tagged (Task.advancePhase p) b

phaseCodecIntertwinesC3 :
  (x : TaggedPhase) →
  phaseCodec (advanceTag x) ≡ Task.advancePhase (phaseCodec x)
phaseCodecIntertwinesC3 (tagged p b) = refl

phaseConsumerIntertwinesC3 :
  (x : TaggedPhase) →
  phaseConsumer (advanceTag x) ≡ Task.advancePhase (phaseConsumer x)
phaseConsumerIntertwinesC3 (tagged p b) = refl

------------------------------------------------------------------------
-- P0c: invariant-only quantization cannot support a changing
-- fixed-point-free C3 output, if the decoder sees ONLY that code.
-- This is a CONSUMER-RELATIVE no-go, not a no-compression theorem.
------------------------------------------------------------------------

phaseAdvanceHasNoFixedPoint :
  (p : Phase) → Task.advancePhase p ≡ p → ⊥
phaseAdvanceHasNoFixedPoint Wheel.phase-0 ()
phaseAdvanceHasNoFixedPoint Wheel.phase-1 ()
phaseAdvanceHasNoFixedPoint Wheel.phase-2 ()

invariantCodecNotSufficientForChangingConsumer :
  ∀ {X Code : Set} →
  (action : X → X) (encode : X → Code) (consumer : X → Phase) →
  (x : X) →
  ((z : X) → encode (action z) ≡ encode z) →
  ((z : X) → consumer (action z) ≡
    Task.advancePhase (consumer z)) →
  Descent.ConsumerSufficient encode consumer → ⊥
invariantCodecNotSufficientForChangingConsumer
  action encode consumer x invariant lawful sufficient =
  phaseAdvanceHasNoFixedPoint (consumer x)
    (trans
      (sym (lawful x))
      (sufficient (action x) x (invariant x)))

-- In particular, the EXISTING 9-point modular-grokking task
-- has a moving phase label under the existing shiftLeft action.
-- The head may compress other information, but cannot erase
-- the label action itself and still be sufficient.
modularGrokkingInvariantCodeNoGo :
  ∀ {Code : Set} →
  (encode : Grok.InputPair → Code) →
  ((z : Grok.InputPair) →
    encode (Task.shiftLeft z) ≡ encode z) →
  Descent.ConsumerSufficient encode Grok.algorithmicRule → ⊥
modularGrokkingInvariantCodeNoGo encode invariant sufficient =
  invariantCodecNotSufficientForChangingConsumer
    Task.shiftLeft encode Grok.algorithmicRule Grok.p00
    invariant
    (λ z → algorithmicActionCorrect z)
    sufficient
  where
    algorithmicActionCorrect :
      (z : Grok.InputPair) →
      Grok.algorithmicRule (Task.shiftLeft z)
      ≡ Task.advancePhase (Grok.algorithmicRule z)
    algorithmicActionCorrect Grok.p00 = refl
    algorithmicActionCorrect Grok.p01 = refl
    algorithmicActionCorrect Grok.p02 = refl
    algorithmicActionCorrect Grok.p10 = refl
    algorithmicActionCorrect Grok.p11 = refl
    algorithmicActionCorrect Grok.p12 = refl
    algorithmicActionCorrect Grok.p20 = refl
    algorithmicActionCorrect Grok.p21 = refl
    algorithmicActionCorrect Grok.p22 = refl

------------------------------------------------------------------------
-- P0d: any codec with a FULL state decoder roundtrip is sufficient
-- for every consumer, but full recovery is stronger than necessary.
-- The noninjective TaggedPhase witness above witnesses the strict
-- distinction for a particular consumer.
------------------------------------------------------------------------

fullReconstructionImpliesConsumerSufficiency :
  ∀ {X Code Outcome : Set}
  (encode : X → Code) (decode : Code → X)
  (roundTrip : (x : X) → decode (encode x) ≡ x)
  (consumer : X → Outcome) →
  Descent.ConsumerSufficient encode consumer
fullReconstructionImpliesConsumerSufficiency
  encode decode roundTrip consumer x y sameCode =
  trans
    (sym (cong consumer (roundTrip x)))
    (trans
      (cong (λ code → consumer (decode code)) sameCode)
      (cong consumer (roundTrip y)))

-- An exact consumer-equivariant quotient can be non-injective.
-- Its cardinality or bit cost is a SEPARATE theorem: neither a
-- head gauge nor a consumer factorization establishes a byte,
-- Shannon, runtime, or finite-precision compression ratio.


------------------------------------------------------------------------
-- P0e: exact FUTURE-consumer sufficiency. This is the structural
-- condition a memory/codec must preserve, beyond a one-step readout.
-- transitionStability is an explicit hypothesis, not inferred from
-- one-step consumer fibre-constancy.
------------------------------------------------------------------------

iterate : ∀ {X : Set} → Nat → (X → X) → X → X
iterate zero step x = x
iterate (suc n) step x = iterate n step (step x)

iteratePreservesCodeEquality :
  ∀ {X Code : Set}
  (step : X → X) (encode : X → Code) →
  ((x y : X) → encode x ≡ encode y →
    encode (step x) ≡ encode (step y)) →
  (n : Nat) (x y : X) →
  encode x ≡ encode y →
  encode (iterate n step x) ≡ encode (iterate n step y)
iteratePreservesCodeEquality step encode stable zero x y equality = equality
iteratePreservesCodeEquality step encode stable (suc n) x y equality =
  iteratePreservesCodeEquality step encode stable n
    (step x) (step y) (stable x y equality)

futureConsumerSufficiency :
  ∀ {X Code Outcome : Set}
  (step : X → X) (encode : X → Code)
  (consumer : X → Outcome) →
  Descent.ConsumerSufficient encode consumer →
  ((x y : X) → encode x ≡ encode y →
    encode (step x) ≡ encode (step y)) →
  (n : Nat) →
  Descent.ConsumerSufficient encode (λ x → consumer (iterate n step x))
futureConsumerSufficiency step encode consumer sufficient stable n
  x y sameCode =
  sufficient
    (iterate n step x)
    (iterate n step y)
    (iteratePreservesCodeEquality step encode stable n x y sameCode)

-- The converse claim is deliberately not made: a compression that
-- preserves one observed target but NOT its transition-stable fibres
-- can still lose information needed by a later target.


------------------------------------------------------------------------
-- P0f: the SAME smaller quotient is exact for a present consumer
-- but UNSOUND for a future consumer if the discarded tag can alter
-- the transition. This is the formal future-memory/steering issue:
-- current-surface fidelity != future-sufficient compression.
------------------------------------------------------------------------

tagSensitiveStep : TaggedPhase → TaggedPhase
tagSensitiveStep (tagged p true) =
  tagged (Task.advancePhase p) true
tagSensitiveStep (tagged p false) = tagged p false

sameCodeBeforeTagSensitiveStep :
  phaseCodec (tagged Wheel.phase-0 true)
  ≡ phaseCodec (tagged Wheel.phase-0 false)
sameCodeBeforeTagSensitiveStep = refl

tagSensitiveStepBreaksPhaseFibre :
  phaseCodec (tagSensitiveStep (tagged Wheel.phase-0 true))
  ≡ phaseCodec (tagSensitiveStep (tagged Wheel.phase-0 false)) →
  ⊥
tagSensitiveStepBreaksPhaseFibre sameAfter =
  phaseAdvanceHasNoFixedPoint Wheel.phase-0 sameAfter

presentConsumerSufficientFutureConsumerNot :
  Descent.ConsumerSufficient
    phaseCodec
    (λ state → phaseConsumer (tagSensitiveStep state)) →
  ⊥
presentConsumerSufficientFutureConsumerNot sufficient =
  tagSensitiveStepBreaksPhaseFibre
    (sufficient
      (tagged Wheel.phase-0 true)
      (tagged Wheel.phase-0 false)
      sameCodeBeforeTagSensitiveStep)

-- A local residual carrying the discarded tag would remove this
-- particular failure, but its cost and minimality are independent
-- MDL/resource questions delegated to the existing compression ladder.


------------------------------------------------------------------------
-- P0g: positive encoder-transition BIDI criterion.
-- A compressed dynamical state is sound when the ORIGINAL transition
-- descends to a transition on the code. This supplies exactly the
-- fibre-stability hypothesis needed by futureConsumerSufficiency.
------------------------------------------------------------------------

encodedTransitionWeldImpliesFibreStability :
  ∀ {X Code : Set}
  (step : X → X) (encode : X → Code)
  (stepCode : Code → Code) →
  ((x : X) → encode (step x) ≡ stepCode (encode x)) →
  (x y : X) → encode x ≡ encode y →
  encode (step x) ≡ encode (step y)
encodedTransitionWeldImpliesFibreStability step encode stepCode weld
  x y same =
  trans
    (weld x)
    (trans (cong stepCode same) (sym (weld y)))

compressedTransitionPreservesEveryFutureConsumer :
  ∀ {X Code Outcome : Set}
  (step : X → X) (encode : X → Code)
  (stepCode : Code → Code) (consumer : X → Outcome) →
  Descent.ConsumerSufficient encode consumer →
  ((x : X) → encode (step x) ≡ stepCode (encode x)) →
  (n : Nat) →
  Descent.ConsumerSufficient encode (λ x → consumer (iterate n step x))
compressedTransitionPreservesEveryFutureConsumer
  step encode stepCode consumer sufficient weld n =
  futureConsumerSufficiency
    step encode consumer sufficient
    (encodedTransitionWeldImpliesFibreStability
       step encode stepCode weld)
    n

-- Converse caution: equal current consumer observations do not
-- construct stepCode. The tagSensitiveStep witness above exhibits
-- the obstruction: two equal codes have different next codes.


------------------------------------------------------------------------
-- P0h: CONCRETE exact fixed-width quantization bound.
-- For the selected phase consumer (3 distinct values):
--   1 Bool bit cannot encode all consumer outcomes;
--   2 Bool bits can, although the independent fine tag is lost.
-- This is fixed-width / zero-error phase coding, not an estimate of
-- neural weight precision, Shannon entropy, hardware or byte savings.
------------------------------------------------------------------------

tag0 tag1 tag2 : TaggedPhase
tag0 = tagged Wheel.phase-0 false
tag1 = tagged Wheel.phase-1 false
tag2 = tagged Wheel.phase-2 false

phase01Distinct : Wheel.phase-0 ≡ Wheel.phase-1 → ⊥
phase01Distinct ()

phase02Distinct : Wheel.phase-0 ≡ Wheel.phase-2 → ⊥
phase02Distinct ()

phase12Distinct : Wheel.phase-1 ≡ Wheel.phase-2 → ⊥
phase12Distinct ()

oneBitCannotPreserveThreePhaseConsumer :
  (encode : TaggedPhase → Bool) →
  Descent.ConsumerSufficient encode phaseConsumer → ⊥
oneBitCannotPreserveThreePhaseConsumer encode sufficient
  with encode tag0 | encode tag1 | encode tag2
... | false | false | false =
  phase01Distinct (sufficient tag0 tag1 refl)
... | false | false | true =
  phase01Distinct (sufficient tag0 tag1 refl)
... | false | true | false =
  phase02Distinct (sufficient tag0 tag2 refl)
... | false | true | true =
  phase12Distinct (sufficient tag1 tag2 refl)
... | true | false | false =
  phase12Distinct (sufficient tag1 tag2 refl)
... | true | false | true =
  phase02Distinct (sufficient tag0 tag2 refl)
... | true | true | false =
  phase01Distinct (sufficient tag0 tag1 refl)
... | true | true | true =
  phase01Distinct (sufficient tag0 tag1 refl)

TwoBits : Set
TwoBits = Bool × Bool

phaseToTwoBits : Phase → TwoBits
phaseToTwoBits Wheel.phase-0 = false , false
phaseToTwoBits Wheel.phase-1 = false , true
phaseToTwoBits Wheel.phase-2 = true , false

twoBitsToPhase : TwoBits → Phase
twoBitsToPhase (false , false) = Wheel.phase-0
twoBitsToPhase (false , true) = Wheel.phase-1
twoBitsToPhase (true , false) = Wheel.phase-2
twoBitsToPhase (true , true) = Wheel.phase-0

phaseTwoBitRoundTrip : (p : Phase) →
  twoBitsToPhase (phaseToTwoBits p) ≡ p
phaseTwoBitRoundTrip Wheel.phase-0 = refl
phaseTwoBitRoundTrip Wheel.phase-1 = refl
phaseTwoBitRoundTrip Wheel.phase-2 = refl

taggedTwoBitEncode : TaggedPhase → TwoBits
taggedTwoBitEncode x = phaseToTwoBits (consumerPhase x)

taggedTwoBitPreservesConsumer :
  (x : TaggedPhase) →
  twoBitsToPhase (taggedTwoBitEncode x) ≡ phaseConsumer x
taggedTwoBitPreservesConsumer (tagged Wheel.phase-0 b) = refl
taggedTwoBitPreservesConsumer (tagged Wheel.phase-1 b) = refl
taggedTwoBitPreservesConsumer (tagged Wheel.phase-2 b) = refl

twoBitsSufficientForPhase :
  Descent.ConsumerSufficient taggedTwoBitEncode phaseConsumer
twoBitsSufficientForPhase x y sameCode =
  trans
    (sym (taggedTwoBitPreservesConsumer x))
    (trans
      (cong twoBitsToPhase sameCode)
      (taggedTwoBitPreservesConsumer y))

twoBitsDiscardTheIrrelevantTag :
  taggedTwoBitEncode (tagged Wheel.phase-1 true)
  ≡ taggedTwoBitEncode (tagged Wheel.phase-1 false)
twoBitsDiscardTheIrrelevantTag = refl

-- The 1-bit impossibility and 2-bit construction establish a
-- minimum fixed width for THIS exact three-outcome consumer.
-- Cost optimality for actual source model execution still needs
-- the existing admissible-consumer MDL / Pareto resource owner.
