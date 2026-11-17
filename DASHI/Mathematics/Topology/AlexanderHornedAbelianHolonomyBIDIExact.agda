module DASHI.Mathematics.Topology.AlexanderHornedAbelianHolonomyBIDIExact where

------------------------------------------------------------------------
-- ALEXANDER HORNED EXTERIOR x KK FLAT U(1) HOLONOMY x BIDI
--
-- The source group is the existing conditional meridian group.
-- The geometric pi_1 identification and essential-meridian supplier
-- remain separate from this algebraic theorem.
--
-- Result: EVERY homomorphism to ANY abelian group annihilates every
-- meridian with the recursive commutator relation. When these
-- meridians generate the group, the homomorphism is identically zero.
-- Given an essential meridian, it yields an explicit non-descent
-- witness: an abelian character does not recover a loop class.
--
-- This applies to FLAT U(1) holonomy representations of pi_1.
-- NONFLAT connection Wilson loops are NOT pi_1 characters.
-- Nonabelian holonomy, curvature, bundles, and physically realized
-- C3 actions remain separate consumers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Finite
import DASHI.Mathematics.Topology.AlexanderHornedC3ExteriorBridge as Bridge
import DASHI.Mathematics.Topology.AlexanderHornedC3CharactersExact as Characters
import DASHI.Mathematics.Topology.AlexanderHornedC3OuterDetectorExact as Outer
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record AbelianHolonomyTarget : Set₁ where
  field
    Value : Set
    neutral : Value
    product : Value → Value → Value
    inverse : Value → Value

    associative : ∀ a b c →
      product (product a b) c ≡ product a (product b c)
    commute : ∀ a b → product a b ≡ product b a
    leftUnit : ∀ a → product neutral a ≡ a
    rightInverse : ∀ a → product a (inverse a) ≡ neutral

open AbelianHolonomyTarget public

inverseNeutral :
  (A : AbelianHolonomyTarget) →
  inverse A (neutral A) ≡ neutral A
inverseNeutral A =
  trans
    (sym (leftUnit A (inverse A (neutral A))))
    (rightInverse A (neutral A))

abelianCommutatorIsNeutral :
  (A : AbelianHolonomyTarget) → ∀ a b →
  product A
    (product A
      (product A a b)
      (inverse A a))
    (inverse A b)
    ≡ neutral A
abelianCommutatorIsNeutral A a b =
  trans
    (cong (λ x → product A x (inverse A b))
      (associative A a b (inverse A a)))
    (trans
      (cong (λ x → product A x (inverse A b))
        (cong (product A a)
          (commute A b (inverse A a))))
      (trans
        (cong (λ x → product A x (inverse A b))
          (sym (associative A a (inverse A a) b)))
        (trans
          (cong (λ x → product A x (inverse A b))
            (cong (λ x → product A x b)
              (rightInverse A a)))
          (trans
            (cong (λ x → product A x (inverse A b))
              (leftUnit A b))
            (rightInverse A b)))))

record AbelianCharacter
    (G : Bridge.EquivariantMeridianGroup)
    (A : AbelianHolonomyTarget) : Set where
  field
    image : Bridge.LoopClass G → Value A
    sendsUnit : image (Bridge.identity G) ≡ neutral A
    sendsProduct : ∀ a b →
      image (Bridge.multiply G a b) ≡
        product A (image a) (image b)
    sendsInverse : ∀ a →
      image (Bridge.invert G a) ≡ inverse A (image a)

open AbelianCharacter public

characterKillsCommutator :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (chi : AbelianCharacter G A) →
  ∀ a b →
  image chi
    (Bridge.multiply G
      (Bridge.multiply G
        (Bridge.multiply G a b)
        (Bridge.invert G a))
      (Bridge.invert G b))
    ≡ neutral A
characterKillsCommutator G A chi a b =
  trans
    (sendsProduct chi
      (Bridge.multiply G
        (Bridge.multiply G a b)
        (Bridge.invert G a))
      (Bridge.invert G b))
    (trans
      (cong₂ (product A)
        (trans
          (sendsProduct chi
            (Bridge.multiply G a b)
            (Bridge.invert G a))
          (cong₂ (product A)
            (sendsProduct chi a b)
            (sendsInverse chi a)))
        (sendsInverse chi b))
      (abelianCommutatorIsNeutral A (image chi a) (image chi b)))

allHornMeridiansAbelianInvisible :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (chi : AbelianCharacter G A) →
  ∀ address →
  image chi (Bridge.meridian G address) ≡ neutral A
allHornMeridiansAbelianInvisible G A chi address =
  trans
    (cong (image chi)
      (Bridge.meridianRefinesAsCommutator G address))
    (characterKillsCommutator G A chi
      (Bridge.meridian G (Finite.leftChild address))
      (Bridge.meridian G (Finite.rightChild address)))

allFormalMeridianWordsAbelianInvisible :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (chi : AbelianCharacter G A) →
  ∀ word →
  image chi (Bridge.interpretWord G word) ≡ neutral A
allFormalMeridianWordsAbelianInvisible G A chi Finite.unit =
  sendsUnit chi
allFormalMeridianWordsAbelianInvisible G A chi (Finite.generator a) =
  allHornMeridiansAbelianInvisible G A chi a
allFormalMeridianWordsAbelianInvisible G A chi (Finite.inverseWord w) =
  trans
    (sendsInverse chi (Bridge.interpretWord G w))
    (trans
      (cong (inverse A)
        (allFormalMeridianWordsAbelianInvisible G A chi w))
      (inverseNeutral A))
allFormalMeridianWordsAbelianInvisible G A chi (Finite.combine w v) =
  trans
    (sendsProduct chi
      (Bridge.interpretWord G w)
      (Bridge.interpretWord G v))
    (trans
      (cong₂ (product A)
        (allFormalMeridianWordsAbelianInvisible G A chi w)
        (allFormalMeridianWordsAbelianInvisible G A chi v))
      (leftUnit A (neutral A)))

allAbelianCharactersTrivialIfGenerated :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  Characters.MeridianGeneration G →
  (chi : AbelianCharacter G A) →
  ∀ x → image chi x ≡ neutral A
allAbelianCharactersTrivialIfGenerated G A gen chi x =
  trans
    (sym (cong (image chi)
      (Characters.representationExact gen x)))
    (allFormalMeridianWordsAbelianInvisible G A chi
      (Characters.representingWord gen x))

-- Even if the C3 action is nontrivial on loop classes, its image
-- under ANY abelian character cannot distinguish rotated loops.
allAbelianCharactersBlindToC3Rotation :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  Characters.MeridianGeneration G →
  (chi : AbelianCharacter G A) →
  ∀ x →
  image chi (Bridge.rotateLoop G x) ≡ image chi x
allAbelianCharactersBlindToC3Rotation G A gen chi x =
  trans
    (allAbelianCharactersTrivialIfGenerated G A gen chi
      (Bridge.rotateLoop G x))
    (sym (allAbelianCharactersTrivialIfGenerated G A gen chi x))

-- A nontrivial meridian and the group unit collide under the
-- abelian observer, but differ under the identity/loop consumer.
essentialMeridianIsAbelianNonDescent :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (chi : AbelianCharacter G A) →
  (essential : Bridge.EssentialMeridian G) →
  Transport.ClaimNonTransportWitness
    (image chi)
    (λ x → x)
essentialMeridianIsAbelianNonDescent G A chi essential =
  Descent.consumerNonDescentWitness
    (Bridge.meridian G (Bridge.EssentialMeridian.address essential))
    (Bridge.identity G)
    (trans
      (allHornMeridiansAbelianInvisible G A chi
        (Bridge.EssentialMeridian.address essential))
      (sym (sendsUnit chi)))
    (Bridge.EssentialMeridian.notIdentity essential)

noBIDIRecoveryOfFullLoopsFromAbelianHolonomy :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (chi : AbelianCharacter G A) →
  Bridge.EssentialMeridian G →
  Transport.ClaimTransport (image chi) (λ x → x) → ⊥
noBIDIRecoveryOfFullLoopsFromAbelianHolonomy G A chi essential =
  Transport.claimNonTransportWitnessBlocksTransport
    (essentialMeridianIsAbelianNonDescent G A chi essential)


------------------------------------------------------------------------
-- SAME-OBJECT DUAL CONSUMER / STEELMAN: ABELIAN BLINDNESS VS
-- NONABELIAN OUTER-ACTION DETECTION.
--
-- Both halves concern the SAME G and the SAME C3 rotateLoop operation.
-- The nonabelian detector quotient is supplied as a premise; the
-- abstract theorem does not construct the geometric embedding or A5^3.
------------------------------------------------------------------------

pairedFlatHolonomyBlindAndOuterActionDetectable :
  (G : Bridge.EquivariantMeridianGroup) →
  (A : AbelianHolonomyTarget) →
  (generation : Characters.MeridianGeneration G) →
  (chi : AbelianCharacter G A) →
  (Q : Outer.EquivariantQuotientDetector G) →
  ((∀ x →
      image chi (Bridge.rotateLoop G x) ≡ image chi x)
    ×
    (∀ g →
      (∀ x →
        Bridge.rotateLoop G x ≡ Outer.sourceInner G g x)
      → ⊥))
pairedFlatHolonomyBlindAndOuterActionDetectable G A gen chi Q =
  allAbelianCharactersBlindToC3Rotation G A gen chi
  ,
  Outer.rotationCannotBeInnerIfDetectorExists G Q
