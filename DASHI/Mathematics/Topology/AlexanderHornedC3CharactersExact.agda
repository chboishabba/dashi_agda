module DASHI.Mathematics.Topology.AlexanderHornedC3CharactersExact where

------------------------------------------------------------------------
-- C3-CHARGE VANISHING IN HORNED-MERIDIAN GROUP MODELS.
--
-- Theorem: if a group has generators with Hatcher's recursive
-- commutator relations, then every homomorphism to C3 kills each
-- meridian; if the meridians generate, every such homomorphism is
-- trivial.  The geometric assertion that a specific exterior has
-- precisely this presentation remains an independent input.
--
-- Primary source: Hatcher, Algebraic Topology, Example 2B.2.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Finite
import DASHI.Mathematics.Topology.AlexanderHornedC3ExteriorBridge as Bridge

record C3Character (G : Bridge.EquivariantMeridianGroup) : Set where
  field
    character : Bridge.LoopClass G → C3.C3
    preservesUnit :
      character (Bridge.identity G) ≡ C3.c0
    preservesMultiply : ∀ a b →
      character (Bridge.multiply G a b)
        ≡ C3._∙_ (character a) (character b)
    preservesInverse : ∀ a →
      character (Bridge.invert G a)
        ≡ C3.inverse (character a)

open C3Character public

characterPreservesCommutator :
  (G : Bridge.EquivariantMeridianGroup) →
  (chi : C3Character G) → ∀ a b →
  character chi
    (Bridge.multiply G
      (Bridge.multiply G
        (Bridge.multiply G a b)
        (Bridge.invert G a))
      (Bridge.invert G b))
  ≡ Finite.commutatorC3 (character chi a) (character chi b)
characterPreservesCommutator G chi a b =
  trans
    (preservesMultiply chi
      (Bridge.multiply G
        (Bridge.multiply G a b)
        (Bridge.invert G a))
      (Bridge.invert G b))
    (cong₂ C3._∙_
      (trans
        (preservesMultiply chi
          (Bridge.multiply G a b)
          (Bridge.invert G a))
        (cong₂ C3._∙_
          (preservesMultiply chi a b)
          (preservesInverse chi a)))
      (preservesInverse chi b))

characterOnHornAddresses :
  (G : Bridge.EquivariantMeridianGroup) →
  C3Character G → Finite.CompatibleC3Character
characterOnHornAddresses G chi =
  Finite.compatibleC3Character
    (λ a → character chi (Bridge.meridian G a))
    (λ a →
      trans
        (cong (character chi)
          (Bridge.meridianRefinesAsCommutator G a))
        (characterPreservesCommutator G chi
          (Bridge.meridian G (Finite.leftChild a))
          (Bridge.meridian G (Finite.rightChild a))))

everyMeridianHasZeroC3Charge :
  (G : Bridge.EquivariantMeridianGroup) →
  (chi : C3Character G) → ∀ a →
  character chi (Bridge.meridian G a) ≡ C3.c0
everyMeridianHasZeroC3Charge G chi a =
  Finite.everyCompatibleC3CharacterVanishes
    (characterOnHornAddresses G chi) a

record MeridianGeneration (G : Bridge.EquivariantMeridianGroup) : Set where
  field
    representingWord : Bridge.LoopClass G → Finite.Word
    representationExact : ∀ x →
      Bridge.interpretWord G (representingWord x) ≡ x

open MeridianGeneration public

characterVanishesOnAllFormalWords :
  (G : Bridge.EquivariantMeridianGroup) →
  (chi : C3Character G) → ∀ w →
    character chi (Bridge.interpretWord G w) ≡ C3.c0
characterVanishesOnAllFormalWords G chi Finite.unit =
  preservesUnit chi
characterVanishesOnAllFormalWords G chi (Finite.generator a) =
  everyMeridianHasZeroC3Charge G chi a
characterVanishesOnAllFormalWords G chi (Finite.inverseWord w) =
  trans
    (preservesInverse chi (Bridge.interpretWord G w))
    (cong C3.inverse (characterVanishesOnAllFormalWords G chi w))
characterVanishesOnAllFormalWords G chi (Finite.combine a b) =
  trans
    (preservesMultiply chi
      (Bridge.interpretWord G a)
      (Bridge.interpretWord G b))
    (trans
      (cong₂ C3._∙_
        (characterVanishesOnAllFormalWords G chi a)
        (characterVanishesOnAllFormalWords G chi b))
      refl)

allC3CharactersTrivialIfMeridiansGenerate :
  (G : Bridge.EquivariantMeridianGroup) →
  MeridianGeneration G →
  (chi : C3Character G) →
  ∀ x → character chi x ≡ C3.c0
allC3CharactersTrivialIfMeridiansGenerate G generation chi x =
  trans
    (sym (cong (character chi) (representationExact generation x)))
    (characterVanishesOnAllFormalWords G chi
      (representingWord generation x))
