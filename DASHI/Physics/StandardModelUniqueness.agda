module DASHI.Physics.StandardModelUniqueness where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

record GroupData : Set₁ where
  field
    Carrier : Set
    e : Carrier
    _∙_ : Carrier → Carrier → Carrier
    inv : Carrier → Carrier

record GaugeCandidate : Set₁ where
  field
    colour weak hypercharge : GroupData
    Representation : Set
    generations : Nat
    hyperchargeAssignment : Representation → Set
    anomalyFree : Set
    chiral : Set

record GaugeIsomorphism (A B : GaugeCandidate) : Set₁ where
  field
    colourIso : Set
    weakIso : Set
    hyperchargeIso : Set
    representationEquivalent : Set

record StandardModelCharacterization : Set₁ where
  field
    standardModel : GaugeCandidate
    colour-is-SU3 : Set
    weak-is-SU2 : Set
    hypercharge-is-U1 : Set
    threeGenerations : GaugeCandidate.generations standardModel ≡ 3
    hyperchargesCorrect : Set
    anomaliesCancel : GaugeCandidate.anomalyFree standardModel
    admissible : GaugeCandidate → Set
    standardModelAdmissible : admissible standardModel
    unique : ∀ candidate → admissible candidate →
      GaugeIsomorphism candidate standardModel

open StandardModelCharacterization public
