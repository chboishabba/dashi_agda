module DASHI.Physics.Common.PhysicalProducerMaturityExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Separate theorem-reducer completion from construction of the mathematical
-- object consumed by that reducer.  A physical producer is not a Boolean
-- status flag: it contains an object together with a proof of the predicate
-- that makes the object admissible.  SameCarrierSameObject then records a
-- literal source -> intermediate -> output chain and proves that the final
-- output is the composite applied to the original source.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

data CompletionStage : Set where
  reducerComplete certificateSchemaComplete syntheticFixtureComplete
    physicalProducerComplete scaleUniformProducerComplete
    continuumProducerComplete : CompletionStage

record PhysicalProducer
    {o p : Level}
    (Object : Set o)
    (Admissible : Object → Set p) : Set (lsuc (o ⊔ p)) where
  field
    object : Object
    admissible : Admissible object
open PhysicalProducer public

mapPhysicalProducer :
  ∀ {a b p q}
    {A : Set a} {B : Set b}
    {PA : A → Set p} {PB : B → Set q} →
  (f : A → B) →
  (preserves : ∀ {value} → PA value → PB (f value)) →
  PhysicalProducer A PA →
  PhysicalProducer B PB
mapPhysicalProducer f preserves producer = record
  { object = f (object producer)
  ; admissible = preserves (admissible producer) }

record SameCarrierSameObject
    {a b c : Level}
    {A : Set a} {B : Set b} {C : Set c}
    (source : A)
    (first : A → B)
    (second : B → C) : Set (a ⊔ b ⊔ c) where
  field
    intermediate : B
    intermediateIsLiteral : intermediate ≡ first source
    output : C
    outputIsLiteral : output ≡ second intermediate
open SameCarrierSameObject public

sameCarrierCompositeExact :
  ∀ {a b c}
    {A : Set a} {B : Set b} {C : Set c}
    {source : A} {first : A → B} {second : B → C} →
  (chain : SameCarrierSameObject source first second) →
  output chain ≡ second (first source)
sameCarrierCompositeExact chain =
  trans
    (outputIsLiteral chain)
    (cong _ (intermediateIsLiteral chain))

literalSameCarrierChain :
  ∀ {a b c}
    {A : Set a} {B : Set b} {C : Set c}
    (source : A) (first : A → B) (second : B → C) →
  SameCarrierSameObject source first second
literalSameCarrierChain source first second = record
  { intermediate = first source
  ; intermediateIsLiteral = refl
  ; output = second (first source)
  ; outputIsLiteral = refl }
