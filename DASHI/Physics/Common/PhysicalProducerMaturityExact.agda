module DASHI.Physics.Common.PhysicalProducerMaturityExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Separate theorem-reducer completion from construction of the mathematical
-- object consumed by that reducer.  A physical producer is not a Boolean
-- status flag: it contains an object together with a proof of the predicate
-- that makes the object admissible.
--
-- SameCarrierSameObject now carries two explicit representation relations.
-- The source-to-intermediate and intermediate-to-output transformations must
-- preserve those relations for every input, and the chosen intermediate and
-- output are definitionally tied to the transformations.  Thus the record
-- proves both literal computation and semantic preservation; arbitrary
-- compositions without same-object evidence cannot inhabit it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

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
    {a b c r s : Level}
    {A : Set a} {B : Set b} {C : Set c}
    (source : A)
    (first : A → B)
    (second : B → C)
    (RepresentsFirst : A → B → Set r)
    (RepresentsSecond : B → C → Set s) :
    Set (a ⊔ b ⊔ c ⊔ r ⊔ s) where
  field
    firstPreservesRepresentation :
      ∀ value → RepresentsFirst value (first value)

    secondPreservesRepresentation :
      ∀ value → RepresentsSecond value (second value)

    intermediate : B
    intermediateIsLiteral : intermediate ≡ first source

    output : C
    outputIsLiteral : output ≡ second intermediate
open SameCarrierSameObject public

sourceRepresentsIntermediate :
  ∀ {a b c r s}
    {A : Set a} {B : Set b} {C : Set c}
    {source : A} {first : A → B} {second : B → C}
    {RepresentsFirst : A → B → Set r}
    {RepresentsSecond : B → C → Set s} →
  (chain : SameCarrierSameObject
    source first second RepresentsFirst RepresentsSecond) →
  RepresentsFirst source (intermediate chain)
sourceRepresentsIntermediate
    {source = source} {RepresentsFirst = RepresentsFirst} chain =
  subst
    (RepresentsFirst source)
    (sym (intermediateIsLiteral chain))
    (firstPreservesRepresentation chain source)
  where
  open import Relation.Binary.PropositionalEquality using (sym)

intermediateRepresentsOutput :
  ∀ {a b c r s}
    {A : Set a} {B : Set b} {C : Set c}
    {source : A} {first : A → B} {second : B → C}
    {RepresentsFirst : A → B → Set r}
    {RepresentsSecond : B → C → Set s} →
  (chain : SameCarrierSameObject
    source first second RepresentsFirst RepresentsSecond) →
  RepresentsSecond (intermediate chain) (output chain)
intermediateRepresentsOutput
    {RepresentsSecond = RepresentsSecond} chain =
  subst
    (RepresentsSecond (intermediate chain))
    (sym (outputIsLiteral chain))
    (secondPreservesRepresentation chain (intermediate chain))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

sameCarrierCompositeExact :
  ∀ {a b c r s}
    {A : Set a} {B : Set b} {C : Set c}
    {source : A} {first : A → B} {second : B → C}
    {RepresentsFirst : A → B → Set r}
    {RepresentsSecond : B → C → Set s} →
  (chain : SameCarrierSameObject
    source first second RepresentsFirst RepresentsSecond) →
  output chain ≡ second (first source)
sameCarrierCompositeExact {second = second} chain =
  trans
    (outputIsLiteral chain)
    (cong second (intermediateIsLiteral chain))

literalSameCarrierChain :
  ∀ {a b c r s}
    {A : Set a} {B : Set b} {C : Set c}
    {RepresentsFirst : A → B → Set r}
    {RepresentsSecond : B → C → Set s} →
  (source : A) (first : A → B) (second : B → C) →
  (firstPreserves : ∀ value → RepresentsFirst value (first value)) →
  (secondPreserves : ∀ value → RepresentsSecond value (second value)) →
  SameCarrierSameObject
    source first second RepresentsFirst RepresentsSecond
literalSameCarrierChain source first second firstPreserves secondPreserves =
  record
    { firstPreservesRepresentation = firstPreserves
    ; secondPreservesRepresentation = secondPreserves
    ; intermediate = first source
    ; intermediateIsLiteral = refl
    ; output = second (first source)
    ; outputIsLiteral = refl }
