module DASHI.Moonshine.PositiveSchreierNeighbourSystemExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- Alexander Lubotzky,
-- "Discrete Groups, Expanding Graphs and Invariant Measures",
-- Progress in Mathematics 125, Birkhauser, 1994.
-- DOI: 10.1007/978-3-0346-0332-4.
--
-- DASHI CONTRIBUTION
--
-- Give the set-level producer that the representation/Brandt programme was
-- missing.  A finite family of genuine actions on a vertex set determines a
-- Schreier neighbour system before linearization:
--
--   generator_i x  |->  actual neighbouring vertex.
--
-- The resulting operator is positive because its coefficients are counts of
-- generator-labelled neighbours.  No section, kernel completion or signed
-- matrix construction is available in this API.
--
-- This is intentionally weaker than a full group record: a future consumer may
-- instantiate it from a group action, a double-coset action, or a finite-depth
-- tree action.  Inverse-closed/symmetric generator structure is kept as an
-- additional witness rather than assumed for every directed correspondence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive

record FiniteSchreierProducer (Vertex Generator : Set) : Set₁ where
  field
    generatorCount : Nat
    generatorAt : Fin generatorCount → Generator
    act : Generator → Vertex → Vertex

open FiniteSchreierProducer public

schreierNeighbourSystem :
  ∀ {Vertex Generator : Set} →
  FiniteSchreierProducer Vertex Generator →
  Positive.PositiveFiniteNeighbourSystem Vertex
schreierNeighbourSystem producer =
  record
    { Positive.arity = generatorCount producer
    ; Positive.neighbour = λ vertex edge →
        act producer (generatorAt producer edge) vertex
    }

schreierOperator :
  ∀ {Vertex Generator : Set} →
  FiniteSchreierProducer Vertex Generator →
  (Vertex → Nat) → Vertex → Nat
schreierOperator producer =
  Positive.positiveOperator (schreierNeighbourSystem producer)

------------------------------------------------------------------------
-- Optional inverse-closed geometry.  The producer records a generator-index
-- involution and the actual action inverse law.  This is the set-level input
-- from which ordinary undirected Schreier-edge double counting can later be
-- derived once a finite vertex enumeration/cardinality layer is supplied.
------------------------------------------------------------------------

record InverseClosedSchreierProducer
    (Vertex Generator : Set)
    (producer : FiniteSchreierProducer Vertex Generator) : Set₁ where
  field
    inverseIndex : Fin (generatorCount producer) → Fin (generatorCount producer)
    inverseIndexInvolutive :
      (edge : Fin (generatorCount producer)) →
      inverseIndex (inverseIndex edge) ≡ edge

    actionInverse :
      (edge : Fin (generatorCount producer)) →
      (vertex : Vertex) →
      act producer (generatorAt producer (inverseIndex edge))
        (act producer (generatorAt producer edge) vertex)
      ≡ vertex

open InverseClosedSchreierProducer public

record PositiveSchreierBoundary : Set where
  field
    actionFirstNeighbourProducerConstructed : Bool
    actionFirstNeighbourProducerConstructedIsTrue :
      actionFirstNeighbourProducerConstructed ≡ true

    signedLinearLiftAvailableInProducer : Bool
    signedLinearLiftAvailableInProducerIsFalse :
      signedLinearLiftAvailableInProducer ≡ false

    inverseClosedActionInterfaceConstructed : Bool
    inverseClosedActionInterfaceConstructedIsTrue :
      inverseClosedActionInterfaceConstructed ≡ true

    bruHatTitsOrQuaternionGroupIdentifiedHere : Bool
    bruHatTitsOrQuaternionGroupIdentifiedHereIsFalse :
      bruHatTitsOrQuaternionGroupIdentifiedHere ≡ false

canonicalPositiveSchreierBoundary : PositiveSchreierBoundary
canonicalPositiveSchreierBoundary =
  record
    { actionFirstNeighbourProducerConstructed = true
    ; actionFirstNeighbourProducerConstructedIsTrue = refl
    ; signedLinearLiftAvailableInProducer = false
    ; signedLinearLiftAvailableInProducerIsFalse = refl
    ; inverseClosedActionInterfaceConstructed = true
    ; inverseClosedActionInterfaceConstructedIsTrue = refl
    ; bruHatTitsOrQuaternionGroupIdentifiedHere = false
    ; bruHatTitsOrQuaternionGroupIdentifiedHereIsFalse = refl
    }
