module DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Replace the too-strong bridge shape
--
--   SSP carrier = Hecke model
--
-- by the operator-compatible target suggested by the representation/modular
-- synthesis:
--
--   Phi o R_p = T_p o Phi.
--
-- An intertwiner preserves the distinction between two carriers while making
-- their dynamics/correspondences comparable.  This module defines that target
-- and a second target matching the repository's existing finite
-- PrimeCorrespondenceHeckeOn API.  It does NOT manufacture either intertwiner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import DASHI.Physics.Closure.PhysicalSSPHeckeModelClosureReceipt as Existing

record PrimeIndexedOperatorIntertwiner
    (RepresentationCarrier ArithmeticCarrier : Set) : Set₁ where
  field
    phi : RepresentationCarrier → ArithmeticCarrier
    reductionOperator :
      Monster.SSP → RepresentationCarrier → RepresentationCarrier
    heckeOperator :
      Monster.SSP → ArithmeticCarrier → ArithmeticCarrier
    intertwines :
      (prime : Monster.SSP) →
      (state : RepresentationCarrier) →
      phi (reductionOperator prime state)
      ≡ heckeOperator prime (phi state)
    intertwinerReceipt : String

open PrimeIndexedOperatorIntertwiner public

record FiniteCorrespondenceObservableIntertwiner
    (RepresentationCarrier HeckeClass : Set) : Set₁ where
  field
    phi : RepresentationCarrier → HeckeClass
    reductionOperator :
      Monster.SSP → RepresentationCarrier → RepresentationCarrier
    representationReadout : RepresentationCarrier → Nat
    heckeCorrespondence : Hecke.PrimeCorrespondenceHeckeOn HeckeClass
    heckeReadout : HeckeClass → Nat
    observableIntertwines :
      (prime : Monster.SSP) →
      (state : RepresentationCarrier) →
      representationReadout (reductionOperator prime state)
      ≡ Hecke.PrimeCorrespondenceHeckeOn.operator
          heckeCorrespondence heckeReadout prime (phi state)
    finiteCorrespondenceReceipt : String

open FiniteCorrespondenceObservableIntertwiner public

------------------------------------------------------------------------
-- The existing closure receipt explicitly leaves carrier equality open.
------------------------------------------------------------------------

existingCarrierEqualityStillOpen :
  Existing.sspCarrierEqualsHeckeModelProved
    Existing.canonicalPhysicalSSPHeckeModelClosureReceipt
  ≡ false
existingCarrierEqualityStillOpen =
  Existing.sspCarrierEqualsHeckeModelProvedIsFalse
    Existing.canonicalPhysicalSSPHeckeModelClosureReceipt

existingGate3StillOpen :
  Existing.gate3Closed
    Existing.canonicalPhysicalSSPHeckeModelClosureReceipt
  ≡ false
existingGate3StillOpen =
  Existing.gate3ClosedIsFalse
    Existing.canonicalPhysicalSSPHeckeModelClosureReceipt

------------------------------------------------------------------------
-- Commuting-square obligation without assuming either side already exists.
------------------------------------------------------------------------

record SSPRepresentationModularIntertwinerTarget : Set₁ where
  field
    RepresentationCarrier : Set
    ArithmeticCarrier : Set
    Intertwiner : Set

    proposedIntertwiner :
      Intertwiner →
      PrimeIndexedOperatorIntertwiner
        RepresentationCarrier ArithmeticCarrier

    witnessConstructed : Bool
    witnessConstructedIsFalse : witnessConstructed ≡ false

    targetDescription : String

open SSPRepresentationModularIntertwinerTarget public

canonicalSSPRepresentationModularIntertwinerTarget :
  SSPRepresentationModularIntertwinerTarget
canonicalSSPRepresentationModularIntertwinerTarget =
  record
    { RepresentationCarrier = ⊤
    ; ArithmeticCarrier = ⊤
    ; Intertwiner = ⊥
    ; proposedIntertwiner = ⊥-elim
    ; witnessConstructed = false
    ; witnessConstructedIsFalse = refl
    ; targetDescription =
        "Construct a prime-indexed reduction/Hecke intertwiner Phi R_p = T_p Phi; carrier equality is not required and is not assumed."
    }

record SSPRepresentationHeckeBoundary : Set where
  field
    equalityReplacedByIntertwinerTarget : Bool
    equalityReplacedByIntertwinerTargetIsTrue :
      equalityReplacedByIntertwinerTarget ≡ true

    existingFiniteCorrespondenceAPIReused : Bool
    existingFiniteCorrespondenceAPIReusedIsTrue :
      existingFiniteCorrespondenceAPIReused ≡ true

    classicalHeckeIntertwinerConstructed : Bool
    classicalHeckeIntertwinerConstructedIsFalse :
      classicalHeckeIntertwinerConstructed ≡ false

    representationReductionClaimedToEqualHeckeAction : Bool
    representationReductionClaimedToEqualHeckeActionIsFalse :
      representationReductionClaimedToEqualHeckeAction ≡ false

canonicalSSPRepresentationHeckeBoundary : SSPRepresentationHeckeBoundary
canonicalSSPRepresentationHeckeBoundary =
  record
    { equalityReplacedByIntertwinerTarget = true
    ; equalityReplacedByIntertwinerTargetIsTrue = refl
    ; existingFiniteCorrespondenceAPIReused = true
    ; existingFiniteCorrespondenceAPIReusedIsTrue = refl
    ; classicalHeckeIntertwinerConstructed = false
    ; classicalHeckeIntertwinerConstructedIsFalse = refl
    ; representationReductionClaimedToEqualHeckeAction = false
    ; representationReductionClaimedToEqualHeckeActionIsFalse = refl
    }
