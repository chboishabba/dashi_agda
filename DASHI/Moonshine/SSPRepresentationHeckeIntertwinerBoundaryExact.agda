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
-- by the operator-compatible target
--
--   Phi o R_p = T_p o Phi.
--
-- The repository now proves the generic quotient-descent mechanism for the
-- actual finite PrimeCorrespondenceHeckeOn API, and has one nontrivial concrete
-- instance: FactorVec -> SupportMask.  Therefore a sectioned exact quotient
-- plus correspondence congruence *derives* the observable intertwining law.
--
-- What remains open is the domain-specific frontier: construct a corresponding
-- quotient/correspondence map from the SO(3)/candidate-dependent reduction
-- carrier to the intended arithmetic Hecke carrier and identify its induced
-- operator with the arithmetic correspondence.  Carrier equality is neither
-- required nor assumed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as QuotientDescent
import DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact as FiniteModel
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
-- The generic and finite-model quotient stages are now constructed.
------------------------------------------------------------------------

genericQuotientDescentConstructed :
  QuotientDescent.quotientCorrespondenceConstructedFromCongruence
    QuotientDescent.canonicalHeckeCorrespondenceQuotientBoundary
  ≡ true
genericQuotientDescentConstructed =
  QuotientDescent.quotientCorrespondenceConstructedFromCongruenceIsTrue
    QuotientDescent.canonicalHeckeCorrespondenceQuotientBoundary

finiteSupportMaskIntertwinerConstructed :
  FiniteModel.observableHeckeIntertwiningProved
    FiniteModel.canonicalFactorVecSupportMaskHeckeBoundary
  ≡ true
finiteSupportMaskIntertwinerConstructed =
  FiniteModel.observableHeckeIntertwiningProvedIsTrue
    FiniteModel.canonicalFactorVecSupportMaskHeckeBoundary

------------------------------------------------------------------------
-- Commuting-square obligation for the actual SSP representation/modular lane.
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
        "Construct a representation-side exact quotient/correspondence whose induced operator is the intended arithmetic Hecke action; generic quotient descent and the FactorVec/support-mask model are already proved."
    }

record SSPRepresentationHeckeBoundary : Set where
  field
    equalityReplacedByIntertwinerTarget : Bool
    equalityReplacedByIntertwinerTargetIsTrue :
      equalityReplacedByIntertwinerTarget ≡ true

    existingFiniteCorrespondenceAPIReused : Bool
    existingFiniteCorrespondenceAPIReusedIsTrue :
      existingFiniteCorrespondenceAPIReused ≡ true

    genericQuotientCorrespondenceDescentProved : Bool
    genericQuotientCorrespondenceDescentProvedIsTrue :
      genericQuotientCorrespondenceDescentProved ≡ true

    concreteFactorVecSupportMaskIntertwinerProved : Bool
    concreteFactorVecSupportMaskIntertwinerProvedIsTrue :
      concreteFactorVecSupportMaskIntertwinerProved ≡ true

    classicalSO3ToArithmeticHeckeIntertwinerConstructed : Bool
    classicalSO3ToArithmeticHeckeIntertwinerConstructedIsFalse :
      classicalSO3ToArithmeticHeckeIntertwinerConstructed ≡ false

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
    ; genericQuotientCorrespondenceDescentProved = true
    ; genericQuotientCorrespondenceDescentProvedIsTrue = refl
    ; concreteFactorVecSupportMaskIntertwinerProved = true
    ; concreteFactorVecSupportMaskIntertwinerProvedIsTrue = refl
    ; classicalSO3ToArithmeticHeckeIntertwinerConstructed = false
    ; classicalSO3ToArithmeticHeckeIntertwinerConstructedIsFalse = refl
    ; representationReductionClaimedToEqualHeckeAction = false
    ; representationReductionClaimedToEqualHeckeActionIsFalse = refl
    }
