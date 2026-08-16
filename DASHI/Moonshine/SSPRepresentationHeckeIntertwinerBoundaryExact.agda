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
-- The generic quotient-descent mechanism is now proved for the actual finite
-- PrimeCorrespondenceHeckeOn API, with a concrete FactorVec -> SupportMask
-- instance.  The natural-level version now permits level-dependent fine and
-- coarse carriers.  On the representation side the explicit fine carrier and
-- quotient are also constructed:
--
--   level 2: two spinor basis states -> one SU(2) doublet sector;
--   level 2j+1: SO(3) weights 0,+/-1,...,+/-j -> matched D_(2j+1) sectors.
--
-- Therefore the remaining representation-side producer is no longer an
-- unnamed quotient.  It is specifically the source-justified level-indexed
-- 15-way correspondence on those fine states, together with proof that it
-- respects the explicit weight-to-sector quotient.  After that, the induced
-- sector correspondence must still be identified/intertwined with the actual
-- arithmetic Hecke/Brandt correspondence.  No carrier equality is assumed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as QuotientDescent
import DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact as FiniteModel
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact as IndexedDescent
import DASHI.Moonshine.CandidateReductionSectorFamilyExact as Sector
import DASHI.Moonshine.SO3WeightMatchedDihedralQuotientExact as Weight
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
-- Constructed quotient/intertwiner stages.
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

indexedQuotientDescentConstructed :
  IndexedDescent.levelwiseQuotientIntertwiningDerived
    IndexedDescent.canonicalIndexedLevelHeckeQuotientBoundary
  ≡ true
indexedQuotientDescentConstructed =
  IndexedDescent.levelwiseQuotientIntertwiningDerivedIsTrue
    IndexedDescent.canonicalIndexedLevelHeckeQuotientBoundary

representationSectorFamilyConstructed :
  Sector.levelDependentReductionCarrierConstructed
    Sector.canonicalCandidateReductionSectorFamilyBoundary
  ≡ true
representationSectorFamilyConstructed =
  Sector.levelDependentReductionCarrierConstructedIsTrue
    Sector.canonicalCandidateReductionSectorFamilyBoundary

representationWeightQuotientConstructed :
  Weight.matchedDihedralSectorQuotientConstructed
    Weight.canonicalSO3WeightMatchedDihedralBoundary
  ≡ true
representationWeightQuotientConstructed =
  Weight.matchedDihedralSectorQuotientConstructedIsTrue
    Weight.canonicalSO3WeightMatchedDihedralBoundary

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
        "Construct the source-justified indexed correspondence on the explicit spinor/SO(3) fine weight carrier; prove congruence under the explicit weight-to-matched-sector quotient; then identify the induced sector correspondence with the intended arithmetic Hecke/Brandt action."
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

    indexedLevelDependentDescentProved : Bool
    indexedLevelDependentDescentProvedIsTrue :
      indexedLevelDependentDescentProved ≡ true

    explicitSO3WeightToSectorQuotientProved : Bool
    explicitSO3WeightToSectorQuotientProvedIsTrue :
      explicitSO3WeightToSectorQuotientProved ≡ true

    fineSO3WeightCorrespondenceConstructed : Bool
    fineSO3WeightCorrespondenceConstructedIsFalse :
      fineSO3WeightCorrespondenceConstructed ≡ false

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
    ; indexedLevelDependentDescentProved = true
    ; indexedLevelDependentDescentProvedIsTrue = refl
    ; explicitSO3WeightToSectorQuotientProved = true
    ; explicitSO3WeightToSectorQuotientProvedIsTrue = refl
    ; fineSO3WeightCorrespondenceConstructed = false
    ; fineSO3WeightCorrespondenceConstructedIsFalse = refl
    ; classicalSO3ToArithmeticHeckeIntertwinerConstructed = false
    ; classicalSO3ToArithmeticHeckeIntertwinerConstructedIsFalse = refl
    ; representationReductionClaimedToEqualHeckeAction = false
    ; representationReductionClaimedToEqualHeckeActionIsFalse = refl
    }
