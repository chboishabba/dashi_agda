module DASHI.Physics.Closure.MonsterVOAFixedPointReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.MoonshineBridge as MoonshineBridge
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Closure.MonstrousMoonshineSSPBoundaryReceipt as Boundary
import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP

------------------------------------------------------------------------
-- Monster VOA fixed-point receipt.
--
-- This receipt records JMD's Moonshine claim as a fail-closed structural
-- interface:
--
-- * VM is treated as carrier/register dynamics over the 15 SSP primes.
-- * the Monster order prime support is exactly that 15-prime support.
-- * a VOA/symmetry algebra action is recorded only on admissible dynamics.
-- * the j-invariant is recorded as a modular/Moonshine fixed-point and
--   zero-residual interpretation.
--
-- It does not prove McKay-Thompson, Hauptmodul, Hecke-eigenvalue, VOA
-- construction, or physical/ontological promotion claims.  If T_p(j) is
-- mentioned, it is carried only as a literature-bound obligation unless a
-- separate local proof is supplied.

data MonsterVOAFixedPointStatus : Set where
  monsterVOAFixedPointRecordedFailClosed :
    MonsterVOAFixedPointStatus

data MonsterVOAComponent : Set where
  vmCarrierRegisterDynamicsOverSSPPrimes :
    MonsterVOAComponent

  monsterOrderPrimeSupportEqualsSSP15 :
    MonsterVOAComponent

  voaSymmetryActsOnAdmissibleDynamics :
    MonsterVOAComponent

  jInvariantFixedPointZeroResidualInterpretation :
    MonsterVOAComponent

  moonshineNumericsRecordedOnly :
    MonsterVOAComponent

  heckeDetailsRemainLiteratureBoundary :
    MonsterVOAComponent

canonicalMonsterVOAComponents :
  List MonsterVOAComponent
canonicalMonsterVOAComponents =
  vmCarrierRegisterDynamicsOverSSPPrimes
  ∷ monsterOrderPrimeSupportEqualsSSP15
  ∷ voaSymmetryActsOnAdmissibleDynamics
  ∷ jInvariantFixedPointZeroResidualInterpretation
  ∷ moonshineNumericsRecordedOnly
  ∷ heckeDetailsRemainLiteratureBoundary
  ∷ []

data VMRegisterRole : Set where
  carrierPrimeRegister :
    VMRegisterRole

  stateCoordinateRegister :
    VMRegisterRole

record VMRegister : Set where
  constructor vmRegister
  field
    primeLane :
      Lane.MonsterPrimeLane

    primeNat :
      Nat

    primeNatIsLaneNat :
      primeNat ≡ Lane.monsterPrimeLaneToNat primeLane

    role :
      VMRegisterRole

open VMRegister public

p2Register : VMRegister
p2Register = vmRegister Lane.p2 2 refl carrierPrimeRegister

p3Register : VMRegister
p3Register = vmRegister Lane.p3 3 refl carrierPrimeRegister

p5Register : VMRegister
p5Register = vmRegister Lane.p5 5 refl carrierPrimeRegister

p7Register : VMRegister
p7Register = vmRegister Lane.p7 7 refl carrierPrimeRegister

p11Register : VMRegister
p11Register = vmRegister Lane.p11 11 refl carrierPrimeRegister

p13Register : VMRegister
p13Register = vmRegister Lane.p13 13 refl carrierPrimeRegister

p17Register : VMRegister
p17Register = vmRegister Lane.p17 17 refl carrierPrimeRegister

p19Register : VMRegister
p19Register = vmRegister Lane.p19 19 refl carrierPrimeRegister

p23Register : VMRegister
p23Register = vmRegister Lane.p23 23 refl carrierPrimeRegister

p29Register : VMRegister
p29Register = vmRegister Lane.p29 29 refl carrierPrimeRegister

p31Register : VMRegister
p31Register = vmRegister Lane.p31 31 refl carrierPrimeRegister

p41Register : VMRegister
p41Register = vmRegister Lane.p41 41 refl carrierPrimeRegister

p47Register : VMRegister
p47Register = vmRegister Lane.p47 47 refl carrierPrimeRegister

p59Register : VMRegister
p59Register = vmRegister Lane.p59 59 refl carrierPrimeRegister

p71Register : VMRegister
p71Register = vmRegister Lane.p71 71 refl carrierPrimeRegister

canonicalVMRegisters :
  List VMRegister
canonicalVMRegisters =
  p2Register
  ∷ p3Register
  ∷ p5Register
  ∷ p7Register
  ∷ p11Register
  ∷ p13Register
  ∷ p17Register
  ∷ p19Register
  ∷ p23Register
  ∷ p29Register
  ∷ p31Register
  ∷ p41Register
  ∷ p47Register
  ∷ p59Register
  ∷ p71Register
  ∷ []

record VMCarrierRegisterDynamics : Setω where
  field
    carrierPrimeLanes :
      List Lane.MonsterPrimeLane

    carrierPrimeLanesAreCanonical :
      carrierPrimeLanes ≡ Lane.canonicalMonsterPrimeLane

    carrierPrimeNats :
      List Nat

    carrierPrimeNatsAreSSP15 :
      carrierPrimeNats ≡ SSP.canonicalSupersingularPrimeLaneNats

    registers :
      List VMRegister

    registersAreCanonical :
      registers ≡ canonicalVMRegisters

    dynamicsAdmissible :
      Bool

    dynamicsAdmissibleIsTrue :
      dynamicsAdmissible ≡ true

open VMCarrierRegisterDynamics public

canonicalVMCarrierRegisterDynamics :
  VMCarrierRegisterDynamics
canonicalVMCarrierRegisterDynamics =
  record
    { carrierPrimeLanes =
        Lane.canonicalMonsterPrimeLane
    ; carrierPrimeLanesAreCanonical =
        refl
    ; carrierPrimeNats =
        SSP.canonicalSupersingularPrimeLaneNats
    ; carrierPrimeNatsAreSSP15 =
        refl
    ; registers =
        canonicalVMRegisters
    ; registersAreCanonical =
        refl
    ; dynamicsAdmissible =
        true
    ; dynamicsAdmissibleIsTrue =
        refl
    }

record MonsterOrderPrimeSupportReceipt : Set where
  field
    monsterOrderPrimeSupportNats :
      List Nat

    monsterOrderPrimeSupportIsExactlySSP15 :
      monsterOrderPrimeSupportNats
      ≡ SSP.canonicalSupersingularPrimeLaneNats

    noExtraMonsterOrderPrimeSupport :
      Bool

    noExtraMonsterOrderPrimeSupportIsTrue :
      noExtraMonsterOrderPrimeSupport ≡ true

    noMissingSSPPrimeSupport :
      Bool

    noMissingSSPPrimeSupportIsTrue :
      noMissingSSPPrimeSupport ≡ true

open MonsterOrderPrimeSupportReceipt public

canonicalMonsterOrderPrimeSupportReceipt :
  MonsterOrderPrimeSupportReceipt
canonicalMonsterOrderPrimeSupportReceipt =
  record
    { monsterOrderPrimeSupportNats =
        SSP.canonicalSupersingularPrimeLaneNats
    ; monsterOrderPrimeSupportIsExactlySSP15 =
        refl
    ; noExtraMonsterOrderPrimeSupport =
        true
    ; noExtraMonsterOrderPrimeSupportIsTrue =
        refl
    ; noMissingSSPPrimeSupport =
        true
    ; noMissingSSPPrimeSupportIsTrue =
        refl
    }

data VOASymmetryActionBoundary : Set where
  actsOnlyOnAdmissibleDynamics :
    VOASymmetryActionBoundary

  actionRecordedNotConstructed :
    VOASymmetryActionBoundary

  noPhysicalActionPromotion :
    VOASymmetryActionBoundary

canonicalVOASymmetryActionBoundary :
  List VOASymmetryActionBoundary
canonicalVOASymmetryActionBoundary =
  actsOnlyOnAdmissibleDynamics
  ∷ actionRecordedNotConstructed
  ∷ noPhysicalActionPromotion
  ∷ []

record VOASymmetryActionReceipt : Setω where
  field
    dynamics :
      VMCarrierRegisterDynamics

    voaSymmetryAlgebraRecorded :
      Bool

    voaSymmetryAlgebraRecordedIsTrue :
      voaSymmetryAlgebraRecorded ≡ true

    actsOnAdmissibleDynamics :
      Bool

    actsOnAdmissibleDynamicsIsTrue :
      actsOnAdmissibleDynamics ≡ true

    constructsMonsterVOAHere :
      Bool

    constructsMonsterVOAHereIsFalse :
      constructsMonsterVOAHere ≡ false

    actionBoundary :
      List VOASymmetryActionBoundary

    actionBoundaryIsCanonical :
      actionBoundary ≡ canonicalVOASymmetryActionBoundary

open VOASymmetryActionReceipt public

canonicalVOASymmetryActionReceipt :
  VOASymmetryActionReceipt
canonicalVOASymmetryActionReceipt =
  record
    { dynamics =
        canonicalVMCarrierRegisterDynamics
    ; voaSymmetryAlgebraRecorded =
        true
    ; voaSymmetryAlgebraRecordedIsTrue =
        refl
    ; actsOnAdmissibleDynamics =
        true
    ; actsOnAdmissibleDynamicsIsTrue =
        refl
    ; constructsMonsterVOAHere =
        false
    ; constructsMonsterVOAHereIsFalse =
        refl
    ; actionBoundary =
        canonicalVOASymmetryActionBoundary
    ; actionBoundaryIsCanonical =
        refl
    }

data JInvariantInterpretationBoundary : Set where
  modularMoonshineFixedPointInterpretation :
    JInvariantInterpretationBoundary

  zeroResidualInterpretation :
    JInvariantInterpretationBoundary

  coefficient196884RecordedAsMoonshineNumerics :
    JInvariantInterpretationBoundary

  irrep196883RecordedAsMoonshineNumerics :
    JInvariantInterpretationBoundary

  noHeckeEigenvalueDetailAsserted :
    JInvariantInterpretationBoundary

canonicalJInvariantInterpretationBoundary :
  List JInvariantInterpretationBoundary
canonicalJInvariantInterpretationBoundary =
  modularMoonshineFixedPointInterpretation
  ∷ zeroResidualInterpretation
  ∷ coefficient196884RecordedAsMoonshineNumerics
  ∷ irrep196883RecordedAsMoonshineNumerics
  ∷ noHeckeEigenvalueDetailAsserted
  ∷ []

record JInvariantFixedPointZeroResidualReceipt : Set where
  field
    jCoefficient :
      Nat

    jCoefficientIs196884 :
      jCoefficient ≡ MoonshineBridge.moonshineCoefficient

    monsterIrrepNumericalDimension :
      Nat

    monsterIrrepNumericalDimensionIs196883 :
      monsterIrrepNumericalDimension ≡ 196883

    modularMoonshineFixedPointInterpretationRecorded :
      Bool

    modularMoonshineFixedPointInterpretationRecordedIsTrue :
      modularMoonshineFixedPointInterpretationRecorded ≡ true

    zeroResidualInterpretationRecorded :
      Bool

    zeroResidualInterpretationRecordedIsTrue :
      zeroResidualInterpretationRecorded ≡ true

    heckeEigenvalueDetailsProvedHere :
      Bool

    heckeEigenvalueDetailsProvedHereIsFalse :
      heckeEigenvalueDetailsProvedHere ≡ false

    TpJStatement :
      String

    interpretationBoundary :
      List JInvariantInterpretationBoundary

    interpretationBoundaryIsCanonical :
      interpretationBoundary ≡ canonicalJInvariantInterpretationBoundary

open JInvariantFixedPointZeroResidualReceipt public

TpJLiteratureBoundaryStatement : String
TpJLiteratureBoundaryStatement =
  "Any T_p(j) or Hecke-eigenvalue detail is a literature-bound obligation here unless separately proven in-repo."

canonicalJInvariantFixedPointZeroResidualReceipt :
  JInvariantFixedPointZeroResidualReceipt
canonicalJInvariantFixedPointZeroResidualReceipt =
  record
    { jCoefficient =
        MoonshineBridge.moonshineCoefficient
    ; jCoefficientIs196884 =
        refl
    ; monsterIrrepNumericalDimension =
        196883
    ; monsterIrrepNumericalDimensionIs196883 =
        refl
    ; modularMoonshineFixedPointInterpretationRecorded =
        true
    ; modularMoonshineFixedPointInterpretationRecordedIsTrue =
        refl
    ; zeroResidualInterpretationRecorded =
        true
    ; zeroResidualInterpretationRecordedIsTrue =
        refl
    ; heckeEigenvalueDetailsProvedHere =
        false
    ; heckeEigenvalueDetailsProvedHereIsFalse =
        refl
    ; TpJStatement =
        TpJLiteratureBoundaryStatement
    ; interpretationBoundary =
        canonicalJInvariantInterpretationBoundary
    ; interpretationBoundaryIsCanonical =
        refl
    }

data MonsterVOAPromotionToken : Set where

monsterVOAPromotionImpossibleHere :
  MonsterVOAPromotionToken →
  ⊥
monsterVOAPromotionImpossibleHere ()

monsterVOAFixedPointStatement : String
monsterVOAFixedPointStatement =
  "JMD Moonshine is receipted as VM carrier/register dynamics over the 15 SSP primes, exact Monster-order prime support, VOA/symmetry action on admissible dynamics, and j-invariant fixed-point/zero-residual interpretation; Hecke details and promotions remain fail-closed."

record MonsterVOAFixedPointReceipt : Setω where
  field
    status :
      MonsterVOAFixedPointStatus

    statusIsFailClosed :
      status ≡ monsterVOAFixedPointRecordedFailClosed

    boundaryReceipt :
      Boundary.MonstrousMoonshineSSPBoundaryReceipt

    components :
      List MonsterVOAComponent

    componentsAreCanonical :
      components ≡ canonicalMonsterVOAComponents

    vmDynamics :
      VMCarrierRegisterDynamics

    monsterOrderPrimeSupport :
      MonsterOrderPrimeSupportReceipt

    voaSymmetryAction :
      VOASymmetryActionReceipt

    jInvariantInterpretation :
      JInvariantFixedPointZeroResidualReceipt

    assertsUnprovedHeckeEigenvalueDetails :
      Bool

    assertsUnprovedHeckeEigenvalueDetailsIsFalse :
      assertsUnprovedHeckeEigenvalueDetails ≡ false

    physicalPromotion :
      Bool

    physicalPromotionIsFalse :
      physicalPromotion ≡ false

    ontologyPromotion :
      Bool

    ontologyPromotionIsFalse :
      ontologyPromotion ≡ false

    politicalPromotion :
      Bool

    politicalPromotionIsFalse :
      politicalPromotion ≡ false

    promotionFlags :
      List MonsterVOAPromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotionWithoutAuthority :
      MonsterVOAPromotionToken → ⊥

    statement :
      String

    statementIsCanonical :
      statement ≡ monsterVOAFixedPointStatement

    receiptBoundary :
      List String

open MonsterVOAFixedPointReceipt public

canonicalMonsterVOAFixedPointReceipt :
  MonsterVOAFixedPointReceipt
canonicalMonsterVOAFixedPointReceipt =
  record
    { status =
        monsterVOAFixedPointRecordedFailClosed
    ; statusIsFailClosed =
        refl
    ; boundaryReceipt =
        Boundary.canonicalMonstrousMoonshineSSPBoundaryReceipt
    ; components =
        canonicalMonsterVOAComponents
    ; componentsAreCanonical =
        refl
    ; vmDynamics =
        canonicalVMCarrierRegisterDynamics
    ; monsterOrderPrimeSupport =
        canonicalMonsterOrderPrimeSupportReceipt
    ; voaSymmetryAction =
        canonicalVOASymmetryActionReceipt
    ; jInvariantInterpretation =
        canonicalJInvariantFixedPointZeroResidualReceipt
    ; assertsUnprovedHeckeEigenvalueDetails =
        false
    ; assertsUnprovedHeckeEigenvalueDetailsIsFalse =
        refl
    ; physicalPromotion =
        false
    ; physicalPromotionIsFalse =
        refl
    ; ontologyPromotion =
        false
    ; ontologyPromotionIsFalse =
        refl
    ; politicalPromotion =
        false
    ; politicalPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotionWithoutAuthority =
        monsterVOAPromotionImpossibleHere
    ; statement =
        monsterVOAFixedPointStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "VM is recorded only as carrier/register dynamics over the 15 SSP primes." ∷
        "Monster order prime support is exactly the 15 SSP primes, with no extra or missing prime support." ∷
        "VOA/symmetry action is recorded only on admissible dynamics; no VOA construction is proven here." ∷
        "The j-invariant is recorded as modular/Moonshine fixed-point and zero-residual interpretation." ∷
        "196884 and 196883 are recorded as factual Moonshine numerics only." ∷
        "T_p(j) and Hecke-eigenvalue details remain literature-bound obligations unless separately proven in-repo." ∷
        "No ontology, political, physical, CKM, YM, NS, SM, Clay, or terminal promotion is issued." ∷
        []
    }

monsterVOAFixedPointUsesExactlySSP15 :
  monsterOrderPrimeSupportNats
    (monsterOrderPrimeSupport canonicalMonsterVOAFixedPointReceipt)
  ≡ SSP.canonicalSupersingularPrimeLaneNats
monsterVOAFixedPointUsesExactlySSP15 =
  refl

monsterVOAFixedPointNoUnprovedHeckeDetails :
  assertsUnprovedHeckeEigenvalueDetails
    canonicalMonsterVOAFixedPointReceipt
  ≡ false
monsterVOAFixedPointNoUnprovedHeckeDetails =
  refl

monsterVOAFixedPointNoPhysicalPromotion :
  physicalPromotion canonicalMonsterVOAFixedPointReceipt ≡ false
monsterVOAFixedPointNoPhysicalPromotion =
  refl
