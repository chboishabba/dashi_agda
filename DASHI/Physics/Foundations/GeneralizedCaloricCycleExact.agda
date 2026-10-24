module DASHI.Physics.Foundations.GeneralizedCaloricCycleExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERALIZED CALORIC CYCLE
--
-- A finite first-law fixture is separated from physical realization.  The
-- same accounting shape may be inhabited by magnetic/electric/stress/pressure
-- controls, while moire geometry remains only a candidate control until a
-- same-object material cycle is measured.
------------------------------------------------------------------------

data CaloricControlKind : Set where
  magneticFieldControl : CaloricControlKind
  electricFieldControl : CaloricControlKind
  uniaxialStressControl : CaloricControlKind
  hydrostaticPressureControl : CaloricControlKind
  moireGeometryCandidate : CaloricControlKind

record FiniteCaloricCycle : Set where
  constructor finite-caloric-cycle
  field
    controlKind : CaloricControlKind
    coldHeat : Nat
    hotHeat : Nat
    workInput : Nat
    coldHeatPositiveMagnitude : Nat
    coldHeatPositive : coldHeat ≡ suc coldHeatPositiveMagnitude
    firstLawReceipt : hotHeat ≡ coldHeat + workInput

open FiniteCaloricCycle public

canonicalFiniteCaloricCycle : FiniteCaloricCycle
canonicalFiniteCaloricCycle =
  finite-caloric-cycle
    magneticFieldControl
    4
    7
    3
    3
    refl
    refl

record GeneralizedCaloricCandidate : Set where
  constructor generalized-caloric-candidate
  field
    candidateControl : CaloricControlKind
    responseSurfaceReference : String
    cyclePathReference : String
    sameObjectMeasuredResponse : Bool
    calibratedControlPath : Bool
    measuredUsefulColdHeat : Bool
    measuredWorkInput : Bool
    hysteresisAndRateLossPaid : Bool
    repeatedCyclePaid : Bool
    materialIntegrityPaid : Bool

open GeneralizedCaloricCandidate public

canonicalGeometryCaloricCandidate : GeneralizedCaloricCandidate
canonicalGeometryCaloricCandidate =
  generalized-caloric-candidate
    moireGeometryCandidate
    "S(T,n,strain,twist,field) same-object response surface required"
    "closed twist/strain/gate/filling path with thermal reservoirs required"
    false false false false false false false

record PhysicalGeneralizedCaloricWitness
    (candidate : GeneralizedCaloricCandidate) : Set where
  constructor physical-generalized-caloric-witness
  field
    sameObjectMeasuredResponseIsTrue :
      sameObjectMeasuredResponse candidate ≡ true
    calibratedControlPathIsTrue :
      calibratedControlPath candidate ≡ true
    measuredUsefulColdHeatIsTrue :
      measuredUsefulColdHeat candidate ≡ true
    measuredWorkInputIsTrue :
      measuredWorkInput candidate ≡ true
    hysteresisAndRateLossPaidIsTrue :
      hysteresisAndRateLossPaid candidate ≡ true
    repeatedCyclePaidIsTrue :
      repeatedCyclePaid candidate ≡ true
    materialIntegrityPaidIsTrue :
      materialIntegrityPaid candidate ≡ true

open PhysicalGeneralizedCaloricWitness public

record GeneralizedCaloricBoundary : Set where
  constructor generalized-caloric-boundary
  field
    finiteFixtureDoesNotPayPhysicalCycle : Bool
    positiveColdHeatArithmeticDoesNotIdentifyMaterial : Bool
    entropyChangeDoesNotByItselfPayUsefulCooling : Bool
    closedControlLoopDoesNotByItselfPayThermodynamicCycle : Bool
    commonFirstLawShapeDoesNotIdentifyMechanism : Bool
    geometryControlCandidateDoesNotClaimObservedMoireCaloricEffect : Bool

open GeneralizedCaloricBoundary public

canonicalGeneralizedCaloricBoundary : GeneralizedCaloricBoundary
canonicalGeneralizedCaloricBoundary =
  generalized-caloric-boundary true true true true true true
