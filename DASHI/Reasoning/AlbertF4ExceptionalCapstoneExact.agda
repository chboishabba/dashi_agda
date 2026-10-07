module DASHI.Reasoning.AlbertF4ExceptionalCapstoneExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.AlbertJordanExternalDonorExact as Donor
import DASHI.Reasoning.E8ExceptionalLiftCapstoneExact as E8

------------------------------------------------------------------------
-- ALBERT / F4 MAX-CUT
--
-- The companion Lean tranche now pays a theorem-level scalar/traceless split
-- from tr(1)=3 and types the Jordan-automorphism / E6-unit-stabilizer target.
-- Agda records those as cross-prover receipts, not as Agda kernel theorems.
--
-- The already-paid E6 minuscule 27 is a finite weight orbit.  An Albert algebra
-- is a 27-dimensional vector space.  The correct bridge is via 27 one-
-- dimensional weight lines, not by identifying the finite set with all vectors.
------------------------------------------------------------------------

record ScalarTracelessDecompositionReceipt : Set₁ where
  field
    Carrier : Set
    Scalar : Set
    unit : Carrier
    trace : Carrier → Scalar
    scalarPart : Carrier → Carrier
    tracelessPart : Carrier → Carrier
    traceUnitIsThreeReceipt : Set
    tracelessTraceZeroReceipt : Set
    reconstructionReceipt : Set
    linearEquivalenceToScalarTimesTraceKernelReceipt : Set
open ScalarTracelessDecompositionReceipt public

record AlbertStructureReceipt : Set₁ where
  field
    Carrier : Set
    jordanProduct : Carrier → Carrier → Carrier
    jordanUnit : Carrier
    trace : Carrier → Set
    cubicNorm : Carrier → Set

    bilinearityReceipt : Set
    jordanCommutativityReceipt : Set
    jordanIdentityReceipt : Set
    unitReceipt : Set
    cubicDegreeThreeReceipt : Set
    cubicUnitReceipt : Set
open AlbertStructureReceipt public

record JordanAutomorphismReceipt (A : AlbertStructureReceipt) : Set₁ where
  field
    Automorphism : Set
    act : Automorphism → Carrier A → Carrier A
    productPreservationReceipt : Set
    unitPreservationReceipt : Set
    tracePreservationReceipt : Set
    cubicPreservationReceipt : Set
    tracelessRestrictionReceipt : Set
open JordanAutomorphismReceipt public

record E6F4UnitStabilizerRecognition
  (A : AlbertStructureReceipt)
  (Aut : JordanAutomorphismReceipt A) : Set₁ where
  field
    E6Actor F4Actor : Set
    e6Action : E6Actor → Carrier A → Carrier A
    f4Action : F4Actor → Carrier A → Carrier A
    f4EquivalentToJordanAutomorphismsReceipt : Set
    f4EquivalentToE6UnitStabilizerReceipt : Set
    sameActionReceipt : Set
open E6F4UnitStabilizerRecognition public

record MinusculeWeightLineRecognition
  (A : AlbertStructureReceipt) : Set₁ where
  field
    MinusculeWeight27 : Set
    WeightLine : Set
    weightLineOf : MinusculeWeight27 → WeightLine
    oneDimensionalLineReceipt : Set
    distinctWeightLinesReceipt : Set
    e6ActionIntertwinerReceipt : Set
    schlafliRelationIntertwinerReceipt : Set
open MinusculeWeightLineRecognition public

record TernaryOnePlus26BasisTransport
  (A : AlbertStructureReceipt) : Set₁ where
  field
    Ternary27 NonOrigin26 : Set
    scalarOrigin : Ternary27
    originPlus26BijectionReceipt : Set
    TracelessCarrier : Set
    nonOrigin26IndexesTracelessBasisReceipt : Set
    relationCompatibilityReceipt : Set
    independentActionCompatibilityReceipt : Set
open TernaryOnePlus26BasisTransport public

record AlbertF4Frontier : Set where
  constructor albert-f4-frontier
  field
    externalAlbertDonorPinned : Bool
    externalH3OctonionicCarrierSourceWritten : Bool
    externalJordanProductSourceWritten : Bool
    externalTraceSourceWritten : Bool
    externalCubicDeterminantSourceWritten : Bool
    externalFullCubicIdentitiesSourceWritten : Bool

    leanScalarTracelessLinearEquivalenceSourceWritten : Bool
    scalarTracelessReceiptTypedInAgda : Bool
    albertStructureReceiptTypedInAgda : Bool
    jordanAutomorphismReceiptTypedInAgda : Bool
    e6F4UnitStabilizerReceiptTypedInAgda : Bool
    minusculeWeightLineReceiptTypedInAgda : Bool
    ternaryOnePlus26BasisReceiptTypedInAgda : Bool

    existingTernary27SchlafliRelationPaid : Bool
    existingE6Minuscule27SameObjectReceiptTyped : Bool

    sameKernelAlbertInstantiationPaid : Bool
    actualMinusculeWeightLineRecognitionPaid : Bool
    actualAlbertJordanWeldPaid : Bool
    actualF4AutomorphismRecognitionPaid : Bool
    actualE6UnitStabilizerRecognitionPaid : Bool
    actualTernaryOnePlus26BasisWeldPaid : Bool
    fullTernary240E8RecognitionPaid : Bool
open AlbertF4Frontier public

currentAlbertF4Frontier : AlbertF4Frontier
currentAlbertF4Frontier = albert-f4-frontier
  true true true true true false
  true true true true true true true
  true true
  false false false false false false false

------------------------------------------------------------------------
-- No-promotion checks.
------------------------------------------------------------------------

data Minuscule27CreatesAlbertAlgebra : Set where
data Dimension52CreatesF4 : Set where
data AlbertRecognitionCreatesFullTernaryE8 : Set where

minuscule27DoesNotCreateAlbert : Minuscule27CreatesAlbertAlgebra → {A : Set} → A
minuscule27DoesNotCreateAlbert ()

dimension52DoesNotCreateF4 : Dimension52CreatesF4 → {A : Set} → A
dimension52DoesNotCreateF4 ()

albertDoesNotCreateFullTernaryE8 : AlbertRecognitionCreatesFullTernaryE8 → {A : Set} → A
albertDoesNotCreateFullTernaryE8 ()
