module DASHI.Moonshine.OggSSP2BCarnahanHalfTranslationParityExtractionExact where

------------------------------------------------------------------------
-- CARNahan 2B HALF-TRANSLATION: EXACT GRADED-EXPONENT PARITY CUT
--
-- SOURCE: Scott Carnahan, "A Self-Dual Integral Form of the Moonshine
-- Module", SIGMA 15 (2019) 030, Corollary 3.25,
-- DOI 10.3842/SIGMA.2019.030.
--
-- For the 2B class the source states:
--
--   H0 trace = (T(tau) + T(tau + 1/2))/2
--   H1 trace = (T(tau) - T(tau + 1/2))/2.
--
-- With the standard weight-n exponent q^(n-1), half-translation multiplies
-- a term by (-1)^(n-1).  Consequently H0 selects ODD weight indices and
-- H1 selects EVEN weight indices, INCLUDING the q^(-1) weight-zero pole.
--
-- This is a reconstruction of the Fourier PARITY FILTER, not a construction
-- of the integral Tate modules themselves.  Crucially no five-way inertia
-- sector splitting, DVR length or analytic valuation follows from this cut.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Carnahan
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSP2BSourceIndexedDVRValuationIdentificationExact as TwoB
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Independent weight parity and q-exponent parity.
--
-- Avoid interpreting the half-translation as (-1)^n: the correct exponent is
-- n-1, and the weight-zero pole has ODD q-exponent parity.
------------------------------------------------------------------------

weightParity : Nat -> Urano.DegreeParity
weightParity zero = Urano.evenDegree
weightParity (suc zero) = Urano.oddDegree
weightParity (suc (suc n)) = weightParity n

data ExponentParity : Set where
  evenExponent oddExponent : ExponentParity

qExponentParity : Nat -> ExponentParity
qExponentParity zero = oddExponent
qExponentParity (suc zero) = evenExponent
qExponentParity (suc (suc n)) = qExponentParity n

oppositeParity : Urano.DegreeParity -> ExponentParity
oppositeParity Urano.evenDegree = oddExponent
oppositeParity Urano.oddDegree = evenExponent

weightToExponentParity :
  (n : Nat) ->
  qExponentParity n ≡ oppositeParity (weightParity n)
weightToExponentParity zero = refl
weightToExponentParity (suc zero) = refl
weightToExponentParity (suc (suc n)) =
  weightToExponentParity n

------------------------------------------------------------------------
-- 2. Actual H0/H1 half-sum/half-difference routing.
------------------------------------------------------------------------

tateBranch : Nat -> Carnahan.TateParity
tateBranch zero = Carnahan.tateH1
tateBranch (suc zero) = Carnahan.tateH0
tateBranch (suc (suc n)) = tateBranch n

branchOfExponentParity :
  ExponentParity -> Carnahan.TateParity
branchOfExponentParity evenExponent = Carnahan.tateH0
branchOfExponentParity oddExponent = Carnahan.tateH1

tateBranchIsFourierParity :
  (n : Nat) ->
  tateBranch n ≡ branchOfExponentParity (qExponentParity n)
tateBranchIsFourierParity zero = refl
tateBranchIsFourierParity (suc zero) = refl
tateBranchIsFourierParity (suc (suc n)) =
  tateBranchIsFourierParity n

branchOfWeightParity :
  Urano.DegreeParity -> Carnahan.TateParity
branchOfWeightParity Urano.evenDegree = Carnahan.tateH1
branchOfWeightParity Urano.oddDegree = Carnahan.tateH0

tateBranchIsOppositeWeightParity :
  (n : Nat) ->
  tateBranch n ≡ branchOfWeightParity (weightParity n)
tateBranchIsOppositeWeightParity zero = refl
tateBranchIsOppositeWeightParity (suc zero) = refl
tateBranchIsOppositeWeightParity (suc (suc n)) =
  tateBranchIsOppositeWeightParity n

weightZeroPoleBelongsToH1 :
  tateBranch 0 ≡ Carnahan.tateH1
weightZeroPoleBelongsToH1 = refl

weightOneBelongsToH0 :
  tateBranch 1 ≡ Carnahan.tateH0
weightOneBelongsToH0 = refl

weightTwoBelongsToH1 :
  tateBranch 2 ≡ Carnahan.tateH1
weightTwoBelongsToH1 = refl

------------------------------------------------------------------------
-- 3. Constructive lossless filtering of an arbitrary coefficient family.
--
-- This is the algebraic index routing underlying Carnahan's two traces.
-- Coefficients are parameters, NOT computed from V^natural or Tate groups.
------------------------------------------------------------------------

data MaybeCoefficient (A : Set) : Set where
  absent : MaybeCoefficient A
  present : A -> MaybeCoefficient A

selectH0 :
  {A : Set} -> Nat -> A -> MaybeCoefficient A
selectH0 n a with tateBranch n
... | Carnahan.tateH0 = present a
... | Carnahan.tateH1 = absent

selectH1 :
  {A : Set} -> Nat -> A -> MaybeCoefficient A
selectH1 n a with tateBranch n
... | Carnahan.tateH0 = absent
... | Carnahan.tateH1 = present a

recoverSplit :
  {A : Set} -> Nat ->
  MaybeCoefficient A -> MaybeCoefficient A ->
  MaybeCoefficient A
recoverSplit n a b with tateBranch n
... | Carnahan.tateH0 = a
... | Carnahan.tateH1 = b

paritySplitReopens :
  {A : Set} -> (n : Nat) -> (a : A) ->
  recoverSplit n (selectH0 n a) (selectH1 n a)
  ≡ present a
paritySplitReopens n a with tateBranch n
... | Carnahan.tateH0 = refl
... | Carnahan.tateH1 = refl

h0AndH1AreNotFiveIndependentSourcePieces :
  Set
h0AndH1AreNotFiveIndependentSourcePieces =
  Carnahan.TateParity -> TwoB.TwoBSourceSlot

-- Constructive pigeonhole obstruction: three specific sector slots cannot
-- be injected into the two parity branches, hence neither can all five.
-- Unlike a constructor-free declaration, this theorem accepts ANY proposed
-- classifier and derives an actual collision.

identityNotMinus :
  TwoB.identitySlot ≡ TwoB.minusOneSlot -> ⊥
identityNotMinus ()

identityNotFour :
  TwoB.identitySlot ≡ TwoB.orderFourSlot -> ⊥
identityNotFour ()

minusNotFour :
  TwoB.minusOneSlot ≡ TwoB.orderFourSlot -> ⊥
minusNotFour ()

noInjectionOfFiveSlotsIntoTateParity :
  (classify : TwoB.TwoBSourceSlot -> Carnahan.TateParity) ->
  ((left right : TwoB.TwoBSourceSlot) ->
    classify left ≡ classify right -> left ≡ right) ->
  ⊥
noInjectionOfFiveSlotsIntoTateParity classify inject
  with classify TwoB.identitySlot
     | classify TwoB.minusOneSlot
     | classify TwoB.orderFourSlot
... | Carnahan.tateH0 | Carnahan.tateH0 | c =
  identityNotMinus (inject TwoB.identitySlot TwoB.minusOneSlot refl)
... | Carnahan.tateH0 | Carnahan.tateH1 | Carnahan.tateH0 =
  identityNotFour (inject TwoB.identitySlot TwoB.orderFourSlot refl)
... | Carnahan.tateH0 | Carnahan.tateH1 | Carnahan.tateH1 =
  minusNotFour (inject TwoB.minusOneSlot TwoB.orderFourSlot refl)
... | Carnahan.tateH1 | Carnahan.tateH1 | c =
  identityNotMinus (inject TwoB.identitySlot TwoB.minusOneSlot refl)
... | Carnahan.tateH1 | Carnahan.tateH0 | Carnahan.tateH1 =
  identityNotFour (inject TwoB.identitySlot TwoB.orderFourSlot refl)
... | Carnahan.tateH1 | Carnahan.tateH0 | Carnahan.tateH0 =
  minusNotFour (inject TwoB.minusOneSlot TwoB.orderFourSlot refl)

------------------------------------------------------------------------
-- 4. Source attribution / nonpromotion.
------------------------------------------------------------------------

carnahanReceipt : Carnahan.PBIntegralTateCohomologyReceipt
carnahanReceipt = Carnahan.canonicalPBIntegralTateCohomologyReceipt

uranoReceipt : Urano.TwoBUranoIntegralModuleParityBoundary
uranoReceipt = Urano.canonicalTwoBUranoIntegralModuleParityBoundary

data FourierParityFilterIsFiveSectorIgusaLocalization : Set where
data FourierParityFilterDeterminesDVRCompositionLengths : Set where
data HalfTranslationFormulaProvesMonsterValuation : Set where

parityFilterDoesNotDefineIgusaLocalization :
  FourierParityFilterIsFiveSectorIgusaLocalization -> ⊥
parityFilterDoesNotDefineIgusaLocalization ()

parityFilterDoesNotDetermineDVRLengths :
  FourierParityFilterDeterminesDVRCompositionLengths -> ⊥
parityFilterDoesNotDetermineDVRLengths ()

halfTranslationDoesNotProveMonsterValuation :
  HalfTranslationFormulaProvesMonsterValuation -> ⊥
halfTranslationDoesNotProveMonsterValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryFormalReconstruction

record TwoBHalfTranslationParityExtractionBoundary : Set where
  constructor two-b-half-translation-parity-extraction-boundary
  field
    halfTranslationSourceCarnahan : Bool
    qExponentOffsetByOneIncluded : Bool
    weightZeroPoleRoutesToH1 : Bool
    oddWeightRoutesToH0 : Bool
    evenWeightRoutesToH1 : Bool
    genericCoefficientSplitReopens : Bool
    actualIntegralTatePiecesConstructed : Bool
    fiveIgusaSectorsIdentified : Bool
    DVRLengthFromParityProved : Bool
    correctedMonsterValuationProved : Bool

canonicalTwoBHalfTranslationParityExtractionBoundary :
  TwoBHalfTranslationParityExtractionBoundary
canonicalTwoBHalfTranslationParityExtractionBoundary =
  two-b-half-translation-parity-extraction-boundary
    true true true true true true false false false false
