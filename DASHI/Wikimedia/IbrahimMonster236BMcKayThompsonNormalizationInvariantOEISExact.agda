module DASHI.Wikimedia.IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MONSTER 2B / 3B / 6B MCKAY-THOMPSON NORMALIZATION INVARIANCE
--
-- OEIS exposes several q-series presentations for each class.  The variants
-- can differ at q^0 while agreeing on the positive-degree coefficients.  The
-- weight-two Monster trace is the q^1 coefficient, so the trace used by the
-- 6B -> 3B / 2B cyclic Fourier lane is normalization-stable even though the
-- constant term is not.
--
-- This owner records OEIS as a source/navigation manifestation only.  It does
-- not make OEIS authoritative for Monster class power maps, same-object VOA
-- actions, or representation intertwiners.
------------------------------------------------------------------------

record NormalizationVariant : Set where
  constructor normalization-variant
  field
    oeisId : String
    classLabel : String
    constantTermDescription : String
    qOneCoefficient : Nat
    qTwoCoefficientDescription : String
open NormalizationVariant public

record McKayThompsonNormalizationFamily : Set where
  constructor mckay-thompson-normalization-family
  field
    classLabel : String
    normalizedVariant : NormalizationVariant
    alternateVariantOne : NormalizationVariant
    alternateVariantTwo : NormalizationVariant
    qOneTrace : Nat
    qOneCoefficientIsNormalizationInvariant : Bool
    constantTermIsNormalizationDependent : Bool
    weightTwoTraceComesFromQOneCoefficient : Bool
open McKayThompsonNormalizationFamily public

------------------------------------------------------------------------
-- 2B.
--
-- A007246 is normalized with a(0)=0.
-- A007191 has a(0)=-24.
-- A045479 has a(0)=-8.
-- A035099 is another documented variant with a(0)=40; retained below as an
-- additional coordinate even though the three-variant family already pays the
-- invariance pattern.
-- All expose q^1 coefficient 276 and q^2 coefficient -2048.
------------------------------------------------------------------------

twoBNormalized : NormalizationVariant
twoBNormalized = normalization-variant
  "A007246" "Monster class 2B" "a(0)=0" 276 "q^2=-2048"

twoBMinusTwentyFour : NormalizationVariant
twoBMinusTwentyFour = normalization-variant
  "A007191" "Monster class 2B" "a(0)=-24" 276 "q^2=-2048"

twoBMinusEight : NormalizationVariant
twoBMinusEight = normalization-variant
  "A045479" "Monster class 2B" "a(0)=-8" 276 "q^2=-2048"

twoBPlusFortyOEIS : String
twoBPlusFortyOEIS = "A035099: Monster class 2B variant with a(0)=40; q^1=276 and q^2=-2048"

twoBNormalizationFamily : McKayThompsonNormalizationFamily
twoBNormalizationFamily = mckay-thompson-normalization-family
  "Monster class 2B"
  twoBNormalized twoBMinusTwentyFour twoBMinusEight
  276 true true true

------------------------------------------------------------------------
-- 3B.
--
-- A007244 is normalized with a(0)=0.
-- A030182 has a(0)=-12.
-- A045481 has a(0)=-3.
-- All expose q^1 coefficient 54 and q^2 coefficient -76.
------------------------------------------------------------------------

threeBNormalized : NormalizationVariant
threeBNormalized = normalization-variant
  "A007244" "Monster class 3B" "a(0)=0" 54 "q^2=-76"

threeBMinusTwelve : NormalizationVariant
threeBMinusTwelve = normalization-variant
  "A030182" "Monster class 3B" "a(0)=-12" 54 "q^2=-76"

threeBMinusThree : NormalizationVariant
threeBMinusThree = normalization-variant
  "A045481" "Monster class 3B" "a(0)=-3" 54 "q^2=-76"

threeBNormalizationFamily : McKayThompsonNormalizationFamily
threeBNormalizationFamily = mckay-thompson-normalization-family
  "Monster class 3B"
  threeBNormalized threeBMinusTwelve threeBMinusThree
  54 true true true

------------------------------------------------------------------------
-- 6B.
--
-- A007255 is normalized with a(0)=0.
-- A045485 has a(0)=7.
-- A121665 has a(0)=12.
-- OEIS explicitly records that these agree apart from n=0.  Hence the q^1
-- coefficient 78, and in particular the weight-two trace, survives the choice
-- of constant-term normalization while the apparent 12 does not.
------------------------------------------------------------------------

sixBNormalized : NormalizationVariant
sixBNormalized = normalization-variant
  "A007255" "Monster class 6B" "a(0)=0" 78 "q^2=364"

sixBPlusSeven : NormalizationVariant
sixBPlusSeven = normalization-variant
  "A045485" "Monster class 6B" "a(0)=7" 78 "q^2=364"

sixBPlusTwelve : NormalizationVariant
sixBPlusTwelve = normalization-variant
  "A121665" "Monster class 6B" "a(0)=12" 78 "q^2=364"

sixBNormalizationFamily : McKayThompsonNormalizationFamily
sixBNormalizationFamily = mckay-thompson-normalization-family
  "Monster class 6B"
  sixBNormalized sixBPlusSeven sixBPlusTwelve
  78 true true true

------------------------------------------------------------------------
-- Trace-extraction receipt for the C6 Fourier lane.
------------------------------------------------------------------------

record NormalizationInvariantTraceTriple : Set where
  constructor normalization-invariant-trace-triple
  field
    twoBTrace : Nat
    threeBTrace : Nat
    sixBTrace : Nat
    twoBTraceNormalizationStable : Bool
    threeBTraceNormalizationStable : Bool
    sixBTraceNormalizationStable : Bool
    constantTermsExcludedFromTraceExtraction : Bool
open NormalizationInvariantTraceTriple public

canonicalNormalizationInvariantTraceTriple : NormalizationInvariantTraceTriple
canonicalNormalizationInvariantTraceTriple =
  normalization-invariant-trace-triple 276 54 78 true true true true

------------------------------------------------------------------------
-- WrongType / authority firewalls.
------------------------------------------------------------------------

data NormalizationVariantCreatesSameSourceObject : Set where
data NormalizationInvariantTraceCreatesClassPowerMap : Set where
data ConstantTermCreatesWeightTwoMultiplicity : Set where
data OeisTraceCreatesLiteralVOAAction : Set where

afterQZeroAgreementDoesNotCreateSameSourceObject :
  NormalizationVariantCreatesSameSourceObject → ⊥
afterQZeroAgreementDoesNotCreateSameSourceObject ()

normalizationVariantDoesNotCreateSameSourceObject :
  NormalizationVariantCreatesSameSourceObject → ⊥
normalizationVariantDoesNotCreateSameSourceObject ()

normalizationInvariantTraceDoesNotCreateClassPowerMap :
  NormalizationInvariantTraceCreatesClassPowerMap → ⊥
normalizationInvariantTraceDoesNotCreateClassPowerMap ()

constantTermDoesNotCreateWeightTwoMultiplicity :
  ConstantTermCreatesWeightTwoMultiplicity → ⊥
constantTermDoesNotCreateWeightTwoMultiplicity ()

oeisTraceDoesNotCreateLiteralVOAAction :
  OeisTraceCreatesLiteralVOAAction → ⊥
oeisTraceDoesNotCreateLiteralVOAAction ()

------------------------------------------------------------------------
-- Pareto frontier.
------------------------------------------------------------------------

record NormalizationInvariantOEISFrontier : Set where
  constructor normalization-invariant-oeis-frontier
  field
    twoBNormalizationFamilyLocated : Bool
    threeBNormalizationFamilyLocated : Bool
    sixBNormalizationFamilyLocated : Bool
    qOneTraces2765458PaidAsOEISCoordinates : Bool
    qZeroNormalizationDependencePaid : Bool
    traceExtractionRobustToQZeroNormalization : Bool
    classPowerMapsPaidByThisOwner : Bool
    sameObjectVOAActionPaidByThisOwner : Bool
    nextResidual : String
open NormalizationInvariantOEISFrontier public

currentNormalizationInvariantOEISFrontier : NormalizationInvariantOEISFrontier
currentNormalizationInvariantOEISFrontier = normalization-invariant-oeis-frontier
  true true true true true true false false
  "consume the normalization-invariant trace triple (2B=276, 3B=54, 6B=78) only after the independent ATLAS class-power receipts identify g^3 in 2B and g^2 in 3B. Keep q^0 constants, including the A121665 value 12, outside weight-two trace and multiplicity inference. Next compare higher positive-degree coefficients across the 2B/3B/6B power family only through graded traces on the same selected Monster element."
