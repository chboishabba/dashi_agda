module DASHI.Moonshine.BrandtStackUnweightingControlsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / EXECUTABLE REFERENCE
--
-- SageMath Brandt-module reference manual, `monodromy_weights`.
-- It defines the weight of an ideal class [I] to be half the number of units
-- of the right order of I and records the executable examples
--
--   BrandtModule(11).monodromy_weights() = (2,3)
--   BrandtModule(37).monodromy_weights() = (1,1,1)
--   BrandtModule(43).monodromy_weights() = (2,1,1,1).
--
-- No DOI is asserted for the software documentation.  Mathematical context:
-- John Voight, "Quaternion Algebras", GTM 288, Springer, 2021,
-- DOI: 10.1007/978-3-030-56694-4.
--
-- OGG CLASSIFICATION AUTHORITY
-- Andrew P. Ogg, "Automorphismes de courbes modulaires", 1974/75, no DOI;
-- John F. R. Duncan and Ken Ono, "The Jack Daniels Problem",
-- J. Number Theory 161 (2016), DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Run the SAME reciprocal-unweighting prescription on two non-Ogg controls.
-- The tuple order is Sage's internal Brandt basis order; it is not identified
-- with named supersingular j-invariants in this file.
--
-- p=37:
--   w=(1,1,1), common scale 1 -> m=(1,1,1), total 3.
--
-- p=43:
--   w=(2,1,1,1), common scale 2 -> m=(1,2,2,2), total 7.
--
-- Thus the tempting statistic `sum monodromy weights = 5` at p=43 is NOT the
-- unweighted fine cardinality.  The source-native reciprocal blow-up has seven
-- states.  This gives an immediate control against treating the p=11 five-state
-- count itself as a universal or purely stacky phenomenon.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingExact as Stack
import DASHI.Moonshine.CandidateLevelExternalOggPredicateExact as External
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge as Ogg

------------------------------------------------------------------------
-- p=37 source-basis carrier.
------------------------------------------------------------------------

data P37BrandtClass : Set where
  p37c0 p37c1 p37c2 : P37BrandtClass

p37MonodromyWeight : P37BrandtClass → Nat
p37MonodromyWeight p37c0 = 1
p37MonodromyWeight p37c1 = 1
p37MonodromyWeight p37c2 = 1

p37SheetMultiplicity : P37BrandtClass → Nat
p37SheetMultiplicity p37c0 = 1
p37SheetMultiplicity p37c1 = 1
p37SheetMultiplicity p37c2 = 1

p37ClearsWeight : (c : P37BrandtClass) →
  p37SheetMultiplicity c * p37MonodromyWeight c ≡ 1
p37ClearsWeight p37c0 = refl
p37ClearsWeight p37c1 = refl
p37ClearsWeight p37c2 = refl

p37StackUnweighting : Stack.ReciprocalUnweighting P37BrandtClass
p37StackUnweighting =
  record
    { Stack.monodromyWeight = p37MonodromyWeight
    ; Stack.sheetMultiplicity = p37SheetMultiplicity
    ; Stack.commonScale = 1
    ; Stack.commonScalePositive = s≤s z≤n
    ; Stack.clearsWeight = p37ClearsWeight
    }

p37UnweightedStateCount : Nat
p37UnweightedStateCount = 1 + 1 + 1

p37UnweightedStateCountIsThree : p37UnweightedStateCount ≡ 3
p37UnweightedStateCountIsThree = refl

------------------------------------------------------------------------
-- p=43 source-basis carrier.
------------------------------------------------------------------------

data P43BrandtClass : Set where
  p43c0 p43c1 p43c2 p43c3 : P43BrandtClass

p43MonodromyWeight : P43BrandtClass → Nat
p43MonodromyWeight p43c0 = 2
p43MonodromyWeight p43c1 = 1
p43MonodromyWeight p43c2 = 1
p43MonodromyWeight p43c3 = 1

p43SheetMultiplicity : P43BrandtClass → Nat
p43SheetMultiplicity p43c0 = 1
p43SheetMultiplicity p43c1 = 2
p43SheetMultiplicity p43c2 = 2
p43SheetMultiplicity p43c3 = 2

p43ClearsWeight : (c : P43BrandtClass) →
  p43SheetMultiplicity c * p43MonodromyWeight c ≡ 2
p43ClearsWeight p43c0 = refl
p43ClearsWeight p43c1 = refl
p43ClearsWeight p43c2 = refl
p43ClearsWeight p43c3 = refl

p43StackUnweighting : Stack.ReciprocalUnweighting P43BrandtClass
p43StackUnweighting =
  record
    { Stack.monodromyWeight = p43MonodromyWeight
    ; Stack.sheetMultiplicity = p43SheetMultiplicity
    ; Stack.commonScale = 2
    ; Stack.commonScalePositive = s≤s z≤n
    ; Stack.clearsWeight = p43ClearsWeight
    }

p43MonodromyWeightSum : Nat
p43MonodromyWeightSum = 2 + 1 + 1 + 1

p43MonodromyWeightSumIsFive : p43MonodromyWeightSum ≡ 5
p43MonodromyWeightSumIsFive = refl

p43UnweightedStateCount : Nat
p43UnweightedStateCount = 1 + 2 + 2 + 2

p43UnweightedStateCountIsSeven : p43UnweightedStateCount ≡ 7
p43UnweightedStateCountIsSeven = refl

p43WeightSumIsNotUnweightedCount : p43MonodromyWeightSum ≡ p43UnweightedStateCount → ⊥
p43WeightSumIsNotUnweightedCount ()

------------------------------------------------------------------------
-- External Ogg controls.  This is POST-HOC classification only; the weights
-- above were not selected using Ogg membership.
------------------------------------------------------------------------

p37IsNotExternallyOgg : External.ExternalOggAt 37 → ⊥
p37IsNotExternallyOgg (Ogg.p2 , ())
p37IsNotExternallyOgg (Ogg.p3 , ())
p37IsNotExternallyOgg (Ogg.p5 , ())
p37IsNotExternallyOgg (Ogg.p7 , ())
p37IsNotExternallyOgg (Ogg.p11 , ())
p37IsNotExternallyOgg (Ogg.p13 , ())
p37IsNotExternallyOgg (Ogg.p17 , ())
p37IsNotExternallyOgg (Ogg.p19 , ())
p37IsNotExternallyOgg (Ogg.p23 , ())
p37IsNotExternallyOgg (Ogg.p29 , ())
p37IsNotExternallyOgg (Ogg.p31 , ())
p37IsNotExternallyOgg (Ogg.p41 , ())
p37IsNotExternallyOgg (Ogg.p47 , ())
p37IsNotExternallyOgg (Ogg.p59 , ())
p37IsNotExternallyOgg (Ogg.p71 , ())

p43IsNotExternallyOgg : External.ExternalOggAt 43 → ⊥
p43IsNotExternallyOgg (Ogg.p2 , ())
p43IsNotExternallyOgg (Ogg.p3 , ())
p43IsNotExternallyOgg (Ogg.p5 , ())
p43IsNotExternallyOgg (Ogg.p7 , ())
p43IsNotExternallyOgg (Ogg.p11 , ())
p43IsNotExternallyOgg (Ogg.p13 , ())
p43IsNotExternallyOgg (Ogg.p17 , ())
p43IsNotExternallyOgg (Ogg.p19 , ())
p43IsNotExternallyOgg (Ogg.p23 , ())
p43IsNotExternallyOgg (Ogg.p29 , ())
p43IsNotExternallyOgg (Ogg.p31 , ())
p43IsNotExternallyOgg (Ogg.p41 , ())
p43IsNotExternallyOgg (Ogg.p47 , ())
p43IsNotExternallyOgg (Ogg.p59 , ())
p43IsNotExternallyOgg (Ogg.p71 , ())

------------------------------------------------------------------------
-- Cheap selector falsifiers.
------------------------------------------------------------------------

record StackCountSignature : Set where
  constructor stackCountSignature
  field
    classCount : Nat
    monodromyWeightSum : Nat
    reciprocalSheetCount : Nat

open StackCountSignature public

p37StackCountSignature : StackCountSignature
p37StackCountSignature = stackCountSignature 3 3 3

p43StackCountSignature : StackCountSignature
p43StackCountSignature = stackCountSignature 4 5 7

record BrandtStackControlBoundary : Set where
  field
    p37SourceWeightsEncoded : Bool
    p37SourceWeightsEncodedIsTrue : p37SourceWeightsEncoded ≡ true

    p43SourceWeightsEncoded : Bool
    p43SourceWeightsEncodedIsTrue : p43SourceWeightsEncoded ≡ true

    sameReciprocalPrescriptionUsed : Bool
    sameReciprocalPrescriptionUsedIsTrue : sameReciprocalPrescriptionUsed ≡ true

    p43FiveWeightSumPromotedToFiveStateCover : Bool
    p43FiveWeightSumPromotedToFiveStateCoverIsFalse :
      p43FiveWeightSumPromotedToFiveStateCover ≡ false

    controlsChosenByWeightPattern : Bool
    controlsChosenByWeightPatternIsFalse : controlsChosenByWeightPattern ≡ false

canonicalBrandtStackControlBoundary : BrandtStackControlBoundary
canonicalBrandtStackControlBoundary =
  record
    { p37SourceWeightsEncoded = true
    ; p37SourceWeightsEncodedIsTrue = refl
    ; p43SourceWeightsEncoded = true
    ; p43SourceWeightsEncodedIsTrue = refl
    ; sameReciprocalPrescriptionUsed = true
    ; sameReciprocalPrescriptionUsedIsTrue = refl
    ; p43FiveWeightSumPromotedToFiveStateCover = false
    ; p43FiveWeightSumPromotedToFiveStateCoverIsFalse = refl
    ; controlsChosenByWeightPattern = false
    ; controlsChosenByWeightPatternIsFalse = refl
    }
