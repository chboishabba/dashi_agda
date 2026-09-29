{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSourceNativeNambuBubbleConditionalExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (_/_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as VacuumReceipt
import DASHI.Physics.Foundations.GRQFTCMP119VacuumEnergyCosmologicalStressCompilerExact as VacuumCompiler
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativePinnedStressSameObjectFrontierExact as Weld
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Bubble
import DASHI.Physics.Foundations.GRQFTUnequalVacuumStaticWallNoGoExact as WallNoGo

------------------------------------------------------------------------
-- SOURCE-NATIVE CONDITIONAL CLOSURE
--
-- Inputs still required:
--
--   1. a rational readout of the literal CMP119 vacuumEnergy sequence with
--      two selected scales reading 21/64 and 19/48;
--   2. proof that this Section-2 source state is the SAME CMP119 object feeding
--      the pinned normalized stress tensor.
--
-- Everything downstream is already compiler-owned.
------------------------------------------------------------------------

record SourceNativeNambuBubbleClosure
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    (source :
      Source.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier)
    {StressTensor : Set}
    (evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor)
    (normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress)
    (vacuum :
      VacuumReceipt.SourceNativeNambuVacuumAmplitudeReceipt source)
    (sameObject :
      Weld.SourceNativePinnedStressSameObjectWeld
        source evaluator cmp119Stress normalized vacuum) : Set₁ where
  constructor source-native-nambu-bubble-closure
  field
    vacuumStressCompiler :
      VacuumCompiler.SourceNativeVacuumCosmologicalStressCompiler vacuum

    bubbleCandidate :
      Bubble.NambuGotoRepulsiveBubbleCandidate
        evaluator cmp119Stress normalized

    interiorSourceVacuumValue :
      VacuumReceipt.vacuumToRat (VacuumReceipt.readout vacuum)
        (Source.vacuumEnergy source
          (VacuumReceipt.interiorScale vacuum))
      ≡ Int.+ 21 / 64

    exteriorSourceVacuumValue :
      VacuumReceipt.vacuumToRat (VacuumReceipt.readout vacuum)
        (Source.vacuumEnergy source
          (VacuumReceipt.exteriorScale vacuum))
      ≡ Int.+ 19 / 48

    flatStaticWallBlocked :
      WallNoGo.staticVacuumFirstIntegral
        WallNoGo.nambuInteriorVacuum
      ≡ WallNoGo.staticVacuumFirstIntegral
        WallNoGo.nambuExteriorVacuum →
      ⊥

open SourceNativeNambuBubbleClosure public

sourceNativeNambuBubbleClosure :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier : Set}
    {source :
      Source.CMP119Section2SourceNativeState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumCarrier}
    {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor}
    {normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress}
    (vacuum :
      VacuumReceipt.SourceNativeNambuVacuumAmplitudeReceipt source)
    (sameObject :
      Weld.SourceNativePinnedStressSameObjectWeld
        source evaluator cmp119Stress normalized vacuum) →
  SourceNativeNambuBubbleClosure
    source evaluator cmp119Stress normalized vacuum sameObject
sourceNativeNambuBubbleClosure vacuum sameObject =
  source-native-nambu-bubble-closure
    (VacuumCompiler.sourceNativeVacuumCosmologicalStressCompiler vacuum)
    (Bubble.nambuGotoRepulsiveBubbleCandidate normalized)
    (VacuumReceipt.interiorAmplitude vacuum)
    (VacuumReceipt.exteriorAmplitude vacuum)
    WallNoGo.nambuStationaryEndpointFirstIntegralsCannotMatch

------------------------------------------------------------------------
-- CURRENT FRONTIER STATUS
------------------------------------------------------------------------

record SourceNativeNambuBubbleClosureBoundary : Set where
  constructor source-native-nambu-bubble-closure-boundary
  field
    downstreamGRJunctionMathConstructed : Bool
    nambuShellFamilyConstructed : Bool
    twoVacuumEffectivePotentialConstructed : Bool
    normalizedCMP119TensorTransportConstructed : Bool
    symbolicVacuumToCosmologicalShapeOwned : Bool
    sourceNativeVacuumEnergySequenceOwned : Bool
    sourceNativeRationalVacuumReadoutOwned : Bool
    requiredTwoSourceNativeVacuumValuesOwned : Bool
    sourceNativePinnedStressSameObjectWeldOwned : Bool
    exactHeadKernelCertified : Bool

canonicalSourceNativeNambuBubbleClosureBoundary :
  SourceNativeNambuBubbleClosureBoundary
canonicalSourceNativeNambuBubbleClosureBoundary =
  source-native-nambu-bubble-closure-boundary
    true true true true true true false false false false
