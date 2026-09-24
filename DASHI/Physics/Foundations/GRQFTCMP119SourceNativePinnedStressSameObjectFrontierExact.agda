{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119SourceNativePinnedStressSameObjectFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Source
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTCMP119SourceNativeVacuumAmplitudeBidiExact as Vacuum

------------------------------------------------------------------------
-- LAST SAME-OBJECT FRONTIER
--
-- Two existing CMP119 surfaces are now individually strong enough:
--
--   A. Section-2 source-native state:
--        vacuumEnergy : Nat -> Vacuum
--        effectiveAction : Nat -> Action
--        equation223
--
--   B. pinned/metric stress lane:
--        concrete stress tensor
--        normalized component evaluator
--        literal / recovered-QFT stress attachments.
--
-- Repository archaeology found no typed field saying that B is generated from
-- the exact A instance whose vacuumEnergy is being read.  We therefore make
-- that missing ancestry relation explicit and constructorless.
------------------------------------------------------------------------

data SourceNativePinnedStressSameObjectAuthority : Set where

sourceNativePinnedStressSameObjectAuthorityInhabited : Bool
sourceNativePinnedStressSameObjectAuthorityInhabited = false

sourceNativePinnedStressSameObjectAuthorityInhabitedIsFalse :
  sourceNativePinnedStressSameObjectAuthorityInhabited ≡ false
sourceNativePinnedStressSameObjectAuthorityInhabitedIsFalse = refl

------------------------------------------------------------------------
-- Once that ancestry authority is supplied externally/upstream, no additional
-- numerical tensor theorem remains: the vacuum readout gives the amplitudes and
-- the normalized stress instance gives the tensor shape.
------------------------------------------------------------------------

record SourceNativePinnedStressSameObjectWeld
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
      Vacuum.SourceNativeNambuVacuumAmplitudeReceipt source) : Set₁ where
  field
    sameObjectAuthority :
      SourceNativePinnedStressSameObjectAuthority

open SourceNativePinnedStressSameObjectWeld public

record SourceNativePinnedStressFrontierBoundary : Set where
  constructor source-native-pinned-stress-frontier-boundary
  field
    section2VacuumEnergySurfaceExists : Bool
    pinnedStressSurfaceExists : Bool
    section2Equation223Exists : Bool
    normalizedStressTensorCompilerExists : Bool
    sourceNativeVacuumReadoutLeafIsTyped : Bool
    sameObjectAncestryWeldExists : Bool
    secondTensorEqualityNeededAfterWeld : Bool

canonicalSourceNativePinnedStressFrontierBoundary :
  SourceNativePinnedStressFrontierBoundary
canonicalSourceNativePinnedStressFrontierBoundary =
  source-native-pinned-stress-frontier-boundary
    true true true true true false false
