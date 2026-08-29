{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact where

------------------------------------------------------------------------
-- ROUND109: SOURCE-OWNED TELESCOPE + SAME-FAMILY SCHWINGER STRESS ENDPOINT
--
-- Round107 isolated finite-stress -> continuum-stress convergence as a physical
-- seam.  Round108 gave a generic fallback through uniform potential convergence
-- plus Cauchy differentiation.  The repository already contains a stronger
-- source-native route for LOCAL INSERTIONS:
--
--   CMP116/CMP119 compatible normalized local expectation expansion
--     -> summable scale increments
--     -> dyadic Cauchy modulus for the SAME ordinary/characteristic insertion.
--
-- Hence a stress first variation that is literally one of those source-native
-- local analytic insertions does not need a fresh convergence estimate.  Its
-- finite-scale response is Cauchy by the published telescope.  Separately,
-- Round85/87 already compile a stress marked source on the SAME completed RG
-- state into a nuclear-continuous continuum field.  The remaining physical seam
-- is therefore SAME-OBJECT identification:
--
--   finite stress insertion = CMP119 local insertion,
--   its Cauchy completion     = completed marked stress field,
--   completed marked stress  = literal `stressTensor Y G`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; subst)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record SourceNativeStressScaleCauchy : Set₁ where
  field
    source : Source.CMP119CompatibleLocalExpectationFlow
    smallHistory : Source.SmallEffectiveCouplingHistory source
    stressInsertion : Source.SourceNativeOrdinaryCharacteristicPair source

    stressDifference : Nat → Nat → ℚ

    -- Literal source-coordinate identification.  Once this is supplied, all
    -- telescope/Cauchy arithmetic is inherited from CMP116/CMP119.
    stressDifferenceIsOrdinarySourceResponse : ∀ start count →
      stressDifference start count ≡
      Sum.ordinaryDifference
        (Source.sourceCompatibleSameFamilyIncrement
          source smallHistory stressInsertion)
        start count
open SourceNativeStressScaleCauchy public

stressResponseCauchyModulus :
  (dataSet : SourceNativeStressScaleCauchy) → ∀ start count →
  stressDifference dataSet start count
  ≤ Scale.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (source dataSet) (smallHistory dataSet) (stressInsertion dataSet)))
      * (Geo.half * Geo.halfPower start)
stressResponseCauchyModulus dataSet start count =
  subst
    (λ selected → selected ≤
      Scale.coefficient
        (Sum.commonMajorant
          (Source.sourceCompatibleSameFamilyIncrement
            (source dataSet) (smallHistory dataSet) (stressInsertion dataSet)))
        * (Geo.half * Geo.halfPower start))
    (stressDifferenceIsOrdinarySourceResponse dataSet start count)
    (Sum.ordinaryCauchyModulus
      (Source.sourceCompatibleSameFamilyIncrement
        (source dataSet) (smallHistory dataSet) (stressInsertion dataSet))
      start count)

record LiteralSchwingerStressMarkedCompletion
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C) : Set₁ where
  field
    continuityScale : Nuclear.ContinuityScale
    CompletedState Composite : Set

    completedSources :
      StressMarked.SameCompletedCompositeStressMarkedSource
        continuityScale CompletedState Composite (Top.StressTensor C)

    -- The continuum stress is not a separately invented field: it is the
    -- stress projection of the SAME completed marked RG state and is literally
    -- the Clay construction's group-indexed stress tensor.
    literalStressIsCompletedMarkedStress :
      Marked.continuumComposite
        (StressMarked.stressField
          (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
            completedSources))
      ≡ Top.stressTensor Y group
open LiteralSchwingerStressMarkedCompletion public

record Round109Boundary : Set where
  field
    sourceTelescopeAlreadyGivesStressCauchyAfterInsertionWeld : Set
    sourceTelescopeAlreadyGivesStressCauchyAfterInsertionWeldWitness :
      sourceTelescopeAlreadyGivesStressCauchyAfterInsertionWeld

    finiteCauchySequenceAloneIdentifiesLiteralSchwingerStress : Set
    finiteCauchySequenceAloneIdentifiesLiteralSchwingerStressNotAutomatic :
      finiteCauchySequenceAloneIdentifiesLiteralSchwingerStress → Set

-- Proven/source-owned pieces.
sourceCompatibleLocalExpectationTelescopeLevel : ProofLevel
sourceCompatibleLocalExpectationTelescopeLevel = standardImported

stressResponseCauchyModulusCompilerLevel : ProofLevel
stressResponseCauchyModulusCompilerLevel = machineChecked

sameCompletedMarkedStressFieldCompilerRound109Level : ProofLevel
sameCompletedMarkedStressFieldCompilerRound109Level =
  StressMarked.sameCompletedCompositeStressFieldCompilerLevel

-- Remaining physical same-object welds.  No new telescope or independent
-- continuum stress construction is required once these are supplied.
literalStressInsertionIsCMP119LocalInsertionLevel : ProofLevel
literalStressInsertionIsCMP119LocalInsertionLevel = conditional

literalStressCauchyCompletionIsCompletedMarkedStressLevel : ProofLevel
literalStressCauchyCompletionIsCompletedMarkedStressLevel = conditional

literalCompletedMarkedStressIsClayStressTensorLevel : ProofLevel
literalCompletedMarkedStressIsClayStressTensorLevel = conditional
