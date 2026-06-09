module DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTFiniteBuildingYMGapTransferBoundary as BTGap
import DASHI.Physics.Closure.BTFiniteHodgeEffectiveActionTheoremBoundary as BTHodgeAction
import DASHI.Physics.Closure.BTFiniteHodgeStarObligation as BTHodge
import DASHI.Physics.Closure.FiniteCoercivityOnSelectedCarrier as FiniteCoercivity
import DASHI.Physics.Closure.YMStrictSelectedHodgeAlgebraLaws as SelectedHodge

------------------------------------------------------------------------
-- BT finite metric/gauge compatibility kappa boundary.
--
-- This module refines the finite-building Yang-Mills mass-gap route by
-- naming the missing compatibility constant:
--
--   kappa_d : finite metric/gauge compatibility coercivity witness.
--
-- The selected finite carrier already has finite-stage evidence:
-- selected-Hodge algebra laws, selected finite IBP/effective-action target,
-- and Nat-side coercivity.  The hard missing theorem is uniform positivity
-- across BT depth:
--
--   inf_d kappa_d > 0.
--
-- This file is a boundary/target receipt.  It does not prove the uniform
-- lower bound, does not transport the selected finite lower bound to
-- continuum Yang-Mills, and keeps spectral-gap, continuum, Clay YM, and
-- terminal promotion false.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data BTDepth : Set where
  depth0 :
    BTDepth
  depth1 :
    BTDepth
  depth2 :
    BTDepth
  arbitraryDepth :
    BTDepth

canonicalFiniteDepths : List BTDepth
canonicalFiniteDepths =
  depth0
  ∷ depth1
  ∷ depth2
  ∷ []

data KappaWitnessClass : Set where
  selectedFiniteKappaWitness :
    KappaWitnessClass
  depthIndexedKappaFamily :
    KappaWitnessClass
  uniformInfimumKappaTarget :
    KappaWitnessClass

data MetricGaugeCompatibilityComponent : Set where
  finiteBTMetricWeights :
    MetricGaugeCompatibilityComponent
  selectedGaugeConnection :
    MetricGaugeCompatibilityComponent
  selectedHodgeStarAlgebra :
    MetricGaugeCompatibilityComponent
  finiteEffectiveActionPairing :
    MetricGaugeCompatibilityComponent
  gaugeInvariantNormComparison :
    MetricGaugeCompatibilityComponent
  finiteCoerciveLowerBound :
    MetricGaugeCompatibilityComponent

canonicalMetricGaugeCompatibilityComponents :
  List MetricGaugeCompatibilityComponent
canonicalMetricGaugeCompatibilityComponents =
  finiteBTMetricWeights
  ∷ selectedGaugeConnection
  ∷ selectedHodgeStarAlgebra
  ∷ finiteEffectiveActionPairing
  ∷ gaugeInvariantNormComparison
  ∷ finiteCoerciveLowerBound
  ∷ []

data BTKappaBoundaryRow : Set where
  btFiniteBuildingGapTransferConsumedRow :
    BTKappaBoundaryRow
  selectedHodgeAlgebraLawsConsumedRow :
    BTKappaBoundaryRow
  btFiniteHodgeStarObligationConsumedRow :
    BTKappaBoundaryRow
  btFiniteHodgeEffectiveActionConsumedRow :
    BTKappaBoundaryRow
  finiteCoercivitySelectedCarrierConsumedRow :
    BTKappaBoundaryRow
  kappaDCompatibilityWitnessNamedRow :
    BTKappaBoundaryRow
  finiteMetricGaugeCompatibilityNamedRow :
    BTKappaBoundaryRow
  depthIndexedKappaFamilyNamedRow :
    BTKappaBoundaryRow
  uniformInfimumPositiveTargetNamedRow :
    BTKappaBoundaryRow
  uniformInfimumPositiveBlockerRow :
    BTKappaBoundaryRow
  continuumTransferHeldFalseRow :
    BTKappaBoundaryRow
  clayAndTerminalHeldFalseRow :
    BTKappaBoundaryRow

canonicalBTKappaBoundaryRows :
  List BTKappaBoundaryRow
canonicalBTKappaBoundaryRows =
  btFiniteBuildingGapTransferConsumedRow
  ∷ selectedHodgeAlgebraLawsConsumedRow
  ∷ btFiniteHodgeStarObligationConsumedRow
  ∷ btFiniteHodgeEffectiveActionConsumedRow
  ∷ finiteCoercivitySelectedCarrierConsumedRow
  ∷ kappaDCompatibilityWitnessNamedRow
  ∷ finiteMetricGaugeCompatibilityNamedRow
  ∷ depthIndexedKappaFamilyNamedRow
  ∷ uniformInfimumPositiveTargetNamedRow
  ∷ uniformInfimumPositiveBlockerRow
  ∷ continuumTransferHeldFalseRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data BTKappaHardBlocker : Set where
  missingWeightedBTMetricGaugeCompatibility :
    BTKappaHardBlocker
  missingGaugeInvariantNormComparison :
    BTKappaHardBlocker
  missingDepthIndexedKappaCoercivityFamily :
    BTKappaHardBlocker
  missingUniformPositiveInfimumKappa :
    BTKappaHardBlocker
  missingContinuumTransferFromKappaFamily :
    BTKappaHardBlocker
  missingClayYangMillsAuthorityToken :
    BTKappaHardBlocker

canonicalBTKappaHardBlockers :
  List BTKappaHardBlocker
canonicalBTKappaHardBlockers =
  missingWeightedBTMetricGaugeCompatibility
  ∷ missingGaugeInvariantNormComparison
  ∷ missingDepthIndexedKappaCoercivityFamily
  ∷ missingUniformPositiveInfimumKappa
  ∷ missingContinuumTransferFromKappaFamily
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

data KappaDCompatibilityWitness : Set where
  selectedFiniteKappaDCompatibilityWitness :
    BTDepth →
    KappaDCompatibilityWitness

data FiniteMetricGaugeCompatibility : Set₂ where
  finiteMetricGaugeCompatibilityFromSelectedHodgeAndAction :
    SelectedHodge.StrictSelectedHodgeAlgebraLaws →
    BTHodgeAction.BTFiniteHodgeEffectiveActionTheoremBoundary →
    KappaDCompatibilityWitness →
    FiniteMetricGaugeCompatibility

data DepthIndexedKappaFamilyTarget : Set where
  depthIndexedKappaFamilyFromFiniteWitness :
    (BTDepth → KappaDCompatibilityWitness) →
    DepthIndexedKappaFamilyTarget

data UniformKappaInfimumTarget : Set where
  infimumKappaDPositiveTarget :
    UniformKappaInfimumTarget

canonicalKappaWitnessDepth0 :
  KappaDCompatibilityWitness
canonicalKappaWitnessDepth0 =
  selectedFiniteKappaDCompatibilityWitness depth0

canonicalKappaWitnessAtDepth :
  BTDepth → KappaDCompatibilityWitness
canonicalKappaWitnessAtDepth depth =
  selectedFiniteKappaDCompatibilityWitness depth

canonicalDepthIndexedKappaFamily :
  DepthIndexedKappaFamilyTarget
canonicalDepthIndexedKappaFamily =
  depthIndexedKappaFamilyFromFiniteWitness canonicalKappaWitnessAtDepth

canonicalFiniteMetricGaugeCompatibility :
  FiniteMetricGaugeCompatibility
canonicalFiniteMetricGaugeCompatibility =
  finiteMetricGaugeCompatibilityFromSelectedHodgeAndAction
    SelectedHodge.canonicalStrictSelectedHodgeAlgebraLaws
    BTHodgeAction.canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
    canonicalKappaWitnessDepth0

canonicalUniformKappaInfimumTarget :
  UniformKappaInfimumTarget
canonicalUniformKappaInfimumTarget =
  infimumKappaDPositiveTarget

FiniteKappaCompatibilityWitnessRecorded : Bool
FiniteKappaCompatibilityWitnessRecorded = true

FiniteMetricGaugeCompatibilityRecorded : Bool
FiniteMetricGaugeCompatibilityRecorded = true

DepthIndexedKappaFamilyTargetRecorded : Bool
DepthIndexedKappaFamilyTargetRecorded = true

UniformInfimumKappaPositiveProved : Bool
UniformInfimumKappaPositiveProved = false

ContinuumTransferFromKappaFamilyProved : Bool
ContinuumTransferFromKappaFamilyProved = false

spectralGapPromoted : Bool
spectralGapPromoted = false

continuumTransferPromoted : Bool
continuumTransferPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

terminalPromotion : Bool
terminalPromotion = false

finiteKappaCompatibilityWitnessRecordedIsTrue :
  FiniteKappaCompatibilityWitnessRecorded ≡ true
finiteKappaCompatibilityWitnessRecordedIsTrue =
  refl

finiteMetricGaugeCompatibilityRecordedIsTrue :
  FiniteMetricGaugeCompatibilityRecorded ≡ true
finiteMetricGaugeCompatibilityRecordedIsTrue =
  refl

depthIndexedKappaFamilyTargetRecordedIsTrue :
  DepthIndexedKappaFamilyTargetRecorded ≡ true
depthIndexedKappaFamilyTargetRecordedIsTrue =
  refl

uniformInfimumKappaPositiveProvedIsFalse :
  UniformInfimumKappaPositiveProved ≡ false
uniformInfimumKappaPositiveProvedIsFalse =
  refl

continuumTransferFromKappaFamilyProvedIsFalse :
  ContinuumTransferFromKappaFamilyProved ≡ false
continuumTransferFromKappaFamilyProvedIsFalse =
  refl

record BTFiniteMetricGaugeCompatibilityKappaBoundary : Setω where
  field
    consumedBTFiniteBuildingYMGapTransferCanonical :
      Bool

    consumedBTFiniteBuildingYMGapTransferCanonicalIsTrue :
      consumedBTFiniteBuildingYMGapTransferCanonical ≡ true

    consumedSelectedHodgeAlgebra :
      SelectedHodge.StrictSelectedHodgeAlgebraLaws

    consumedSelectedHodgeAlgebraIsCanonical :
      consumedSelectedHodgeAlgebra
      ≡
      SelectedHodge.canonicalStrictSelectedHodgeAlgebraLaws

    consumedBTFiniteHodgeStarObligation :
      BTHodge.BTFiniteHodgeStarObligation

    consumedBTFiniteHodgeStarObligationIsCanonical :
      consumedBTFiniteHodgeStarObligation
      ≡
      BTHodge.canonicalBTFiniteHodgeStarObligation

    consumedBTFiniteHodgeEffectiveAction :
      BTHodgeAction.BTFiniteHodgeEffectiveActionTheoremBoundary

    consumedBTFiniteHodgeEffectiveActionIsCanonical :
      consumedBTFiniteHodgeEffectiveAction
      ≡
      BTHodgeAction.canonicalBTFiniteHodgeEffectiveActionTheoremBoundary

    consumedFiniteCoercivityOnSelectedCarrierCanonical :
      Bool

    consumedFiniteCoercivityOnSelectedCarrierCanonicalIsTrue :
      consumedFiniteCoercivityOnSelectedCarrierCanonical ≡ true

    finiteDepths :
      List BTDepth

    finiteDepthsAreCanonical :
      finiteDepths ≡ canonicalFiniteDepths

    compatibilityComponents :
      List MetricGaugeCompatibilityComponent

    compatibilityComponentsAreCanonical :
      compatibilityComponents ≡ canonicalMetricGaugeCompatibilityComponents

    kappaWitnessClass :
      KappaWitnessClass

    kappaWitnessClassIsSelectedFinite :
      kappaWitnessClass ≡ selectedFiniteKappaWitness

    kappaDCompatibilityWitness :
      KappaDCompatibilityWitness

    kappaDCompatibilityWitnessIsCanonical :
      kappaDCompatibilityWitness ≡ canonicalKappaWitnessDepth0

    finiteMetricGaugeCompatibility :
      FiniteMetricGaugeCompatibility

    finiteMetricGaugeCompatibilityIsCanonical :
      finiteMetricGaugeCompatibility
      ≡
      canonicalFiniteMetricGaugeCompatibility

    depthIndexedKappaFamilyTarget :
      DepthIndexedKappaFamilyTarget

    depthIndexedKappaFamilyTargetIsCanonical :
      depthIndexedKappaFamilyTarget ≡ canonicalDepthIndexedKappaFamily

    uniformInfimumKappaPositiveTarget :
      UniformKappaInfimumTarget

    uniformInfimumKappaPositiveTargetIsCanonical :
      uniformInfimumKappaPositiveTarget
      ≡
      canonicalUniformKappaInfimumTarget

    finiteKappaCompatibilityWitnessRecorded :
      FiniteKappaCompatibilityWitnessRecorded ≡ true

    finiteMetricGaugeCompatibilityRecorded :
      FiniteMetricGaugeCompatibilityRecorded ≡ true

    depthIndexedKappaFamilyTargetRecorded :
      DepthIndexedKappaFamilyTargetRecorded ≡ true

    upstreamBTGapUniformLowerBoundStillFalse :
      BTGap.uniformFiniteBuildingLowerBoundProved
        BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
      ≡
      false

    upstreamBTGapContinuumTransferStillFalse :
      BTGap.continuumTransferFromFiniteBTBuildingProved
        BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
      ≡
      false

    selectedHodgeMetricPromotionStillFalse :
      SelectedHodge.metricHodgeStarPromoted consumedSelectedHodgeAlgebra
      ≡
      false

    selectedHodgeYMPromotionStillFalse :
      SelectedHodge.sourcedYMPromoted consumedSelectedHodgeAlgebra
      ≡
      false

    btHodgeObligationTerminalStillFalse :
      BTHodge.terminalPromotion consumedBTFiniteHodgeStarObligation
      ≡
      false

    btHodgeActionClayStillFalse :
      BTHodgeAction.clayYangMillsPromoted
        consumedBTFiniteHodgeEffectiveAction
      ≡
      false

    finiteCoercivityGapStillFalse :
      FiniteCoercivity.gapReceiptConstructed
        FiniteCoercivity.canonicalFiniteCoercivityOnSelectedCarrierReceipt
      ≡
      false

    exactKappaBlocker :
      BTKappaHardBlocker

    exactKappaBlockerIsUniformInfimum :
      exactKappaBlocker ≡ missingUniformPositiveInfimumKappa

    hardBlockers :
      List BTKappaHardBlocker

    hardBlockersAreCanonical :
      hardBlockers ≡ canonicalBTKappaHardBlockers

    rows :
      List BTKappaBoundaryRow

    rowsAreCanonical :
      rows ≡ canonicalBTKappaBoundaryRows

    rowCount :
      Nat

    rowCountIs12 :
      rowCount ≡ 12

    componentCount :
      Nat

    componentCountIs6 :
      componentCount ≡ 6

    finiteDepthCount :
      Nat

    finiteDepthCountIs3 :
      finiteDepthCount ≡ 3

    uniformInfimumKappaPositive :
      Bool

    uniformInfimumKappaPositiveIsFalse :
      uniformInfimumKappaPositive ≡ false

    continuumTransferFromKappaFamily :
      Bool

    continuumTransferFromKappaFamilyIsFalse :
      continuumTransferFromKappaFamily ≡ false

    spectralGapPromotedField :
      Bool

    spectralGapPromotedFieldIsFalse :
      spectralGapPromotedField ≡ false

    continuumTransferPromotedField :
      Bool

    continuumTransferPromotedFieldIsFalse :
      continuumTransferPromotedField ≡ false

    clayYangMillsPromotedField :
      Bool

    clayYangMillsPromotedFieldIsFalse :
      clayYangMillsPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    boundary :
      List String

open BTFiniteMetricGaugeCompatibilityKappaBoundary public

canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary :
  BTFiniteMetricGaugeCompatibilityKappaBoundary
canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary =
  record
    { consumedBTFiniteBuildingYMGapTransferCanonical =
        true
    ; consumedBTFiniteBuildingYMGapTransferCanonicalIsTrue =
        refl
    ; consumedSelectedHodgeAlgebra =
        SelectedHodge.canonicalStrictSelectedHodgeAlgebraLaws
    ; consumedSelectedHodgeAlgebraIsCanonical =
        refl
    ; consumedBTFiniteHodgeStarObligation =
        BTHodge.canonicalBTFiniteHodgeStarObligation
    ; consumedBTFiniteHodgeStarObligationIsCanonical =
        refl
    ; consumedBTFiniteHodgeEffectiveAction =
        BTHodgeAction.canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
    ; consumedBTFiniteHodgeEffectiveActionIsCanonical =
        refl
    ; consumedFiniteCoercivityOnSelectedCarrierCanonical =
        true
    ; consumedFiniteCoercivityOnSelectedCarrierCanonicalIsTrue =
        refl
    ; finiteDepths =
        canonicalFiniteDepths
    ; finiteDepthsAreCanonical =
        refl
    ; compatibilityComponents =
        canonicalMetricGaugeCompatibilityComponents
    ; compatibilityComponentsAreCanonical =
        refl
    ; kappaWitnessClass =
        selectedFiniteKappaWitness
    ; kappaWitnessClassIsSelectedFinite =
        refl
    ; kappaDCompatibilityWitness =
        canonicalKappaWitnessDepth0
    ; kappaDCompatibilityWitnessIsCanonical =
        refl
    ; finiteMetricGaugeCompatibility =
        canonicalFiniteMetricGaugeCompatibility
    ; finiteMetricGaugeCompatibilityIsCanonical =
        refl
    ; depthIndexedKappaFamilyTarget =
        canonicalDepthIndexedKappaFamily
    ; depthIndexedKappaFamilyTargetIsCanonical =
        refl
    ; uniformInfimumKappaPositiveTarget =
        canonicalUniformKappaInfimumTarget
    ; uniformInfimumKappaPositiveTargetIsCanonical =
        refl
    ; finiteKappaCompatibilityWitnessRecorded =
        refl
    ; finiteMetricGaugeCompatibilityRecorded =
        refl
    ; depthIndexedKappaFamilyTargetRecorded =
        refl
    ; upstreamBTGapUniformLowerBoundStillFalse =
        BTGap.canonicalBTFiniteBuildingYMGapTransferUniformLowerBoundFalse
    ; upstreamBTGapContinuumTransferStillFalse =
        BTGap.canonicalBTFiniteBuildingYMGapTransferContinuumTransferFalse
    ; selectedHodgeMetricPromotionStillFalse =
        SelectedHodge.canonicalStrictSelectedHodgeAlgebraMetricPromotionFalse
    ; selectedHodgeYMPromotionStillFalse =
        SelectedHodge.canonicalStrictSelectedHodgeAlgebraYMPromotionFalse
    ; btHodgeObligationTerminalStillFalse =
        BTHodge.canonicalBTFiniteHodgeTerminalPromotionFalse
    ; btHodgeActionClayStillFalse =
        BTHodgeAction.canonicalBTFiniteHodgeEffectiveActionClayYMFalse
    ; finiteCoercivityGapStillFalse =
        FiniteCoercivity.FiniteCoercivityOnSelectedCarrierReceipt.gapReceiptConstructedIsFalse
          FiniteCoercivity.canonicalFiniteCoercivityOnSelectedCarrierReceipt
    ; exactKappaBlocker =
        missingUniformPositiveInfimumKappa
    ; exactKappaBlockerIsUniformInfimum =
        refl
    ; hardBlockers =
        canonicalBTKappaHardBlockers
    ; hardBlockersAreCanonical =
        refl
    ; rows =
        canonicalBTKappaBoundaryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        12
    ; rowCountIs12 =
        refl
    ; componentCount =
        6
    ; componentCountIs6 =
        refl
    ; finiteDepthCount =
        3
    ; finiteDepthCountIs3 =
        refl
    ; uniformInfimumKappaPositive =
        false
    ; uniformInfimumKappaPositiveIsFalse =
        refl
    ; continuumTransferFromKappaFamily =
        false
    ; continuumTransferFromKappaFamilyIsFalse =
        refl
    ; spectralGapPromotedField =
        false
    ; spectralGapPromotedFieldIsFalse =
        refl
    ; continuumTransferPromotedField =
        false
    ; continuumTransferPromotedFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        false
    ; clayYangMillsPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        false
    ; terminalPromotionFieldIsFalse =
        refl
    ; boundary =
        "kappa_d is recorded as the finite metric/gauge compatibility coercivity witness for selected BT depth"
        ∷ "The selected finite Hodge laws and finite Hodge effective-action boundary are consumed as finite compatibility evidence"
        ∷ "The Nat-side selected carrier coercivity receipt is consumed but not transported to the real YM quotient"
        ∷ "The depth-indexed kappa family is named as a target; no uniform lower bound is proved"
        ∷ "The exact kappa hard blocker is missingUniformPositiveInfimumKappa, i.e. inf_d kappa_d > 0"
        ∷ "The upstream BT gap-transfer hard blocker remains the missing uniform finite-building mass-gap lower bound"
        ∷ "No spectral-gap, continuum-transfer, Clay Yang-Mills, or terminal promotion follows"
        ∷ []
    }

canonicalBTKappaBoundaryRowCountIs12 :
  listCount canonicalBTKappaBoundaryRows ≡ 12
canonicalBTKappaBoundaryRowCountIs12 =
  refl

canonicalBTKappaComponentCountIs6 :
  listCount canonicalMetricGaugeCompatibilityComponents ≡ 6
canonicalBTKappaComponentCountIs6 =
  refl

canonicalBTKappaFiniteDepthCountIs3 :
  listCount canonicalFiniteDepths ≡ 3
canonicalBTKappaFiniteDepthCountIs3 =
  refl

canonicalBTKappaExactBlocker :
  exactKappaBlocker canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
  ≡
  missingUniformPositiveInfimumKappa
canonicalBTKappaExactBlocker =
  refl

canonicalBTKappaUniformInfimumFalse :
  uniformInfimumKappaPositive
    canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
  ≡
  false
canonicalBTKappaUniformInfimumFalse =
  refl

canonicalBTKappaContinuumTransferFalse :
  continuumTransferFromKappaFamily
    canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
  ≡
  false
canonicalBTKappaContinuumTransferFalse =
  refl

canonicalBTKappaClayYangMillsFalse :
  clayYangMillsPromotedField
    canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
  ≡
  false
canonicalBTKappaClayYangMillsFalse =
  refl

canonicalBTKappaTerminalFalse :
  terminalPromotionField canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
  ≡
  false
canonicalBTKappaTerminalFalse =
  refl
