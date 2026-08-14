module DASHI.Physics.YangMills.BalabanSelectedBackgroundLiteralPlaquetteFamilyProducerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- The pre-Round-46 correlated singleton object already contains the literal
-- raw plaquette extractor, the same Moore--Penrose normal solve, the selected
-- variation, stationarity, projected-variation identity and exact correlated
-- cancellation.  The new vertical LiteralSelectedPlaquetteWitness asks only
-- that its four owner estimates be carried with explicit unused slack.
--
-- This module proves the exact bridge.  It therefore shrinks G2 from
-- "reconstruct every field of LiteralSelectedPlaquetteWitness" to the genuinely
-- analytic/local task: produce the existing correlated physical singleton data
-- together with four owner inequalities whose coefficient total fits the
-- singleton allowance.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanSelectedOwnerBudgetSlackExact as Slack
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette

record CorrelatedSingletonWithSlack
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    extraction : Closure.CorrelatedSingletonExtractionData
      background bondField plaquette

    ownerBounds :
      Slack.CorrelatedOwnerBoundsWithSlack
        (Authority.canonicalCorrelatedResidualFamily
          (Closure.residualAuthority extraction))
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CorrelatedSingletonWithSlack public

correlatedSingletonWithSlackToLiteralWitness :
  ∀ {background bondField plaquette} →
  CorrelatedSingletonWithSlack background bondField plaquette →
  Plaquette.LiteralSelectedPlaquetteWitness background bondField plaquette
correlatedSingletonWithSlackToLiteralWitness witnessData = record
  { Multiplier =
      Closure.Multiplier (extraction witnessData)
  ; pseudoData =
      Closure.pseudoData (extraction witnessData)
  ; firstVariationCovector =
      Closure.firstVariationCovector (extraction witnessData)
  ; residualAuthority =
      Closure.residualAuthority (extraction witnessData)
  ; FineVariation =
      Closure.FineVariation (extraction witnessData)
  ; variation =
      Closure.variation (extraction witnessData)
  ; GaugeAdmissible =
      Closure.GaugeAdmissible (extraction witnessData)
  ; ConstraintTangent =
      Closure.ConstraintTangent (extraction witnessData)
  ; SupportedNearPlaquette =
      Closure.SupportedNearPlaquette (extraction witnessData)
  ; gaugeAdmissible =
      Closure.gaugeAdmissible (extraction witnessData)
  ; constraintTangent =
      Closure.constraintTangent (extraction witnessData)
  ; localSupport =
      Closure.localSupport (extraction witnessData)
  ; variationNormSq =
      Closure.variationNormSq (extraction witnessData)
  ; selectorConstant =
      Closure.selectorConstant (extraction witnessData)
  ; selectorConstantNonnegative =
      Closure.selectorConstantNonnegative (extraction witnessData)
  ; variationChargeBound =
      Closure.variationChargeBound (extraction witnessData)
  ; firstVariation =
      Closure.firstVariation (extraction witnessData)
  ; selectedEulerLagrangeStationary =
      Closure.selectedEulerLagrangeStationary (extraction witnessData)
  ; projectedVariationExact =
      Closure.projectedVariationExact (extraction witnessData)
  ; exactCancellation =
      Closure.exactCancellation (extraction witnessData)
  ; ownerBounds =
      ownerBounds witnessData
  }

record CorrelatedSingletonFamilyWithSlack
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      CorrelatedSingletonWithSlack background bondField plaquette

open CorrelatedSingletonFamilyWithSlack public

correlatedSingletonFamilyWithSlackToLiteralFamily :
  ∀ {background bondField} →
  CorrelatedSingletonFamilyWithSlack background bondField →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField
correlatedSingletonFamilyWithSlackToLiteralFamily family = record
  { atPlaquette = λ plaquette →
      correlatedSingletonWithSlackToLiteralWitness
        (atPlaquette family plaquette) }

selectedLiteralPlaquetteVerticalProducerLevel : ProofLevel
selectedLiteralPlaquetteVerticalProducerLevel = machineChecked

selectedLiteralPlaquetteLocalAnalyticInputLevel : ProofLevel
selectedLiteralPlaquetteLocalAnalyticInputLevel = conditional
