module DASHI.Biology.Physical.PhysicalDevelopmentalOperatorSystemExact where

------------------------------------------------------------------------
-- Cumulative physical-development operator.
--
-- The point is not to replace chemistry, continuum mechanics, bioelectricity,
-- DNA, or PNF with one ontology.  The module composes their already-declared
-- owners into a single state transition whose factorization is explicit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.FiniteReactionDiffusionConservationExact as RD
import DASHI.Biology.Physical.ElectrochemicalMembranePowerExact as Power
import DASHI.Biology.Physical.MechanochemicalMorphogenesisSIExact as Mech
import DASHI.Biology.Physical.DevelopmentalGoalFactorizationExact as Goal
import DASHI.Biology.Physical.DevelopmentalHiddenStateFutureDefectExact as Future
import DASHI.Biology.Physical.SIBioelectricNetworkAdapterExact as BioSI
import DASHI.Biology.Physical.PadicPhysicalParameterProjectionExact as Padic
import DASHI.Biology.Physical.PhysicalOriginsLadderExact as Origins
import DASHI.Biology.Physical.CellBrainTransducerBridgeExact as CellBrain
import DASHI.Biology.DNACompiledOperatorsRegression as DNA
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Biology.AgenticMaterialsControlCore as Agentic
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as ChemistryWave

xor : Bool → Bool → Bool
xor false false = false
xor false true = true
xor true false = true
xor true true = false

record PhysicalDevelopmentalState : Set where
  constructor physicalDevelopmentalState
  field
    chemicalInventory : Nat
    epigeneticState : Bool
    regulatoryState : Bool
    electricalState : Bool
    metabolicReserve : Nat
    mechanicalState : Bool
    morphology : Bool
    targetGoal : Goal.DevelopmentalGoal

open PhysicalDevelopmentalState public

regulatoryOperator : Bool → PhysicalDevelopmentalState → PhysicalDevelopmentalState
regulatoryOperator genome x = record x
  { regulatoryState = xor genome (epigeneticState x) }

electricalOperator : PhysicalDevelopmentalState → PhysicalDevelopmentalState
electricalOperator x = record x
  { electricalState = xor (regulatoryState x) (electricalState x) }

mechanicalOperator : PhysicalDevelopmentalState → PhysicalDevelopmentalState
mechanicalOperator x = record x
  { mechanicalState = xor (electricalState x) (mechanicalState x) }

morphologyOperator : PhysicalDevelopmentalState → PhysicalDevelopmentalState
morphologyOperator x = record x
  { morphology = mechanicalState x }

chemicalSourceOperator : Nat → PhysicalDevelopmentalState → PhysicalDevelopmentalState
chemicalSourceOperator q x = record x
  { chemicalInventory = q + chemicalInventory x }

physicalDevelopmentalStep :
  Bool → Nat → PhysicalDevelopmentalState → PhysicalDevelopmentalState
physicalDevelopmentalStep genome source x =
  morphologyOperator
    (mechanicalOperator
      (electricalOperator
        (regulatoryOperator genome
          (chemicalSourceOperator source x))))

physicalDevelopmentalStepFactorises :
  (genome : Bool) (source : Nat) (x : PhysicalDevelopmentalState) →
  physicalDevelopmentalStep genome source x ≡
  morphologyOperator
    (mechanicalOperator
      (electricalOperator
        (regulatoryOperator genome
          (chemicalSourceOperator source x))))
physicalDevelopmentalStepFactorises genome source x = refl

chemicalSourceSurvivesDownstreamOperators :
  (genome : Bool) (source : Nat) (x : PhysicalDevelopmentalState) →
  chemicalInventory (physicalDevelopmentalStep genome source x)
    ≡ source + chemicalInventory x
chemicalSourceSurvivesDownstreamOperators genome source x = refl

------------------------------------------------------------------------
-- The physical carrier exposes more state than morphology alone; the imported
-- Future theorem proves that dropping hidden control can be dynamically unsafe.
------------------------------------------------------------------------

morphologyOnlyFutureSafetyFails :
  Future.Dynamic.DynamicConsumerSafety
    Future.developmentalSystem Future.morphologyProjection → ⊥
morphologyOnlyFutureSafetyFails = Future.morphologyProjectionCannotBeDynamicallySafe

------------------------------------------------------------------------
-- Cumulative owner bundle.  These fields are concrete theorem-bearing owners,
-- not Boolean receipts.
------------------------------------------------------------------------

record PhysicalDevelopmentalOwners : Set₁ where
  field
    reactionDiffusionSI : RD.ReactionDiffusionSISignature
    membranePowerSI : Power.MembranePowerSISignature
    tissueMechanicsSI : Mech.TissueMechanicsSISignature
    bioelectricSINetwork : BioSI.Bioelectric.BioelectricNetwork
    originSeparation : Origins.PhysicalOriginSeparation
    cellNetworkTransducer : CellBrain.Multiplex.StatefulTransducer

open PhysicalDevelopmentalOwners public

canonicalPhysicalDevelopmentalOwners : PhysicalDevelopmentalOwners
canonicalPhysicalDevelopmentalOwners = record
  { reactionDiffusionSI = RD.canonicalReactionDiffusionSISignature
  ; membranePowerSI = Power.canonicalMembranePowerSISignature
  ; tissueMechanicsSI = Mech.canonicalTissueMechanicsSISignature
  ; bioelectricSINetwork = BioSI.canonicalSIBioelectricNetwork
  ; originSeparation = Origins.canonicalPhysicalOriginSeparation
  ; cellNetworkTransducer = CellBrain.canonicalBioelectricTransducer
  }
