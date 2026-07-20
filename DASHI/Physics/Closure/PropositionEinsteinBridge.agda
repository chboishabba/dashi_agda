module DASHI.Physics.Closure.PropositionEinsteinBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Geometry.LorentzianLeviCivitaConditional as LorentzConditional
import DASHI.Physics.Closure.EinsteinHilbertVariationConditional as EHConditional
import DASHI.Physics.Closure.StressEnergyBianchiConditional as SourceConditional
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Closure.TypedStressEnergyMassBridge as Source
import DASHI.Physics.Closure.FiniteQuantumGRFlatModel as FlatQGR

open import DASHI.Unified.GRQuantumProofTerms

------------------------------------------------------------------------
-- Proposition-level discrete valuation -> Einstein pipeline.
--
-- The finite flat producer below is fully inhabited by existing exact receipts.
-- The general pipeline is a theorem contract whose analytic, variational, and
-- continuum fields must be supplied as proof terms.  No Boolean flag promotes
-- the scalar congestion proxy into a tensor equation.

record ValuationMetricSelection : Set₁ where
  field
    DiscreteValuation : Set
    Metric : Set
    selectMetric : DiscreteValuation → Metric
    selectionRespectsGauge : Set
    selectedMetricNondegenerate : Set
    selectedMetricLorentzian13 : Set
open ValuationMetricSelection public

record DiscreteCurvaturePipeline
  (selection : ValuationMetricSelection) : Set₁ where
  open ValuationMetricSelection selection
  field
    Connection Riemann Ricci ScalarCurvature EinsteinTensor : Set
    leviCivita : Metric → Connection
    riemann : Connection → Riemann
    ricci : Riemann → Ricci
    scalarCurvature : Metric → Ricci → ScalarCurvature
    einsteinTensor : Metric → Ricci → ScalarCurvature → EinsteinTensor

    leviCivitaExistence : Set
    leviCivitaUniqueness : Set
    discreteConnectionConverges : Set
    discreteRiemannConverges : Set
    discreteRicciConverges : Set
    scalarProxyIsTraceLimit : Set
    contractedBianchiIdentity : Set
open DiscreteCurvaturePipeline public

record VariationalEinsteinSource
  (selection : ValuationMetricSelection)
  (curvature : DiscreteCurvaturePipeline selection) : Set₁ where
  open ValuationMetricSelection selection
  open DiscreteCurvaturePipeline curvature
  field
    MatterState StressEnergy Action : Set
    matterAction : MatterState → Action
    stressEnergy : MatterState → StressEnergy

    einsteinHilbertBasisFromLovelockHypotheses : Set
    metricVariationProducesEinsteinTensor : Set
    matterVariationProducesStressEnergy : Set
    diffeomorphismNoetherIdentity : Set
    stressEnergyCovariantlyConserved : Set
    universalCoupling : Set
    spinTwoSelfCouplingBootstrap : Set
    sourceEquationFromOneVariationPrinciple : Set
    backgroundIndependent : Set
open VariationalEinsteinSource public

record GeneralValuationEinsteinClosure : Set₁ where
  field
    metricSelection : ValuationMetricSelection
    curvaturePipeline : DiscreteCurvaturePipeline metricSelection
    variationalSource :
      VariationalEinsteinSource metricSelection curvaturePipeline
    terminalEinsteinProof : EinsteinTensorProof
open GeneralValuationEinsteinClosure public

------------------------------------------------------------------------
-- Existing exact finite producer.

record ExactFlatEinsteinProducer : Set where
  constructor exact-flat-einstein-producer
  field
    lorentzianMetric : Flat.FlatLorentzianMetricReceipt
    leviCivita : Flat.FlatLeviCivitaReceipt
    symbolicLeadingBasis : EH.EHLeadingBasisReceipt
    symbolicVariation : EH.SymbolicEHVariationReceipt
    flatVacuumEinstein : EH.FlatVacuumEinsteinReceipt
    flatBianchiStress : Source.FlatBianchiStressReceipt
    zeroMassIdentification :
      Source.MassIdentificationWitness Source.zeroDefectEnergy
    finiteQuantumGRInterface : FlatQGR.FlatQuantumGRInterfaceReceipt
    scope : String
open ExactFlatEinsteinProducer public

canonicalExactFlatEinsteinProducer : ExactFlatEinsteinProducer
canonicalExactFlatEinsteinProducer =
  exact-flat-einstein-producer
    Flat.flatLorentzianMetricReceipt
    Flat.flatLeviCivitaReceipt
    EH.symbolicEHLeadingBasisReceipt
    EH.symbolicEHVariationReceipt
    EH.flatVacuumEinsteinReceipt
    Source.flatBianchiStressReceipt
    Source.zeroMassIdentificationWitness
    FlatQGR.flatQuantumGRInterfaceReceipt
    "exact finite flat/zero-source producer; not the general continuum Einstein theorem"

------------------------------------------------------------------------
-- Conditional authority adapters already present in the repository.

record ExistingConditionalEinsteinAdapters : Set where
  constructor existing-conditional-einstein-adapters
  field
    lorentzianReceipt :
      LorentzConditional.LorentzianMetricReceipt
        LorentzConditional.canonicalConditionalLorentzianWitness
    leviCivitaReceipt :
      LorentzConditional.LeviCivitaReceipt
        LorentzConditional.canonicalConditionalLorentzianWitness
        LorentzConditional.canonicalConditionalLorentzianReceipt
        LorentzConditional.canonicalConditionalConnection
    einsteinHilbertBasisReceipt :
      EHConditional.EinsteinHilbertBasisReceipt
        EHConditional.canonicalConditionalEHBasis
    einsteinEquationReceipt :
      EHConditional.EinsteinEquationReceipt
        EHConditional.canonicalConditionalEHBasis
        EHConditional.canonicalConditionalEHBasisReceipt
        EHConditional.canonicalConditionalEHVariation
    sourceBoundary : SourceConditional.MassIdentificationBoundary
open ExistingConditionalEinsteinAdapters public

canonicalExistingConditionalEinsteinAdapters :
  ExistingConditionalEinsteinAdapters
canonicalExistingConditionalEinsteinAdapters =
  existing-conditional-einstein-adapters
    Flat.conditionalLorentzianReceipt
    Flat.conditionalLeviCivitaReceipt
    EH.conditionalBasisReceipt
    EH.conditionalEinsteinEquationReceipt
    SourceConditional.canonicalMassIdentificationBoundary

propositionEinsteinBoundaryText : String
propositionEinsteinBoundaryText =
  "The repository now has exact flat Lorentzian, zero-connection, zero-Ricci, zero-source, symbolic EH-variation, and finite quantum/GR interface proofs.  General metric selection, discrete-to-continuum tensor convergence, general Bianchi, nonzero source variation, and spin-two bootstrap remain explicit proposition-valued obligations."
