module DASHI.Economics.AIGeometricMarketStressOperator2026Exact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AICerebrasChinaOpenWeightCalibration2026Exact as Competitive
import DASHI.Interop.PNFSpectralFieldGraph as Spectral

------------------------------------------------------------------------
-- GEOMETRIC / SPECTRAL MARKET-STRESS INTERFACE
--
-- Financial entanglement and capability substitution are distinct geometries.
-- A later numeric/data owner must instantiate weights; qualitative evidence is
-- not silently promoted into fabricated eigenvalues or conductance numbers.
------------------------------------------------------------------------

record RepoSpectralBridge : Set where
  constructor repoSpectralBridge
  field
    laplacianOperator : Spectral.GraphLaplacianOperator

open RepoSpectralBridge public

record EntanglementStressObservables : Set₁ where
  field
    WeightedAdjacency : Set
    GraphLaplacian : Set
    CycleWeight : Set
    SpectralRadius : Set
    AlgebraicConnectivity : Set
    TerminalConductance : Set
    ConcentrationIndex : Set
    FundingSpread : Set

    weightedAdjacency : WeightedAdjacency
    graphLaplacian : GraphLaplacian
    cycleWeight : CycleWeight
    spectralRadius : SpectralRadius
    algebraicConnectivity : AlgebraicConnectivity
    terminalConductance : TerminalConductance
    concentrationIndex : ConcentrationIndex
    fundingSpread : FundingSpread

open EntanglementStressObservables public

record CapabilityCompressionObservables : Set₁ where
  field
    OpenClosedCapabilityDistance : Set
    OpenTokenShare : Set
    PricePerQualityUnit : Set
    LocalServingFeasibility : Set

    openClosedCapabilityDistance : OpenClosedCapabilityDistance
    openTokenShare : OpenTokenShare
    pricePerQualityUnit : PricePerQualityUnit
    localServingFeasibility : LocalServingFeasibility

open CapabilityCompressionObservables public

record JointCapitalRecoveryStress : Set₂ where
  field
    FinancialObservables : Set₁
    CapabilityObservables : Set₁
    financialObservables : FinancialObservables
    capabilityObservables : CapabilityObservables
    commercialRecoveryMargin : Set
    strategicBackstopDependence : Trit

open JointCapitalRecoveryStress public

record QualitativeJointStress : Set where
  constructor qualitativeJointStress
  field
    financialEntanglementHigh : Bool
    fundingHurdleHigh : Bool
    terminalConductanceWeak : Bool
    capabilityDistanceFalling : Bool
    openUsageRising : Bool
    proprietaryRentPressure : Bool
    policyBackstopSalienceRising : Bool

open QualitativeJointStress public

candidateOctober2026JointStress : QualitativeJointStress
candidateOctober2026JointStress =
  qualitativeJointStress true true true true true true true

data HighSpectralRadiusImpliesBubblePermission : Set where
data LowTerminalConductanceImpliesInsolvencyPermission : Set where
data HighEntanglementImpliesAntitrustLiabilityPermission : Set where
data PolicyBackstopSalienceImpliesCapturePermission : Set where

highSpectralRadiusDoesNotAutoProveBubble :
  HighSpectralRadiusImpliesBubblePermission → ⊥
highSpectralRadiusDoesNotAutoProveBubble ()

lowTerminalConductanceDoesNotAutoProveInsolvency :
  LowTerminalConductanceImpliesInsolvencyPermission → ⊥
lowTerminalConductanceDoesNotAutoProveInsolvency ()

highEntanglementDoesNotAutoProveAntitrustLiability :
  HighEntanglementImpliesAntitrustLiabilityPermission → ⊥
highEntanglementDoesNotAutoProveAntitrustLiability ()

policyBackstopSalienceDoesNotAutoProveCapture :
  PolicyBackstopSalienceImpliesCapturePermission → ⊥
policyBackstopSalienceDoesNotAutoProveCapture ()

capitalState : Capital.TwoGeometryCapitalRecoveryState
capitalState = Capital.candidateTwoGeometryState2026

competitiveState : Competitive.CompetitiveSubstitutionCoordinates
competitiveState = Competitive.candidateCompetitiveSubstitution2026
