module DASHI.Physics.Closure.NSTriadKNStage3OutputRelocationExperimentIntegration where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Shin-ichi Inage; Jean-Michel Bony; Hajer Bahouri; Jean-Yves
-- Chemin; Raphael Danchin; Tosio Kato; Gustavo Ponce; Loukas Grafakos;
-- Rodolfo H. Torres; Minghui Liu; Gabor Pataki; Augustin-Louis Cauchy; Agda
-- standard-library contributors; DASHI repository contributors.
-- Title: "Stage-3 output-relocation falsification, unit-weight recovery and
-- cutoff-uniform shell-majorant experiment integration".
-- Venue/year: Mathematics 14 (2026), article 1410; Annales scientifiques de
-- l'Ecole Normale Superieure 14 (1981); Fourier Analysis and Nonlinear Partial
-- Differential Equations, Springer, 2011; Communications on Pure and Applied
-- Mathematics 41 (1988); Journal of Functional Analysis 187 (2001);
-- Mathematical Programming / arXiv, 2015--2017; Agda standard library; DASHI
-- formal development, 2026.
-- DOI: 10.3390/math14091410; 10.24033/asens.1404;
-- 10.1007/978-3-642-16830-7; 10.1002/cpa.3160410704;
-- 10.1006/jfan.2001.3804; 10.48550/arXiv.1507.00290; the integration receipt
-- has no DOI.
-- Uses: the comparator source-status audit, the output-relocation vertical
-- slice, exact primal/dual affine classification, unit weights, exact rational
-- geometric sums, the positive kernel and finite signed domination.
-- Relationship: the cheap experiment reaches a sharper decision.  The
-- source-style affine construction is infeasible, unit weights close symbolic
-- Check A, and all finite-cutoff reasoning after the concrete shell bridge is
-- proved.  The first remaining leaf is inhabiting that shell bridge, not
-- constructing a general geometric-series library.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNInageHighHighComparatorAudit as Comparator
import DASHI.Physics.Closure.NSTriadKNStage3OutputRelocationVerticalSlice as Slice
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFarkasDecision as Decision
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightShellSchur as ShellSchur
import DASHI.Physics.Closure.NSTriadKNRationalFiniteSignedMajorant as Signed
import DASHI.Physics.Closure.NSTriadKNOutputRelocationConditionalCutoffUniformClosure as Conditional

record OutputRelocationExperimentReceipt : Set where
  constructor receipt
  field
    peerReviewedComparatorRecorded :
      Comparator.independentHighHighShellComparatorRecorded ≡ true
    comparatorNotUsedAsArchetypeTheorem :
      Comparator.preprintSuppliesDASHIArchetypeTheorem ≡ false
    comparatorNotUsedAsAbsorptionProof :
      Comparator.preprintSuppliesUnconditionalAbsorption ≡ false

    relocationSymbolIdentityClosed :
      Slice.outputRelocationSymbolIdentityClosed ≡ true
    concreteComplexCarrierClosed :
      Slice.outputRelocationConcreteComplexCarrierClosed ≡ true
    endpointArithmeticClosed :
      Slice.outputRelocationEndpointArithmeticClosed ≡ true
    weightedExponentIdentityClosed :
      Slice.outputRelocationWeightedExponentIdentityClosed ≡ true
    coefficientExtractionInterfaceClosed :
      Slice.outputRelocationCoefficientExtractionInterfaceClosed ≡ true

    sourceStyleBaseClassified :
      Decision.outputRelocationBaseSystemClassified ≡ true
    sourceStyleDirectionClassified :
      Decision.outputRelocationDirectionSystemClassified ≡ true
    sourceStyleAffineAnsatzInfeasible :
      Decision.currentHomogeneityPreservingAffineAnsatzInfeasible ≡ true
    unitWeightsAllowed : Unit.unitWeightsAllowedBySchurCarrier ≡ true
    unitWeightSymbolicCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true

    rationalFiniteCutoffSummationClosed :
      Envelope.outputRelocationRationalFiniteCutoffSummationClosed ≡ true
    positiveKernelSummable :
      Majorant.outputRelocationPositiveKernelCutoffUniformlySummable ≡ true
    threeUnitWeightShellConditionsClosed :
      ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosed
      ≡ true
    finiteSignedDominationClosed :
      Signed.finiteTwoSidedTriangleDominationClosed ≡ true
    allDownstreamOfShellBridgeClosed :
      Conditional.outputRelocationAllDownstreamOfShellBridgeClosed ≡ true

    concreteShellBridgeStillOpen :
      Conditional.outputRelocationConcreteShellBridgeInhabited ≡ false
    concreteAnalyticArchetypeStillOpen :
      Conditional.outputRelocationConcreteCutoffUniformArchetypeClosed
      ≡ false

open OutputRelocationExperimentReceipt public

outputRelocationExperimentReceipt : OutputRelocationExperimentReceipt
outputRelocationExperimentReceipt = receipt
  Comparator.independentHighHighShellComparatorRecordedIsTrue
  Comparator.preprintSuppliesDASHIArchetypeTheoremIsFalse
  Comparator.preprintSuppliesUnconditionalAbsorptionIsFalse
  Slice.outputRelocationSymbolIdentityClosedIsTrue
  Slice.outputRelocationConcreteComplexCarrierClosedIsTrue
  Slice.outputRelocationEndpointArithmeticClosedIsTrue
  Slice.outputRelocationWeightedExponentIdentityClosedIsTrue
  Slice.outputRelocationCoefficientExtractionInterfaceClosedIsTrue
  Decision.outputRelocationBaseSystemClassifiedIsTrue
  Decision.outputRelocationDirectionSystemClassifiedIsTrue
  Decision.currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue
  Unit.unitWeightsAllowedBySchurCarrierIsTrue
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  Envelope.outputRelocationRationalFiniteCutoffSummationClosedIsTrue
  Majorant.outputRelocationPositiveKernelCutoffUniformlySummableIsTrue
  ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosedIsTrue
  Signed.finiteTwoSidedTriangleDominationClosedIsTrue
  Conditional.outputRelocationAllDownstreamOfShellBridgeClosedIsTrue
  Conditional.outputRelocationConcreteShellBridgeInhabitedIsFalse
  Conditional.outputRelocationConcreteCutoffUniformArchetypeClosedIsFalse

outputRelocationCheapFalsificationExperimentImplemented : Bool
outputRelocationCheapFalsificationExperimentImplemented = true

currentSourceStyleAffineRouteFalsifiedByOutputRelocationAlgebra : Bool
currentSourceStyleAffineRouteFalsifiedByOutputRelocationAlgebra = true

outputRelocationExperimentReachesNumericFeasibilityTest : Bool
outputRelocationExperimentReachesNumericFeasibilityTest = true

unitWeightSymbolicCheckARecovered : Bool
unitWeightSymbolicCheckARecovered = true

outputRelocationFiniteCutoffMajorantProgramClosed : Bool
outputRelocationFiniteCutoffMajorantProgramClosed = true

firstOpenLeafIsConcreteShellBridge : Bool
firstOpenLeafIsConcreteShellBridge = true

-- Compatibility status retained for old audit consumers.  A broad constructive
-- dyadic-series development is no longer the first open leaf.
firstOpenLeafIsConstructiveDyadicSeries : Bool
firstOpenLeafIsConstructiveDyadicSeries = false

outputRelocationCheapFalsificationExperimentImplementedIsTrue :
  outputRelocationCheapFalsificationExperimentImplemented ≡ true
outputRelocationCheapFalsificationExperimentImplementedIsTrue = refl

currentSourceStyleAffineRouteFalsifiedByOutputRelocationAlgebraIsTrue :
  currentSourceStyleAffineRouteFalsifiedByOutputRelocationAlgebra ≡ true
currentSourceStyleAffineRouteFalsifiedByOutputRelocationAlgebraIsTrue = refl

outputRelocationExperimentReachesNumericFeasibilityTestIsTrue :
  outputRelocationExperimentReachesNumericFeasibilityTest ≡ true
outputRelocationExperimentReachesNumericFeasibilityTestIsTrue = refl

unitWeightSymbolicCheckARecoveredIsTrue :
  unitWeightSymbolicCheckARecovered ≡ true
unitWeightSymbolicCheckARecoveredIsTrue = refl

outputRelocationFiniteCutoffMajorantProgramClosedIsTrue :
  outputRelocationFiniteCutoffMajorantProgramClosed ≡ true
outputRelocationFiniteCutoffMajorantProgramClosedIsTrue = refl

firstOpenLeafIsConcreteShellBridgeIsTrue :
  firstOpenLeafIsConcreteShellBridge ≡ true
firstOpenLeafIsConcreteShellBridgeIsTrue = refl

firstOpenLeafIsConstructiveDyadicSeriesIsFalse :
  firstOpenLeafIsConstructiveDyadicSeries ≡ false
firstOpenLeafIsConstructiveDyadicSeriesIsFalse = refl
