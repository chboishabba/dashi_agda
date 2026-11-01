module DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityParetoRegression where

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityParetoExact as Pareto

modelThreeExists : Pareto.OscillatorModel
modelThreeExists = Pareto.model3

modelSixExists : Pareto.OscillatorModel
modelSixExists = Pareto.model6

modelNineExists : Pareto.OscillatorModel
modelNineExists = Pareto.model9

paretoBoundaryExists : Pareto.OscillatorIdentifiabilityParetoBoundary
paretoBoundaryExists = Pareto.canonicalOscillatorIdentifiabilityParetoBoundary

problemSurface :
  Pareto.OscillatorParetoEvidence → MDL.ConsumerMDLProblem
problemSurface = Pareto.oscillatorConsumerMDLProblem

costSurface :
  (evidence : Pareto.OscillatorParetoEvidence) →
  MDL.CostHyperfabric (Pareto.oscillatorConsumerMDLProblem evidence)
costSurface = Pareto.oscillatorCostHyperfabric
