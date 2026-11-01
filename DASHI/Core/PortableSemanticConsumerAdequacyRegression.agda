module DASHI.Core.PortableSemanticConsumerAdequacyRegression where

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.PortableLoopInterpretationExact as Loop
import DASHI.Core.PortableSemanticConsumerAdequacyBridgeExact as Bridge

jsCandidateEligible :
  MDL.Eligible Bridge.loopBackendSelectionProblem Loop.jsSequential
jsCandidateEligible = Bridge.jsSequentialEligible

gpuCandidateEligible :
  MDL.Eligible Bridge.loopBackendSelectionProblem Loop.gpuParallel
gpuCandidateEligible = Bridge.gpuParallelEligible
