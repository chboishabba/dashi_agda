module DASHI.Physics.Closure.NSTriadKNLuoSubmissionLemmaCrosswalkExact where

------------------------------------------------------------------------
-- PURPOSE
-- Machine-readable crosswalk from the intended human manuscript to the exact
-- formal modules and declarations.  Status strings distinguish implemented
-- reducers from still-uninhabited physical analytic leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact as Audit

weightedIncrementEntry : Audit.ManuscriptFormalCrosswalkEntry
weightedIncrementEntry = record
  { manuscriptLemma = "Weighted periodic increment kernel Fourier identity"
  ; formalModule = "NSTriadKNLuoWeightedIncrementFourierIntegrationCutsetExact"
  ; formalDeclaration = "weightedIncrementKernelFourierFieldIdentity"
  ; dependencyBoundary = "spatial integral to finite convolution; finite convolution to exact multiplier"
  ; proofStatus = "reducer implemented; official physical primitive cutset uninhabited"
  }

threePairEntry : Audit.ManuscriptFormalCrosswalkEntry
threePairEntry = record
  { manuscriptLemma = "The r_p1, r_p2 and high-tail coefficient identifications"
  ; formalModule = "NSTriadKNLuoThreePairCoefficientCutsetExact"
  ; formalDeclaration = "threePairWholeFoldReceipt"
  ; dependencyBoundary = "three pointwise physical coefficient theorems on one mature pair carrier"
  ; proofStatus = "whole-fold transport implemented; three coefficient leaves uninhabited"
  }

multiplierEntry : Audit.ManuscriptFormalCrosswalkEntry
multiplierEntry = record
  { manuscriptLemma = "Uniform smooth/hard periodic multiplier comparison"
  ; formalModule = "NSTriadKNLuoMultiplierReceiptAndSourceSchurCutsetExact"
  ; formalDeclaration = "officialMultiplierRealizationFromFiniteReceipts"
  ; dependencyBoundary = "finite signed convolution receipts and shell-uniform kernel L1 theorem"
  ; proofStatus = "constructor implemented; concrete official receipts uninhabited"
  }

schurEntry : Audit.ManuscriptFormalCrosswalkEntry
schurEntry = record
  { manuscriptLemma = "Physical Luo flux estimate from the weighted Schur bridge"
  ; formalModule = "NSTriadKNLuoCanonicalSourceSchurIdentificationExact"
  ; formalDeclaration = "canonicalFluxKernelToWeightedSchur"
  ; dependencyBoundary = "flux, gradient, constant, scalar transport and source-energy domination"
  ; proofStatus = "constructor implemented; physical identification leaves uninhabited"
  }

equation42Entry : Audit.ManuscriptFormalCrosswalkEntry
equation42Entry = record
  { manuscriptLemma = "Physical shell-energy inequality and equation (4.2)"
  ; formalModule = "NSTriadKNLuoEquation42PhysicalIdentityAdapterExact"
  ; formalDeclaration = "equation42FinitePhysicalInputs"
  ; dependencyBoundary = "physical shell-energy inequality plus exact nonlinear RHS/fold identity"
  ; proofStatus = "adapter implemented; two physical PDE leaves uninhabited"
  }

section4Entry : Audit.ManuscriptFormalCrosswalkEntry
section4Entry = record
  { manuscriptLemma = "The four Section 4 dyadic estimates"
  ; formalModule = "NSTriadKNLuoSection4PhysicalBoundsAdapterExact"
  ; formalDeclaration = "section4ComponentBounds"
  ; dependencyBoundary = "J11 lower, J11 upper, J12 and J2 source bounds separately"
  ; proofStatus = "adapter implemented; four source bounds uninhabited"
  }

fixedShiftEntry : Audit.ManuscriptFormalCrosswalkEntry
fixedShiftEntry = record
  { manuscriptLemma = "Fixed-shift decay bootstrap"
  ; formalModule = "NSTriadKNLuoFixedShiftRecursionReductionExact"
  ; formalDeclaration = "fixedShiftRecursionFromIntegratedEnergy"
  ; dependencyBoundary = "integrated cutoff inequality and uniform correction comparison"
  ; proofStatus = "order reduction implemented; physical recursion/correction leaves uninhabited"
  }

continuationEntry : Audit.ManuscriptFormalCrosswalkEntry
continuationEntry = record
  { manuscriptLemma = "Continuation beyond the selected terminal time"
  ; formalModule = "NSTriadKNLuoCriticalPathCompositionExact"
  ; formalDeclaration = "criticalPathContinuation"
  ; dependencyBoundary = "one CanonicalAnalyticPhysicalLeaves inhabitant"
  ; proofStatus = "composition implemented; physical leaf package uninhabited"
  }

maximalTimeEntry : Audit.ManuscriptFormalCrosswalkEntry
maximalTimeEntry = record
  { manuscriptLemma = "Finite maximal-time contradiction"
  ; formalModule = "NSTriadKNLuoCriticalPathCompositionExact"
  ; formalDeclaration = "criticalPathContradictsSelectedFiniteMaximality"
  ; dependencyBoundary = "physical leaves plus selected-terminal maximality identification"
  ; proofStatus = "logical theorem implemented; arbitrary physical maximal-time identification uninhabited"
  }

finiteLimitEntry : Audit.ManuscriptFormalCrosswalkEntry
finiteLimitEntry = record
  { manuscriptLemma = "Pass finite Fourier estimates and identities to the physical limit"
  ; formalModule = "NSTriadKNLuoFiniteInfiniteRealPromotionExact"
  ; formalDeclaration = "uniformFiniteBoundPassesToLimit; uniformFiniteEqualityPassesToLimit"
  ; dependencyBoundary = "uniform finite results, convergence and closedness of order/equality"
  ; proofStatus = "limit reducers implemented; physical convergence cutsets uninhabited"
  }

submissionEntry : Audit.ManuscriptFormalCrosswalkEntry
submissionEntry = record
  { manuscriptLemma = "Periodic Navier--Stokes global regularity theorem"
  ; formalModule = "NSTriadKNPeriodicNavierStokesSubmissionTheoremExact"
  ; formalDeclaration = "periodicNavierStokesGlobalRegularity"
  ; dependencyBoundary = "global smooth velocity-pressure witness for every admissible datum"
  ; proofStatus = "exact theorem type implemented; global witness constructor uninhabited"
  }

auditEntry : Audit.ManuscriptFormalCrosswalkEntry
auditEntry = record
  { manuscriptLemma = "Assumption, circularity, source and reproducibility audit"
  ; formalModule = "NSTriadKNLuoSubmissionAuditReceiptExact"
  ; formalDeclaration = "completeSubmissionAuditReceipt"
  ; dependencyBoundary = "dependency inventory, no-circularity, source fidelity, crosswalk and clean build"
  ; proofStatus = "audit schema and source inventory implemented; completed audit receipt uninhabited"
  }

submissionLemmaCrosswalk : List Audit.ManuscriptFormalCrosswalkEntry
submissionLemmaCrosswalk =
  weightedIncrementEntry ∷
  threePairEntry ∷
  multiplierEntry ∷
  schurEntry ∷
  equation42Entry ∷
  section4Entry ∷
  fixedShiftEntry ∷
  continuationEntry ∷
  maximalTimeEntry ∷
  finiteLimitEntry ∷
  submissionEntry ∷
  auditEntry ∷
  []

submissionLemmaCrosswalkConstructed : Bool
submissionLemmaCrosswalkConstructed = true

submissionLemmaCrosswalkConstructedIsTrue :
  submissionLemmaCrosswalkConstructed ≡ true
submissionLemmaCrosswalkConstructedIsTrue = refl
