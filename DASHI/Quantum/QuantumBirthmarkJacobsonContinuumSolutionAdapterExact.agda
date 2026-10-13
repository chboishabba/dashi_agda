{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonContinuumSolutionAdapterExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary as EMS
import DASHI.Quantum.QuantumBirthmarkJacobsonPhysicalTerminalCompilerBoundaryExact as Terminal

------------------------------------------------------------------------
-- The repo already has the correct continuum target.  Do not introduce a
-- second Jacobson-specific notion of a continuum Einstein-matter solution.
--
-- Native Lean supplies a terminal conditional equation on one selected domain.
-- To promote that result into DASHI's existing continuum schema, a physical
-- model must instantiate the existing EMS carrier and identify its metric,
-- matter, Einstein/stress tensors, domain, regularity and Bianchi/divergence
-- data with the same objects consumed by the Jacobson package.
------------------------------------------------------------------------

record ContinuumJacobsonAttachmentObligations : Set where
  constructor continuumJacobsonAttachmentObligations
  field
    metricFieldSameObject : Bool
    matterFieldSameObject : Bool
    einsteinTensorSameObject : Bool
    stressTensorSameObject : Bool
    declaredDomainSameObject : Bool
    LorentzianSignaturePaid : Bool
    smoothOrControlledRegularityPaid : Bool
    initialOrBoundaryDataPaid : Bool
    contractedBianchiPaid : Bool
    divergenceTransportPaid : Bool

-- No canonical physical inhabitant is fabricated.

continuumSolutionSchemaReused : Bool
continuumSolutionSchemaReused = true

terminalConditionalEinsteinCompilerAvailable : Bool
terminalConditionalEinsteinCompilerAvailable =
  Terminal.terminalConditionalEinsteinCompilerSourceWritten

noSecondContinuumSolutionFormalismRequired : Bool
noSecondContinuumSolutionFormalismRequired = true

physicalInstantiationStillRequired : Bool
physicalInstantiationStillRequired = true

-- Once an actual existing-schema solution is supplied, conservation is already
-- an owned theorem; Jacobson does not need a parallel conservation formalism.
matterConservationAlreadyOwned :
  (S : EMS.ContinuumEinsteinMatterSystem) →
  (solution : EMS.ContinuumSolutionData S) →
  (p : EMS.Point S) →
  (b : EMS.Index S) →
  EMS.DivergenceStress S (EMS.matter solution) (EMS.metric solution) p b
    ≡ EMS.zero S
matterConservationAlreadyOwned = EMS.matterConservationFromEinsteinAndBianchi

statusStatement : String
statusStatement =
  "The terminal Jacobson compiler must instantiate the existing ContinuumEinsteinMatterSolutionBoundary rather than a parallel GR schema. The remaining attachment is same-object physical identification of metric/matter/tensors/domain plus regularity, Bianchi and divergence transport. Once a ContinuumSolutionData inhabitant is supplied, matter conservation is already derived by existing repo machinery."
