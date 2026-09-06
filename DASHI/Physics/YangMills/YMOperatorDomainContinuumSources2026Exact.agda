module DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Explicit sources for the operator-domain / continuum boundary exposed by
-- the September 2026 Lean return.  These sources calibrate theorem families;
-- they do not inhabit any physical Yang--Mills obligation by citation alone.
------------------------------------------------------------------------

record LiteratureSource : Set where
  constructor source
  field
    authors : String
    title : String
    venueYear : String
    stableIdentifier : String
    sectionTopic : String
    relationship : String

open LiteratureSource public

katoPerturbationTheory : LiteratureSource
katoPerturbationTheory = source
  "Tosio Kato"
  "Perturbation Theory for Linear Operators"
  "Classics in Mathematics, Springer, 1995 reprint of the second edition"
  "DOI 10.1007/978-3-642-66282-9"
  "closed operators; sesquilinear forms; convergence and perturbation of operators"
  "canonical functional-analytic calibration for replacing bounded-total-map transport by a domain/form-aware continuum theorem"

moscoVariationalConvergence : LiteratureSource
moscoVariationalConvergence = source
  "Umberto Mosco"
  "Convergence of Convex Sets and of Solutions of Variational Inequalities"
  "Advances in Mathematics 3 (1969), 510--585"
  "DOI 10.1016/0001-8708(69)90009-7"
  "variational convergence of convex sets/forms and convergence of solutions"
  "calibration source for a possible Mosco-form route; not evidence that the selected Yang--Mills forms satisfy its hypotheses"

osterwalderSchraderI : LiteratureSource
osterwalderSchraderI = source
  "Konrad Osterwalder and Robert Schrader"
  "Axioms for Euclidean Green's Functions"
  "Communications in Mathematical Physics 31 (1973), 83--112"
  "DOI 10.1007/BF01645738"
  "Euclidean axioms and reconstruction"
  "continuum reconstruction target; does not supply the finite-to-continuum Yang--Mills construction"

osterwalderSchraderII : LiteratureSource
osterwalderSchraderII = source
  "Konrad Osterwalder and Robert Schrader"
  "Axioms for Euclidean Green's Functions II"
  "Communications in Mathematical Physics 42 (1975), 281--305"
  "DOI 10.1007/BF01608978"
  "corrected reconstruction hypotheses"
  "continuum OS/Wightman boundary source; not an automatic promotion receipt"

operatorDomainContinuumSources : List LiteratureSource
operatorDomainContinuumSources =
  katoPerturbationTheory ∷
  moscoVariationalConvergence ∷
  osterwalderSchraderI ∷
  osterwalderSchraderII ∷ []

------------------------------------------------------------------------
-- Exact source identity for the checked sibling Lean tranche.
------------------------------------------------------------------------

record LeanSourceArtifact : Set where
  constructor lean-source-artifact
  field
    project : String
    path : String
    stableIdentifier : String

open LeanSourceArtifact public

generatorUniquenessLean : LeanSourceArtifact
generatorUniquenessLean = lean-source-artifact
  "RequestProject / attached Aristotle Lean project"
  "RequestProject/YangMills/GeneratorUniquenessCore.lean"
  "YangMills.generator_unique_of_evolution_eq"

physicalNullQuotientLean : LeanSourceArtifact
physicalNullQuotientLean = lean-source-artifact
  "RequestProject / attached Aristotle Lean project"
  "RequestProject/YangMills/PhysicalNullQuotient.lean"
  "RequestProject.YangMills.PhysicalNullQuotient.preservesNull_of_isSymmetricOp"

gaugeInvariantCarrierLean : LeanSourceArtifact
gaugeInvariantCarrierLean = lean-source-artifact
  "RequestProject / attached Aristotle Lean project"
  "RequestProject/YangMills/GaugeInvariantL2Carrier.lean"
  "RequestProject.YangMills.GaugeInvariantL2Carrier.hamiltonian_eqOn_core_of_same_evolution"

gaugeInvariantWitnessLean : LeanSourceArtifact
gaugeInvariantWitnessLean = lean-source-artifact
  "RequestProject / attached Aristotle Lean project"
  "RequestProject/YangMills/GaugeInvariantCarrierWitness.lean"
  "RequestProject.YangMills.GaugeInvariantCarrierWitness.physicalCarrier_nontrivial"

massGapFormTransportLean : LeanSourceArtifact
massGapFormTransportLean = lean-source-artifact
  "RequestProject / attached Aristotle Lean project"
  "RequestProject/YangMills/MassGapFormTransport.lean"
  "RequestProject.YangMills.MassGapFormTransport.hasFormGap_of_tendsto_of_gap_tendsto"
