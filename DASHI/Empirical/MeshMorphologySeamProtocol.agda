module DASHI.Empirical.MeshMorphologySeamProtocol where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Empirical.MeshMorphologyCalibration
open import DASHI.Empirical.SeamABExperiment

-- O,R,C,S,L,P,G,F specialization for the mesh-morphology/seam problem.
--
-- O : observed mesh artifacts
-- R : human-labelled morphology calibration + bidirectional seam requirement
-- C : barycentric radial-mass measurement and A/B transfer computations
-- S : current classifications and directional metrics
-- L : fail-closed evidence lattice
-- P : accepted protocol result
-- G : gap obligations
-- F : promotion gate

record ObservedArtifacts (Mesh : Set) : Set where
  field
    baseMesh : Mesh
    romMesh : Mesh

record Requirements (Mesh : Set) : Set where
  field
    calibration : HumanCalibration Mesh
    runBothDirections : ABExperiment Direction

record Computation
       (Mesh Point Signature Metric : Set) : Set₁ where
  field
    radialModel : BarycentricRadialMassModel Mesh Point Signature
    compareToCalibration : HumanCalibration Mesh → Mesh → Comparison
    seamExperiment : ABExperiment Metric

record State (Mesh Metric : Set) : Set where
  field
    baseMorphology : Classification
    romMorphology : Classification
    seamMetrics : ABExperiment Metric

-- Evidence is intentionally small and fail-closed. There is no constructor
-- which licenses a guessed morphology or a one-direction-only experiment.
data Evidence : Set where
  calibrated-two-exemplar : Evidence
  radial-comparison-explicit : Evidence
  both-seam-directions-present : Evidence
  unresolved-returned-to-human : Evidence

data Gap : Set where
  missing-human-exemplar : Gap
  missing-ogre-exemplar : Gap
  missing-radial-comparison : Gap
  missing-strategy-A : Gap
  missing-strategy-B : Gap
  unresolved-morphology : Gap

data Promotion : Set where
  accepted needs-more-evidence : Promotion

record ProtocolResult (Mesh Metric : Set) : Set where
  field
    state : State Mesh Metric
    morphologyEvidence : Evidence
    seamEvidence : Evidence
    promotion : Promotion

-- The promotion gate is explicit: both morphology classifications must have
-- non-unresolved comparison evidence and both A/B results must already exist in
-- the experiment carrier.
promote :
  {Mesh Metric : Set} →
  (baseComparison romComparison : Comparison) →
  ABExperiment Metric →
  Promotion
promote nearer-human nearer-human experiment = accepted
promote nearer-human nearer-ogre experiment = accepted
promote nearer-ogre nearer-human experiment = accepted
promote nearer-ogre nearer-ogre experiment = accepted
promote unresolved romComparison experiment = needs-more-evidence
promote baseComparison unresolved experiment = needs-more-evidence

unresolvedBaseFailsClosed :
  {Metric : Set} →
  (romComparison : Comparison) →
  (experiment : ABExperiment Metric) →
  promote unresolved romComparison experiment ≡ needs-more-evidence
unresolvedBaseFailsClosed romComparison experiment = refl

unresolvedRomFailsClosed :
  {Metric : Set} →
  (baseComparison : Comparison) →
  (experiment : ABExperiment Metric) →
  promote baseComparison unresolved experiment ≡ needs-more-evidence
unresolvedRomFailsClosed baseComparison experiment = refl
