module DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact where

------------------------------------------------------------------------
-- ROUND67: LITERAL TOP-DOWN CLAY CONSTRUCTION
--
-- PRIMARY SOURCES
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Stop choosing an implementation cutset first and then trying to argue that
-- its 10/11 leaves imply Clay.  Instead construct the literal mathematical
-- object demanded at the endpoint and let the official Clay requirements
-- determine, by type checking, exactly what evidence is still missing.
--
-- There is deliberately:
--
--   * no leaf count;
--   * no package count;
--   * no abstract `AllCompactSimpleContinuumYM : Set`;
--   * no final `identifyLiteralClaySolution` hypothesis.
--
-- A single `LiteralYangMillsConstruction` carries the SAME all-group finite-
-- cutoff family, continuum Schwinger object, local operators/OPE/stress tensor,
-- reconstructed Hilbert/Hamiltonian/vacuum data and explicit mass scale.
-- The official Clay vocabulary is then DEFINITIONALLY induced by that object.
-- A `LiteralClayEvidence` inhabits those exact requirement types, and
-- `literalTopDownClaySolution` constructs `ClayYangMillsSolution` by direct
-- pattern matching on the official precondition/postcondition/invariant enums.
--
-- Consequently future work should compile BACKWARDS from any uninhabited field
-- of `LiteralClayEvidence`; numerical "frontier counts" are at most generated
-- diagnostics and are not proof architecture.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay

------------------------------------------------------------------------
-- Literal carriers.  These are mathematical carriers, not theorem-package
-- placeholders.
------------------------------------------------------------------------

record LiteralYangMillsCarriers : Set₁ where
  field
    CompactSimpleGroup : Set
    Spacetime : Set
    Cutoff : Set
    FiniteMeasure : Set
    ContinuumMeasure : Set
    SchwingerFamily : Set
    Observable : Set
    Position : Set
    CurvaturePolynomial : Set
    LocalOperator : Set
    OPECoefficient : Set
    StressTensor : Set
    HilbertSpace : Set
    Hamiltonian : Set
    VacuumState : Set

open LiteralYangMillsCarriers public

------------------------------------------------------------------------
-- Semantic predicates attached to the SAME carriers.  Domain-specific source
-- modules instantiate these predicates with their literal notions; they are not
-- allowed to replace the carriers by unrelated witnesses downstream.
------------------------------------------------------------------------

record LiteralYangMillsSemantics (C : LiteralYangMillsCarriers) : Set₁ where
  field
    IsCompactSimple : CompactSimpleGroup C → Set
    IsFourDimensionalEuclidean : Spacetime C → Set

    IsFiniteVolumeCutoffMeasure :
      CompactSimpleGroup C → Cutoff C → FiniteMeasure C → Set
    IsReflectionPositiveRegularization :
      CompactSimpleGroup C → Cutoff C → FiniteMeasure C → Set
    HasUltravioletYangMillsNormalization :
      CompactSimpleGroup C → (Cutoff C → FiniteMeasure C) → Set
    HasAsymptoticallyFreeScaleTrajectory :
      CompactSimpleGroup C → (Cutoff C → FiniteMeasure C) → Set

    IsGaugeInvariantObservable : Observable C → Set
    IsLocalObservable : Observable C → Position C → Set

    IsContinuumLimitOf :
      CompactSimpleGroup C →
      (Cutoff C → FiniteMeasure C) → ContinuumMeasure C → Set
    SchwingerBelongsToMeasure :
      ContinuumMeasure C → SchwingerFamily C → Set
    IsNontrivialQuantumYangMills :
      CompactSimpleGroup C → ContinuumMeasure C → SchwingerFamily C → Set

    CurvatureOperatorCorrespondence :
      CompactSimpleGroup C →
      (CurvaturePolynomial C → LocalOperator C) → Set
    IsGaugeInvariantLocalOperator : LocalOperator C → Set

    IsPhysicalOPECoefficient :
      CompactSimpleGroup C →
      LocalOperator C → LocalOperator C → LocalOperator C →
      Position C → OPECoefficient C → Set
    IsPhysicalOPERemainder :
      CompactSimpleGroup C →
      LocalOperator C → LocalOperator C → Position C → Nat → ℚ → Set
    HasShortDistanceAsymptoticFreedom :
      CompactSimpleGroup C → SchwingerFamily C → Set
    HasStressTensorAndOPE :
      CompactSimpleGroup C →
      SchwingerFamily C → StressTensor C → Set

    SatisfiesAcceptedWightmanOrOSAxioms :
      CompactSimpleGroup C → SchwingerFamily C → Set
    IsReconstructedHilbertSpace :
      CompactSimpleGroup C → SchwingerFamily C → HilbertSpace C → Set
    IsPositiveSelfAdjointHamiltonian :
      HilbertSpace C → Hamiltonian C → Set
    IsVacuumSectorAndPositiveEnergyComplement :
      HilbertSpace C → Hamiltonian C → VacuumState C → Set
    IsStrictlyPositiveFiniteMassGap : Hamiltonian C → ℚ → Set

    GaugeSymmetryPreservedAlongConstruction :
      CompactSimpleGroup C → Set
    LocalityPreservedAlongConstruction :
      CompactSimpleGroup C → Set
    EuclideanCovariancePreservedAlongConstruction :
      CompactSimpleGroup C → Set
    ReflectionPositivityPreservedAlongConstruction :
      CompactSimpleGroup C → Set
    PositivityNormalizationPreservedAlongConstruction :
      CompactSimpleGroup C → Set
    VolumeCutoffCompatibilityPreserved :
      CompactSimpleGroup C → Set
    PhysicalScaleLowerBoundUniform :
      CompactSimpleGroup C → ℚ → Set
    NoSpectralPollutionBelowGap :
      CompactSimpleGroup C → Hamiltonian C → ℚ → Set
    NontrivialityPreservedInLimit :
      CompactSimpleGroup C → ContinuumMeasure C → Set
    GapAndClusteringAreDerivedNotAssumed :
      CompactSimpleGroup C → Set
    CompactSimpleParameterizationPreserved : Set

open LiteralYangMillsSemantics public

------------------------------------------------------------------------
-- One literal all-group construction object.
------------------------------------------------------------------------

record LiteralYangMillsConstruction
    (C : LiteralYangMillsCarriers)
    (S : LiteralYangMillsSemantics C) : Set₁ where
  field
    spacetime : Spacetime C

    finiteMeasure :
      CompactSimpleGroup C → Cutoff C → FiniteMeasure C
    continuumMeasure :
      CompactSimpleGroup C → ContinuumMeasure C
    schwinger :
      CompactSimpleGroup C → SchwingerFamily C

    localObservable :
      CompactSimpleGroup C → Position C → Observable C
    curvatureOperator :
      CompactSimpleGroup C → CurvaturePolynomial C → LocalOperator C

    opeCoefficient :
      CompactSimpleGroup C →
      LocalOperator C → LocalOperator C → LocalOperator C →
      Position C → OPECoefficient C
    opeRemainder :
      CompactSimpleGroup C →
      LocalOperator C → LocalOperator C → Position C → Nat → ℚ

    stressTensor : CompactSimpleGroup C → StressTensor C
    hilbertSpace : CompactSimpleGroup C → HilbertSpace C
    hamiltonian : CompactSimpleGroup C → Hamiltonian C
    vacuum : CompactSimpleGroup C → VacuumState C
    massGap : CompactSimpleGroup C → ℚ

open LiteralYangMillsConstruction public

------------------------------------------------------------------------
-- The OFFICIAL Clay requirement types induced by this literal object.
------------------------------------------------------------------------

preconditionRequirement :
  ∀ {C S} →
  (Y : LiteralYangMillsConstruction C S) →
  Clay.ClayPrecondition → Set
preconditionRequirement {C} {S} Y Clay.compactSimpleGaugeGroupIndex =
  ∀ G → IsCompactSimple S G
preconditionRequirement {C} {S} Y Clay.fourDimensionalEuclideanSpacetime =
  IsFourDimensionalEuclidean S (spacetime Y)
preconditionRequirement {C} {S} Y Clay.gaugeInvariantLocalObservableFamily =
  ∀ G position →
  IsGaugeInvariantObservable S (localObservable Y G position)
preconditionRequirement {C} {S} Y Clay.finiteVolumeCutoffMeasureFamily =
  ∀ G cutoff → IsFiniteVolumeCutoffMeasure S G cutoff (finiteMeasure Y G cutoff)
preconditionRequirement {C} {S} Y Clay.reflectionPositiveRegularization =
  ∀ G cutoff →
  IsReflectionPositiveRegularization S G cutoff (finiteMeasure Y G cutoff)
preconditionRequirement {C} {S} Y Clay.ultravioletYangMillsNormalization =
  ∀ G → HasUltravioletYangMillsNormalization S G (finiteMeasure Y G)
preconditionRequirement {C} {S} Y Clay.asymptoticallyFreeScaleTrajectory =
  ∀ G → HasAsymptoticallyFreeScaleTrajectory S G (finiteMeasure Y G)
preconditionRequirement {C} {S} Y Clay.acceptedAxiomaticQFTTarget =
  ∀ G → SatisfiesAcceptedWightmanOrOSAxioms S G (schwinger Y G)

postconditionRequirement :
  ∀ {C S} →
  (Y : LiteralYangMillsConstruction C S) →
  Clay.ClayPostcondition → Set
postconditionRequirement {S = S} Y Clay.nontrivialQuantumYangMillsTheoryOnR4 =
  ∀ G → IsNontrivialQuantumYangMills S G (continuumMeasure Y G) (schwinger Y G)
postconditionRequirement {S = S} Y Clay.gaugeInvariantCurvatureOperatorCorrespondence =
  ∀ G → CurvatureOperatorCorrespondence S G (curvatureOperator Y G)
postconditionRequirement {S = S} Y Clay.shortDistanceAsymptoticFreedomAgreement =
  ∀ G → HasShortDistanceAsymptoticFreedom S G (schwinger Y G)
postconditionRequirement {S = S} Y Clay.stressTensorAndOperatorProductExpansion =
  ∀ G → HasStressTensorAndOPE S G (schwinger Y G) (stressTensor Y G)
postconditionRequirement {S = S} Y Clay.acceptedWightmanOrOSStrengthAxioms =
  ∀ G → SatisfiesAcceptedWightmanOrOSAxioms S G (schwinger Y G)
postconditionRequirement {S = S} Y Clay.reconstructedPositiveSelfAdjointHamiltonian =
  ∀ G →
  IsReconstructedHilbertSpace S G (schwinger Y G) (hilbertSpace Y G)
  × IsPositiveSelfAdjointHamiltonian S (hilbertSpace Y G) (hamiltonian Y G)
postconditionRequirement {S = S} Y Clay.vacuumSectorAndPositiveEnergyComplement =
  ∀ G →
  IsVacuumSectorAndPositiveEnergyComplement S
    (hilbertSpace Y G) (hamiltonian Y G) (vacuum Y G)
postconditionRequirement {S = S} Y Clay.strictlyPositiveFiniteMassGap =
  ∀ G → IsStrictlyPositiveFiniteMassGap S (hamiltonian Y G) (massGap Y G)
postconditionRequirement {S = S} Y Clay.constructionForEveryCompactSimpleGaugeGroup =
  ∀ G →
  IsCompactSimple S G →
  IsContinuumLimitOf S G (finiteMeasure Y G) (continuumMeasure Y G)

invariantRequirement :
  ∀ {C S} →
  (Y : LiteralYangMillsConstruction C S) →
  Clay.ClayInvariant → Set
invariantRequirement {S = S} Y Clay.gaugeSymmetryPreserved =
  ∀ G → GaugeSymmetryPreservedAlongConstruction S G
invariantRequirement {S = S} Y Clay.localityPreserved =
  ∀ G → LocalityPreservedAlongConstruction S G
invariantRequirement {S = S} Y Clay.euclideanCovariancePreserved =
  ∀ G → EuclideanCovariancePreservedAlongConstruction S G
invariantRequirement {S = S} Y Clay.reflectionPositivityPreserved =
  ∀ G → ReflectionPositivityPreservedAlongConstruction S G
invariantRequirement {S = S} Y Clay.measurePositivityAndNormalizationPreserved =
  ∀ G → PositivityNormalizationPreservedAlongConstruction S G
invariantRequirement {S = S} Y Clay.volumeAndCutoffCompatibilityPreserved =
  ∀ G → VolumeCutoffCompatibilityPreserved S G
invariantRequirement {S = S} Y Clay.physicalScaleLowerBoundUniform =
  ∀ G → PhysicalScaleLowerBoundUniform S G (massGap Y G)
invariantRequirement {S = S} Y Clay.noSpectralPollutionBelowGap =
  ∀ G → NoSpectralPollutionBelowGap S G (hamiltonian Y G) (massGap Y G)
invariantRequirement {S = S} Y Clay.nontrivialityPreservedInTheLimit =
  ∀ G → NontrivialityPreservedInLimit S G (continuumMeasure Y G)
invariantRequirement {S = S} Y Clay.targetGapAndClusteringNotAssumedAsInputs =
  ∀ G → GapAndClusteringAreDerivedNotAssumed S G
invariantRequirement {S = S} Y Clay.compactSimpleGroupParameterizationPreserved =
  CompactSimpleParameterizationPreserved S

------------------------------------------------------------------------
-- Literal evidence: these are now the ONLY top-level holes.  They are indexed
-- by the official Clay requirements and mention the same concrete construction
-- object definitionally.
------------------------------------------------------------------------

record LiteralClayEvidence
    {C : LiteralYangMillsCarriers}
    {S : LiteralYangMillsSemantics C}
    (Y : LiteralYangMillsConstruction C S) : Set₁ where
  field
    preconditions :
      ∀ requirement → preconditionRequirement Y requirement
    postconditions :
      ∀ requirement → postconditionRequirement Y requirement
    invariants :
      ∀ requirement → invariantRequirement Y requirement

open LiteralClayEvidence public

literalClayVocabulary :
  ∀ {C S} → LiteralYangMillsConstruction C S → Clay.ClayProblemVocabulary
literalClayVocabulary Y = record
  { Clay.ClayProblemVocabulary.PreconditionWitness = preconditionRequirement Y
  ; Clay.ClayProblemVocabulary.PostconditionWitness = postconditionRequirement Y
  ; Clay.ClayProblemVocabulary.InvariantWitness = invariantRequirement Y
  }

-- No abstract endpoint identification remains: the official Clay solution is
-- constructed directly from evidence about the literal object.
literalTopDownClaySolution :
  ∀ {C S} (Y : LiteralYangMillsConstruction C S) →
  LiteralClayEvidence Y →
  Clay.ClayYangMillsSolution (literalClayVocabulary Y)
literalTopDownClaySolution Y evidence = record
  { Clay.ClayYangMillsSolution.preconditions = preconditions evidence
  ; Clay.ClayYangMillsSolution.postconditions = postconditions evidence
  ; Clay.ClayYangMillsSolution.invariants = invariants evidence
  }
