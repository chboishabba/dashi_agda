module DASHI.Physics.YangMills.YangMillsClayProblemContractExact where

------------------------------------------------------------------------
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
-- Tadeusz Balaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- State the literal Clay-facing contract before any implementation-status
-- discussion.  The contract is deliberately stronger than a fixed-lattice gap,
-- a finite propagator, an all-beta fixed-spacing theorem, or a formal OS
-- interface.  A solution must construct, for every compact simple gauge group,
-- a nontrivial four-dimensional quantum Yang--Mills theory on R^4 satisfying an
-- accepted axiomatic QFT scheme, carrying the required gauge-invariant local
-- operators and short-distance asymptotically-free/OPE behaviour, and possessing
-- a strictly positive finite Hamiltonian spectral gap above the vacuum.
--
-- This module indexes the required preconditions, postconditions and invariants
-- and defines the type of a complete witness.  It supplies no inhabitant of that
-- type and therefore makes no Clay completion claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.List.Base using (length)

------------------------------------------------------------------------
-- Literal problem contract.
------------------------------------------------------------------------

data ClayPrecondition : Set where
  compactSimpleGaugeGroupIndex : ClayPrecondition
  fourDimensionalEuclideanSpacetime : ClayPrecondition
  gaugeInvariantLocalObservableFamily : ClayPrecondition
  finiteVolumeCutoffMeasureFamily : ClayPrecondition
  reflectionPositiveRegularization : ClayPrecondition
  ultravioletYangMillsNormalization : ClayPrecondition
  asymptoticallyFreeScaleTrajectory : ClayPrecondition
  acceptedAxiomaticQFTTarget : ClayPrecondition

data ClayPostcondition : Set where
  nontrivialQuantumYangMillsTheoryOnR4 : ClayPostcondition
  gaugeInvariantCurvatureOperatorCorrespondence : ClayPostcondition
  shortDistanceAsymptoticFreedomAgreement : ClayPostcondition
  stressTensorAndOperatorProductExpansion : ClayPostcondition
  acceptedWightmanOrOSStrengthAxioms : ClayPostcondition
  reconstructedPositiveSelfAdjointHamiltonian : ClayPostcondition
  vacuumSectorAndPositiveEnergyComplement : ClayPostcondition
  strictlyPositiveFiniteMassGap : ClayPostcondition
  constructionForEveryCompactSimpleGaugeGroup : ClayPostcondition

data ClayInvariant : Set where
  gaugeSymmetryPreserved : ClayInvariant
  localityPreserved : ClayInvariant
  euclideanCovariancePreserved : ClayInvariant
  reflectionPositivityPreserved : ClayInvariant
  measurePositivityAndNormalizationPreserved : ClayInvariant
  volumeAndCutoffCompatibilityPreserved : ClayInvariant
  physicalScaleLowerBoundUniform : ClayInvariant
  noSpectralPollutionBelowGap : ClayInvariant
  nontrivialityPreservedInTheLimit : ClayInvariant
  targetGapAndClusteringNotAssumedAsInputs : ClayInvariant
  compactSimpleGroupParameterizationPreserved : ClayInvariant

clayPreconditions : List ClayPrecondition
clayPreconditions =
  compactSimpleGaugeGroupIndex
  ∷ fourDimensionalEuclideanSpacetime
  ∷ gaugeInvariantLocalObservableFamily
  ∷ finiteVolumeCutoffMeasureFamily
  ∷ reflectionPositiveRegularization
  ∷ ultravioletYangMillsNormalization
  ∷ asymptoticallyFreeScaleTrajectory
  ∷ acceptedAxiomaticQFTTarget
  ∷ []

clayPostconditions : List ClayPostcondition
clayPostconditions =
  nontrivialQuantumYangMillsTheoryOnR4
  ∷ gaugeInvariantCurvatureOperatorCorrespondence
  ∷ shortDistanceAsymptoticFreedomAgreement
  ∷ stressTensorAndOperatorProductExpansion
  ∷ acceptedWightmanOrOSStrengthAxioms
  ∷ reconstructedPositiveSelfAdjointHamiltonian
  ∷ vacuumSectorAndPositiveEnergyComplement
  ∷ strictlyPositiveFiniteMassGap
  ∷ constructionForEveryCompactSimpleGaugeGroup
  ∷ []

clayInvariants : List ClayInvariant
clayInvariants =
  gaugeSymmetryPreserved
  ∷ localityPreserved
  ∷ euclideanCovariancePreserved
  ∷ reflectionPositivityPreserved
  ∷ measurePositivityAndNormalizationPreserved
  ∷ volumeAndCutoffCompatibilityPreserved
  ∷ physicalScaleLowerBoundUniform
  ∷ noSpectralPollutionBelowGap
  ∷ nontrivialityPreservedInTheLimit
  ∷ targetGapAndClusteringNotAssumedAsInputs
  ∷ compactSimpleGroupParameterizationPreserved
  ∷ []

clayPreconditionCountExact : length clayPreconditions ≡ 8
clayPreconditionCountExact = refl

clayPostconditionCountExact : length clayPostconditions ≡ 9
clayPostconditionCountExact = refl

clayInvariantCountExact : length clayInvariants ≡ 11
clayInvariantCountExact = refl

record ClayProblemVocabulary : Set₁ where
  field
    PreconditionWitness : ClayPrecondition → Set
    PostconditionWitness : ClayPostcondition → Set
    InvariantWitness : ClayInvariant → Set

open ClayProblemVocabulary public

record ClayYangMillsSolution
    (vocabulary : ClayProblemVocabulary) : Set₁ where
  field
    preconditions :
      ∀ requirement → PreconditionWitness vocabulary requirement
    postconditions :
      ∀ requirement → PostconditionWitness vocabulary requirement
    invariants :
      ∀ requirement → InvariantWitness vocabulary requirement

------------------------------------------------------------------------
-- Strength separation.  These constructors prevent accidental promotion of a
-- valuable intermediate theorem into the literal Clay conclusion.
------------------------------------------------------------------------

data YangMillsResultStrength : Set where
  finiteLatticeHessian : YangMillsResultStrength
  finiteBackgroundPropagator : YangMillsResultStrength
  fixedSpacingStrongCouplingClustering : YangMillsResultStrength
  allBetaPositiveLatticeGap : YangMillsResultStrength
  thermodynamicEuclideanMeasure : YangMillsResultStrength
  continuumOSSchwingerTheory : YangMillsResultStrength
  reconstructedSingleGroupMassGap : YangMillsResultStrength
  literalClayYangMillsConclusion : YangMillsResultStrength

finiteHessianIsNotClay :
  finiteLatticeHessian ≡ literalClayYangMillsConclusion → ⊥
finiteHessianIsNotClay ()

finitePropagatorIsNotClay :
  finiteBackgroundPropagator ≡ literalClayYangMillsConclusion → ⊥
finitePropagatorIsNotClay ()

fixedSpacingClusteringIsNotClay :
  fixedSpacingStrongCouplingClustering
  ≡ literalClayYangMillsConclusion → ⊥
fixedSpacingClusteringIsNotClay ()

allBetaLatticeGapIsNotClay :
  allBetaPositiveLatticeGap ≡ literalClayYangMillsConclusion → ⊥
allBetaLatticeGapIsNotClay ()

continuumOSAloneIsNotClay :
  continuumOSSchwingerTheory ≡ literalClayYangMillsConclusion → ⊥
continuumOSAloneIsNotClay ()

singleGroupGapIsNotAllGroupsClay :
  reconstructedSingleGroupMassGap
  ≡ literalClayYangMillsConclusion → ⊥
singleGroupGapIsNotAllGroupsClay ()

-- No canonical inhabitant of ClayYangMillsSolution is supplied.
