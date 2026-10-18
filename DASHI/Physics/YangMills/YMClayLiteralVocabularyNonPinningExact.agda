module DASHI.Physics.YangMills.YMClayLiteralVocabularyNonPinningExact where

------------------------------------------------------------------------
-- DIAGNOSTIC: THE LITERAL CLAY VOCABULARY IS NOT YET PINNED
--
-- This module is NOT a claim about Yang-Mills.  It is a falsification test
-- for the statement used by the literal top-down closure cone.
--
-- LiteralYangMillsCarriers is a record of abstract Sets and
-- LiteralYangMillsSemantics a record of abstract predicates over them.
-- Consequently ClayYangMillsSolution (literalClayVocabulary Y) is a statement
-- relative to the carriers and semantics supplied by the caller.
--
-- The degenerate choice below makes every carrier the unit type, every
-- semantic predicate trivially true, and the mass gap zero.  The official
-- solution object is still inhabited.  Therefore the generic terminal
-- vocabulary is a conditional compiler target, not by itself a pinned
-- formalization of the Clay theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

trivialCarriers : Top.LiteralYangMillsCarriers
trivialCarriers = record
  { CompactSimpleGroup = ⊤
  ; Spacetime = ⊤
  ; Cutoff = ⊤
  ; FiniteMeasure = ⊤
  ; ContinuumMeasure = ⊤
  ; SchwingerFamily = ⊤
  ; Observable = ⊤
  ; Position = ⊤
  ; CurvaturePolynomial = ⊤
  ; LocalOperator = ⊤
  ; OPECoefficient = ⊤
  ; StressTensor = ⊤
  ; HilbertSpace = ⊤
  ; Hamiltonian = ⊤
  ; VacuumState = ⊤
  }

trivialSemantics : Top.LiteralYangMillsSemantics trivialCarriers
trivialSemantics = record
  { IsCompactSimple = λ _ → ⊤
  ; IsFourDimensionalEuclidean = λ _ → ⊤
  ; IsFiniteVolumeCutoffMeasure = λ _ _ _ → ⊤
  ; IsReflectionPositiveRegularization = λ _ _ _ → ⊤
  ; HasUltravioletYangMillsNormalization = λ _ _ → ⊤
  ; HasAsymptoticallyFreeScaleTrajectory = λ _ _ → ⊤
  ; IsGaugeInvariantObservable = λ _ → ⊤
  ; IsLocalObservable = λ _ _ → ⊤
  ; IsContinuumLimitOf = λ _ _ _ → ⊤
  ; SchwingerBelongsToMeasure = λ _ _ → ⊤
  ; IsNontrivialQuantumYangMills = λ _ _ _ → ⊤
  ; CurvatureOperatorCorrespondence = λ _ _ → ⊤
  ; IsGaugeInvariantLocalOperator = λ _ → ⊤
  ; IsLocalOperator = λ _ _ → ⊤
  ; IsPhysicalOPECoefficient = λ _ _ _ _ _ _ → ⊤
  ; IsPhysicalOPERemainder = λ _ _ _ _ _ _ → ⊤
  ; HasShortDistanceAsymptoticFreedom = λ _ _ → ⊤
  ; HasStressTensorAndOPE = λ _ _ _ → ⊤
  ; SatisfiesAcceptedWightmanOrOSAxioms = λ _ _ → ⊤
  ; IsReconstructedHilbertSpace = λ _ _ _ → ⊤
  ; IsPositiveSelfAdjointHamiltonian = λ _ _ → ⊤
  ; IsVacuumSectorAndPositiveEnergyComplement = λ _ _ _ → ⊤
  ; IsStrictlyPositiveFiniteMassGap = λ _ _ → ⊤
  ; GaugeSymmetryPreservedAlongConstruction = λ _ → ⊤
  ; LocalityPreservedAlongConstruction = λ _ → ⊤
  ; EuclideanCovariancePreservedAlongConstruction = λ _ → ⊤
  ; ReflectionPositivityPreservedAlongConstruction = λ _ → ⊤
  ; PositivityNormalizationPreservedAlongConstruction = λ _ → ⊤
  ; VolumeCutoffCompatibilityPreserved = λ _ → ⊤
  ; PhysicalScaleLowerBoundUniform = λ _ _ → ⊤
  ; NoSpectralPollutionBelowGap = λ _ _ _ → ⊤
  ; NontrivialityPreservedInLimit = λ _ _ → ⊤
  ; GapAndClusteringAreDerivedNotAssumed = λ _ → ⊤
  ; CompactSimpleParameterizationPreserved = ⊤
  }

trivialConstruction :
  Top.LiteralYangMillsConstruction trivialCarriers trivialSemantics
trivialConstruction = record
  { spacetime = tt
  ; finiteMeasure = λ _ _ → tt
  ; continuumMeasure = λ _ → tt
  ; schwinger = λ _ → tt
  ; localObservable = λ _ _ → tt
  ; curvatureOperator = λ _ _ → tt
  ; opeCoefficient = λ _ _ _ _ _ → tt
  ; opeRemainder = λ _ _ _ _ _ → 0ℚ
  ; stressTensor = λ _ → tt
  ; hilbertSpace = λ _ → tt
  ; hamiltonian = λ _ → tt
  ; vacuum = λ _ → tt
  ; massGap = λ _ → 0ℚ
  }

trivialPreconditions :
  ∀ requirement → Top.preconditionRequirement trivialConstruction requirement
trivialPreconditions Clay.compactSimpleGaugeGroupIndex = λ _ → tt
trivialPreconditions Clay.fourDimensionalEuclideanSpacetime = tt
trivialPreconditions Clay.gaugeInvariantLocalObservableFamily = λ _ _ → tt , tt
trivialPreconditions Clay.finiteVolumeCutoffMeasureFamily = λ _ _ → tt
trivialPreconditions Clay.reflectionPositiveRegularization = λ _ _ → tt
trivialPreconditions Clay.ultravioletYangMillsNormalization = λ _ → tt
trivialPreconditions Clay.asymptoticallyFreeScaleTrajectory = λ _ → tt
trivialPreconditions Clay.acceptedAxiomaticQFTTarget = λ _ → tt

trivialPostconditions :
  ∀ requirement → Top.postconditionRequirement trivialConstruction requirement
trivialPostconditions Clay.nontrivialQuantumYangMillsTheoryOnR4 =
  λ _ → tt , tt , tt
trivialPostconditions Clay.gaugeInvariantCurvatureOperatorCorrespondence =
  λ _ → tt , (λ _ → tt) , (λ _ _ → tt)
trivialPostconditions Clay.shortDistanceAsymptoticFreedomAgreement = λ _ → tt
trivialPostconditions Clay.stressTensorAndOperatorProductExpansion =
  λ _ → tt , (λ _ _ _ _ → tt) , (λ _ _ _ _ → tt)
trivialPostconditions Clay.acceptedWightmanOrOSStrengthAxioms = λ _ → tt
trivialPostconditions Clay.reconstructedPositiveSelfAdjointHamiltonian =
  λ _ → tt , tt
trivialPostconditions Clay.vacuumSectorAndPositiveEnergyComplement = λ _ → tt
trivialPostconditions Clay.strictlyPositiveFiniteMassGap = λ _ → tt
trivialPostconditions Clay.constructionForEveryCompactSimpleGaugeGroup =
  λ _ _ → tt

trivialInvariants :
  ∀ requirement → Top.invariantRequirement trivialConstruction requirement
trivialInvariants Clay.gaugeSymmetryPreserved = λ _ → tt
trivialInvariants Clay.localityPreserved = λ _ → tt
trivialInvariants Clay.euclideanCovariancePreserved = λ _ → tt
trivialInvariants Clay.reflectionPositivityPreserved = λ _ → tt
trivialInvariants Clay.measurePositivityAndNormalizationPreserved = λ _ → tt
trivialInvariants Clay.volumeAndCutoffCompatibilityPreserved = λ _ → tt
trivialInvariants Clay.physicalScaleLowerBoundUniform = λ _ → tt
trivialInvariants Clay.noSpectralPollutionBelowGap = λ _ → tt
trivialInvariants Clay.nontrivialityPreservedInTheLimit = λ _ → tt
trivialInvariants Clay.targetGapAndClusteringNotAssumedAsInputs = λ _ → tt
trivialInvariants Clay.compactSimpleGroupParameterizationPreserved = tt

trivialLiteralClayEvidence : Top.LiteralClayEvidence trivialConstruction
trivialLiteralClayEvidence = record
  { preconditions = trivialPreconditions
  ; postconditions = trivialPostconditions
  ; invariants = trivialInvariants
  }

vocabularyIsNotPinned :
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary trivialConstruction)
vocabularyIsNotPinned =
  Top.literalTopDownClaySolution trivialConstruction trivialLiteralClayEvidence
