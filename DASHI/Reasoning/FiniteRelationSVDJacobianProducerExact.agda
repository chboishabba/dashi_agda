module DASHI.Reasoning.FiniteRelationSVDJacobianProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.FiniteRelationLinearAlgebraProducerExact as Finite
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy

------------------------------------------------------------------------
-- EXACT TINY SVD PRODUCER
--
-- Mathematical background:
-- Roger A. Horn and Charles R. Johnson,
-- Matrix Analysis, 2nd ed., Cambridge University Press, 2013.
-- DOI: 10.1017/CBO9781139020411.
--
-- This is a literal 2x2 diagonal SVD receipt.  It is intentionally much
-- narrower than a generic SVD algorithm and is not an empirical LLM result.
------------------------------------------------------------------------

sampleDataMatrix : Finite.Mat2
sampleDataMatrix = Finite.mat2 3 0 0 1

record ExactSVD2 (matrix : Finite.Mat2) : Set where
  constructor exactSVD2
  field
    leftAxis1 leftAxis2 : Finite.Vec2
    rightAxis1 rightAxis2 : Finite.Vec2
    singularScale1 singularScale2 : Nat
    leftAxesOrthogonal : Finite.dot leftAxis1 leftAxis2 ≡ 0
    rightAxesOrthogonal : Finite.dot rightAxis1 rightAxis2 ≡ 0
    firstSingularEquation :
      Finite.matVec matrix rightAxis1
      ≡ Finite.scaleVec singularScale1 leftAxis1
    secondSingularEquation :
      Finite.matVec matrix rightAxis2
      ≡ Finite.scaleVec singularScale2 leftAxis2
    svdReading : String

open ExactSVD2 public

canonicalSampleSVD : ExactSVD2 sampleDataMatrix
canonicalSampleSVD =
  exactSVD2
    Finite.principalAxis
    Finite.secondaryAxis
    Finite.principalAxis
    Finite.secondaryAxis
    3 1
    refl refl refl refl
    "Exact SVD of diag(3,1): U and V are the coordinate axes and the singular scales are 3 and 1."

principalSingularScaleSquaresToGramEigenvalue :
  singularScale1 canonicalSampleSVD * singularScale1 canonicalSampleSVD ≡ 9
principalSingularScaleSquaresToGramEigenvalue = refl

secondarySingularScaleSquaresToGramEigenvalue :
  singularScale2 canonicalSampleSVD * singularScale2 canonicalSampleSVD ≡ 1
secondarySingularScaleSquaresToGramEigenvalue = refl

principalSVDActionReceipt :
  Finite.matVec sampleDataMatrix Finite.principalAxis
  ≡ Finite.scaleVec 3 Finite.principalAxis
principalSVDActionReceipt = firstSingularEquation canonicalSampleSVD

secondarySVDActionReceipt :
  Finite.matVec sampleDataMatrix Finite.secondaryAxis
  ≡ Finite.scaleVec 1 Finite.secondaryAxis
secondarySVDActionReceipt = secondSingularEquation canonicalSampleSVD

------------------------------------------------------------------------
-- EXTERNAL NUMERICAL RECEIPT CONTRACT
--
-- The focused Python producer recomputes a committed JSON fixture.  This Agda
-- object records the exact intended import surface.  It does not parse JSON;
-- the repository checker is the executable equality gate between computation
-- and the committed fixture, while the Agda regression owns the mathematical
-- equalities above.
------------------------------------------------------------------------

record ExternalNumericalReceiptContract : Set where
  constructor externalNumericalReceiptContract
  field
    schema : String
    fixturePath : String
    gramAndEigenpairsRecomputed : Bool
    rotationFitRecomputed : Bool
    affineFitRecomputed : Bool
    finiteDifferenceRecomputed : Bool
    empiricalEmbeddingsLoaded : Bool
    relationSemanticsRealized : Bool
    receiptReading : String

canonicalExternalNumericalReceiptContract : ExternalNumericalReceiptContract
canonicalExternalNumericalReceiptContract =
  externalNumericalReceiptContract
    "dashi.relation-representation.numeric-producer.v1"
    "Artifacts/relation-representation/numeric-producer-receipt.json"
    true true true true false false
    "Executable deterministic fixture receipt. Real embedding/activation arrays and target-domain realization remain later producers."

------------------------------------------------------------------------
-- JACOBIAN ADMISSION
--
-- A finite difference can motivate local-sensitivity testing, but a Jacobian
-- needs substantially more structure.  We keep those obligations explicit.
------------------------------------------------------------------------

record JacobianProducerObligation : Set where
  constructor jacobianProducerObligation
  field
    differentiableCarrierSupplied : Bool
    scalarFieldOrNormedSpaceSupplied : Bool
    perturbationCoordinatesSupplied : Bool
    derivativeExistenceReceiptSupplied : Bool
    derivativeMatrixReceiptSupplied : Bool
    empiricalActivationCarrierIdentified : Bool
    jacobianReading : String

emptyJacobianProducerObligation : JacobianProducerObligation
emptyJacobianProducerObligation =
  jacobianProducerObligation
    false false false false false false
    "The current finite-difference witness is not promoted to a Jacobian; a future real/constructive differentiable carrier must discharge every listed obligation."

finiteDifferencePreJacobianWitness :
  Finite.forwardDifference Finite.squareMap 2
  ≡ Finite.forwardDifference Finite.squareMap 3 → ⊥
finiteDifferencePreJacobianWitness =
  Finite.localSensitivityChangesWithState

------------------------------------------------------------------------
-- Producer-family mapping.
------------------------------------------------------------------------

svdCandidateFamily : Adequacy.TransformationFamily
svdCandidateFamily = Adequacy.quotientCompression

rotationCandidateFamily : Adequacy.TransformationFamily
rotationCandidateFamily = Adequacy.linearRotation

affineCandidateFamily : Adequacy.TransformationFamily
affineCandidateFamily = Adequacy.affineTransformation

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SVDJacobianProducerBoundary : Set where
  constructor svdJacobianProducerBoundary
  field
    exactTinySVDIsGenericSVDAlgorithm : Bool
    exactTinySVDIsGenericSVDAlgorithmIsFalse :
      exactTinySVDIsGenericSVDAlgorithm ≡ false

    numericalFixtureIsEmpiricalEmbeddingExperiment : Bool
    numericalFixtureIsEmpiricalEmbeddingExperimentIsFalse :
      numericalFixtureIsEmpiricalEmbeddingExperiment ≡ false

    finiteDifferenceAutomaticallySuppliesJacobian : Bool
    finiteDifferenceAutomaticallySuppliesJacobianIsFalse :
      finiteDifferenceAutomaticallySuppliesJacobian ≡ false

    singularAxisAutomaticallyRealizesSemanticEssence : Bool
    singularAxisAutomaticallyRealizesSemanticEssenceIsFalse :
      singularAxisAutomaticallyRealizesSemanticEssence ≡ false

    exactProducerCanBeConsumedByRelationProtocol : Bool
    exactProducerCanBeConsumedByRelationProtocolIsTrue :
      exactProducerCanBeConsumedByRelationProtocol ≡ true

canonicalSVDJacobianProducerBoundary : SVDJacobianProducerBoundary
canonicalSVDJacobianProducerBoundary =
  svdJacobianProducerBoundary false refl false refl false refl false refl true refl
