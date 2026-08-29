module DASHI.Reasoning.FiniteRelationLinearAlgebraProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy

------------------------------------------------------------------------
-- EXACT FINITE PRODUCERS FOR RELATION-REPRESENTATION EXPERIMENTS
--
-- MATHEMATICAL NEIGHBOURHOOD
-- Roger A. Horn and Charles R. Johnson,
-- Matrix Analysis, 2nd ed., Cambridge University Press, 2013.
-- DOI: 10.1017/CBO9781139020411.
--
-- SOURCE SCOPE
-- Horn--Johnson is background for matrix/eigenvalue/rank-one language.  The
-- tiny Nat-valued examples and producer interfaces below are DASHI finite
-- constructions.  They are not claimed to reproduce numerical SVD of an LLM.
--
-- The purpose is narrower: provide exact proof objects which a future external
-- embedding/activation pipeline can target after numerical computation.
------------------------------------------------------------------------

record Vec2 : Set where
  constructor vec2
  field
    x y : Nat

open Vec2 public

record Mat2 : Set where
  constructor mat2
  field
    a11 a12 a21 a22 : Nat

open Mat2 public

scaleVec : Nat → Vec2 → Vec2
scaleVec k (vec2 u v) = vec2 (k * u) (k * v)

matVec : Mat2 → Vec2 → Vec2
matVec (mat2 a b c d) (vec2 u v) =
  vec2 (a * u + b * v) (c * u + d * v)

dot : Vec2 → Vec2 → Nat
dot (vec2 a b) (vec2 c d) = a * c + b * d

------------------------------------------------------------------------
-- Spectral/eigenpair producer.
------------------------------------------------------------------------

record ExactEigenpair (matrix : Mat2) : Set where
  constructor exactEigenpair
  field
    vector : Vec2
    eigenvalue : Nat
    eigenEquation : matVec matrix vector ≡ scaleVec eigenvalue vector
    eigenReading : String

open ExactEigenpair public

-- Two exact residual samples: (3,0) and (0,1).  Their unnormalised X^T X is
-- diag(9,1), so the two coordinate directions are exact eigenvectors.

sampleResidualA : Vec2
sampleResidualA = vec2 3 0

sampleResidualB : Vec2
sampleResidualB = vec2 0 1

sampleGram : Mat2
sampleGram = mat2 9 0 0 1

principalAxis : Vec2
principalAxis = vec2 1 0

secondaryAxis : Vec2
secondaryAxis = vec2 0 1

principalEigenpair : ExactEigenpair sampleGram
principalEigenpair =
  exactEigenpair principalAxis 9 refl
    "Exact finite principal-axis witness for the 2x2 Gram specimen."

secondaryEigenpair : ExactEigenpair sampleGram
secondaryEigenpair =
  exactEigenpair secondaryAxis 1 refl
    "Exact finite secondary-axis witness for the 2x2 Gram specimen."

spectralGapCode : Nat
spectralGapCode = 9 ∸ 1

spectralGapCodeIsEight : spectralGapCode ≡ 8
spectralGapCodeIsEight = refl

record FiniteSpectralProducerReceipt : Set where
  constructor finiteSpectralProducerReceipt
  field
    gram : Mat2
    first : ExactEigenpair gram
    second : ExactEigenpair gram
    squaredPrincipalScale : Nat
    squaredSecondaryScale : Nat
    gapCode : Nat
    receiptReading : String

canonicalFiniteSpectralReceipt : FiniteSpectralProducerReceipt
canonicalFiniteSpectralReceipt =
  finiteSpectralProducerReceipt
    sampleGram
    principalEigenpair
    secondaryEigenpair
    9 1 8
    "Finite X^T X/eigenpair receipt.  Square roots/singular vectors over reals are not inferred from this Nat shadow."

------------------------------------------------------------------------
-- Exact rank-one outer-product producer.
------------------------------------------------------------------------

outer : Vec2 → Vec2 → Mat2
outer (vec2 a b) (vec2 c d) =
  mat2 (a * c) (a * d) (b * c) (b * d)

rankOneLeft : Vec2
rankOneLeft = vec2 2 3

rankOneRight : Vec2
rankOneRight = vec2 1 2

rankOneMatrix : Mat2
rankOneMatrix = mat2 2 4 3 6

rankOneOuterProductReceipt :
  outer rankOneLeft rankOneRight ≡ rankOneMatrix
rankOneOuterProductReceipt = refl

record ExactRankOneProducer : Set where
  constructor exactRankOneProducer
  field
    leftFactor rightFactor : Vec2
    producedMatrix : Mat2
    outerReceipt : outer leftFactor rightFactor ≡ producedMatrix
    rankOneReading : String

canonicalExactRankOneProducer : ExactRankOneProducer
canonicalExactRankOneProducer =
  exactRankOneProducer
    rankOneLeft rankOneRight rankOneMatrix refl
    "Exact finite outer-product producer; this is a rank-one construction, not a claim that an observed relation matrix is rank one."

-- Reuse the existing independent multiplicative-minor obstruction rather than
-- inventing another rank-one rejection calculus.

rankOneObstructionOwner :
  Interaction.RankOneMinorObstruction Interaction.mismatchSurface
rankOneObstructionOwner = Interaction.mismatchRankOneObstruction

------------------------------------------------------------------------
-- Exact finite rotation/operator producer.
--
-- We use a four-state oriented axis carrier so no signed arithmetic is smuggled
-- into Nat.  This is an exact order-four operator shadow, not a real orthogonal
-- matrix theorem.
------------------------------------------------------------------------

data AxisPhase4 : Set where
  axisX axisY axisNegX axisNegY : AxisPhase4

quarterTurn : AxisPhase4 → AxisPhase4
quarterTurn axisX = axisY
quarterTurn axisY = axisNegX
quarterTurn axisNegX = axisNegY
quarterTurn axisNegY = axisX

quarterTurnSquared : AxisPhase4 → AxisPhase4
quarterTurnSquared p = quarterTurn (quarterTurn p)

quarterTurnFourth : (p : AxisPhase4) →
  quarterTurn (quarterTurn (quarterTurn (quarterTurn p))) ≡ p
quarterTurnFourth axisX = refl
quarterTurnFourth axisY = refl
quarterTurnFourth axisNegX = refl
quarterTurnFourth axisNegY = refl

record ExactRotationProducer : Set where
  constructor exactRotationProducer
  field
    Carrier : Set
    rotate : Carrier → Carrier
    orderFour : (p : Carrier) → rotate (rotate (rotate (rotate p))) ≡ p
    family : Adequacy.TransformationFamily
    rotationReading : String

canonicalQuarterTurnProducer : ExactRotationProducer
canonicalQuarterTurnProducer =
  exactRotationProducer AxisPhase4 quarterTurn quarterTurnFourth
    Adequacy.linearRotation
    "Exact finite order-four rotation producer; no real inner-product orthogonality theorem is claimed."

------------------------------------------------------------------------
-- Exact affine producer over Nat^2.
------------------------------------------------------------------------

affineDemo : Vec2 → Vec2
affineDemo (vec2 u v) = vec2 (2 * u + 1) (3 * v + 2)

affineDemoAt23 : affineDemo (vec2 2 3) ≡ vec2 5 11
affineDemoAt23 = refl

record ExactAffineProducer : Set where
  constructor exactAffineProducer
  field
    transform : Vec2 → Vec2
    specimenInput specimenOutput : Vec2
    specimenReceipt : transform specimenInput ≡ specimenOutput
    family : Adequacy.TransformationFamily
    affineReading : String

canonicalAffineProducer : ExactAffineProducer
canonicalAffineProducer =
  exactAffineProducer affineDemo (vec2 2 3) (vec2 5 11) refl
    Adequacy.affineTransformation
    "Exact affine-map producer over a finite Nat specimen."

------------------------------------------------------------------------
-- Finite-difference local sensitivity / Jacobian surrogate.
--
-- This is intentionally not called a derivative.  It is the exact discrete
-- producer that can motivate a Jacobian obligation once a differentiable
-- representation carrier is supplied.
------------------------------------------------------------------------

squareMap : Nat → Nat
squareMap n = n * n

forwardDifference : (Nat → Nat) → Nat → Nat
forwardDifference f n = f (suc n) ∸ f n

squareDifferenceAt2 : forwardDifference squareMap 2 ≡ 5
squareDifferenceAt2 = refl

squareDifferenceAt3 : forwardDifference squareMap 3 ≡ 7
squareDifferenceAt3 = refl

localSensitivityChangesWithState :
  forwardDifference squareMap 2 ≡ forwardDifference squareMap 3 → ⊥
localSensitivityChangesWithState ()

record FiniteDifferenceSensitivityReceipt : Set where
  constructor finiteDifferenceSensitivityReceipt
  field
    map : Nat → Nat
    leftPoint rightPoint : Nat
    leftDifference rightDifference : Nat
    leftReceipt : forwardDifference map leftPoint ≡ leftDifference
    rightReceipt : forwardDifference map rightPoint ≡ rightDifference
    differencesDistinct : leftDifference ≡ rightDifference → ⊥
    sensitivityReading : String

canonicalFiniteDifferenceSensitivity : FiniteDifferenceSensitivityReceipt
canonicalFiniteDifferenceSensitivity =
  finiteDifferenceSensitivityReceipt
    squareMap 2 3 5 7 refl refl (λ ())
    "Local finite difference changes with state; this is evidence against a globally constant local response in the specimen, not a calculus/Jacobian theorem."

------------------------------------------------------------------------
-- Manifold admission remains explicitly separate.
------------------------------------------------------------------------

record ManifoldProducerObligation : Set where
  constructor manifoldProducerObligation
  field
    chartCarrierSupplied : Bool
    chartTransitionReceiptsSupplied : Bool
    localMetricOrGeodesicReceiptSupplied : Bool
    empiricalActivationCarrierIdentified : Bool
    obligationReading : String

emptyManifoldProducerObligation : ManifoldProducerObligation
emptyManifoldProducerObligation =
  manifoldProducerObligation false false false false
    "No smooth/manifold realization is manufactured by the finite linear-algebra producer; a future application must supply charts/transitions/geometry and identify them with the actual activation carrier."

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record FiniteRelationProducerBoundary : Set where
  constructor finiteRelationProducerBoundary
  field
    finiteEigenpairReceiptIsFullNumericalSVD : Bool
    finiteEigenpairReceiptIsFullNumericalSVDIsFalse :
      finiteEigenpairReceiptIsFullNumericalSVD ≡ false

    rankOneConstructionProvesObservedDataRankOne : Bool
    rankOneConstructionProvesObservedDataRankOneIsFalse :
      rankOneConstructionProvesObservedDataRankOne ≡ false

    orderFourFiniteRotationProvesRealOrthogonality : Bool
    orderFourFiniteRotationProvesRealOrthogonalityIsFalse :
      orderFourFiniteRotationProvesRealOrthogonality ≡ false

    finiteDifferenceIsJacobian : Bool
    finiteDifferenceIsJacobianIsFalse :
      finiteDifferenceIsJacobian ≡ false

    producerReceiptAutomaticallyRealizesSemantics : Bool
    producerReceiptAutomaticallyRealizesSemanticsIsFalse :
      producerReceiptAutomaticallyRealizesSemantics ≡ false

    externalNumericalReceiptCanTargetTheseInterfaces : Bool
    externalNumericalReceiptCanTargetTheseInterfacesIsTrue :
      externalNumericalReceiptCanTargetTheseInterfaces ≡ true

canonicalFiniteRelationProducerBoundary : FiniteRelationProducerBoundary
canonicalFiniteRelationProducerBoundary =
  finiteRelationProducerBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
