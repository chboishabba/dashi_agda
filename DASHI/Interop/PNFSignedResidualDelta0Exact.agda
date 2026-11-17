module DASHI.Interop.PNFSignedResidualDelta0Exact where

------------------------------------------------------------------------
-- LITERAL SIGNED-RESIDUAL Delta_0 ON THE CANONICAL PNF TRIANGLE
--
-- Source vocabulary:
--   Fan R. K. Chung, "Spectral Graph Theory", CBMS 92, AMS (1997),
--   DOI 10.1090/cbms/092.
--
-- Repository-specific contribution:
--   PNFHodgeResidualTopology already fixes the canonical oriented triangle
--
--      0 --partial(+1)--> 1 --noTypedMeet(+3)--> 2
--      ^                                          |
--      |------------- contradiction(-9) ----------|
--
-- where the magnitudes 1,3,9 and the negative contradiction sign come from
-- the existing residual-severity/signed-weight constructors.
--
-- Here we instantiate the literal signed-weight incidence operator
--
--                    Delta_0 = B^T W B
--
-- with W = diag(1,3,-9).  This is deliberately called a signed-*weight*
-- realization: it should not be conflated with conventions in signed-graph
-- theory that absorb edge signs into an incidence matrix while retaining
-- nonnegative edge magnitudes.
--
-- The resulting integer operator is exact and indefinite on the zero-sum
-- sector: one explicit zero-sum field has energy -2 and another has energy +4.
-- This closes the old "unsigned C3 != full signed residual Delta0" boundary
-- with a concrete producer, while still granting no continuum/Hodge authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Interop.PNFHodgeResidualTopology as Hodge
import DASHI.Interop.PNFSpectralFieldGraph as Graph
import DASHI.Interop.PNFTernaryCycleSpectralExact as Unsigned
import DASHI.Interop.SensibLawResidualLattice as Residual

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; ⊝_; solve)

------------------------------------------------------------------------
-- The weights are not free parameters: expose the existing canonical data.
------------------------------------------------------------------------

edge01IsPartial :
  Hodge.residualLevel Hodge.canonicalResidualOneCell ≡ Residual.partial
edge01IsPartial = refl

edge12IsNoTypedMeet :
  Hodge.residualLevel Hodge.canonicalTransportOneCell ≡ Residual.noTypedMeet
edge12IsNoTypedMeet = refl

edge20IsContradiction :
  Hodge.residualLevel Hodge.canonicalContradictionOneCell ≡ Residual.contradiction
edge20IsContradiction = refl

edge01SignPositive :
  Graph.sign (Hodge.graphWeight Hodge.canonicalResidualOneCell)
  ≡ Graph.positiveWeight
edge01SignPositive = refl

edge12SignPositive :
  Graph.sign (Hodge.graphWeight Hodge.canonicalTransportOneCell)
  ≡ Graph.positiveWeight
edge12SignPositive = refl

edge20SignNegative :
  Graph.sign (Hodge.graphWeight Hodge.canonicalContradictionOneCell)
  ≡ Graph.negativeResidualWeight
edge20SignNegative = refl

edge01MagnitudeIsOne :
  Graph.magnitude (Hodge.graphWeight Hodge.canonicalResidualOneCell) ≡ 1
edge01MagnitudeIsOne = Graph.partialResidualWeightSeverityIsOne

edge12MagnitudeIsThree :
  Graph.magnitude (Hodge.graphWeight Hodge.canonicalTransportOneCell) ≡ 3
edge12MagnitudeIsThree = Graph.noTypedMeetResidualWeightSeverityIsThree

edge20MagnitudeIsNine :
  Graph.magnitude (Hodge.graphWeight Hodge.canonicalContradictionOneCell) ≡ 9
edge20MagnitudeIsNine = Graph.contradictionResidualWeightSeverityIsNine

------------------------------------------------------------------------
-- Integer field and literal B^T W B operator.
--
-- With oriented incidence rows
--   b01=(-1,1,0), b12=(0,-1,1), b20=(1,0,-1)
-- and W=diag(1,3,-9), matrix multiplication gives
--
--   [ -8  -1   9 ]
--   [ -1   4  -3 ]
--   [  9  -3  -6 ].
------------------------------------------------------------------------

record TriangleField : Set where
  constructor triangleField
  field
    value0 value1 value2 : ℤ

open TriangleField public

zeroField : TriangleField
zeroField = triangleField (+ 0) (+ 0) (+ 0)

constantField : ℤ → TriangleField
constantField x = triangleField x x x

signedResidualDelta0 : TriangleField → TriangleField
signedResidualDelta0 field =
  triangleField
    (((- (+ 8)) * value0 field) - value1 field + ((+ 9) * value2 field))
    ((- value0 field) + ((+ 4) * value1 field) - ((+ 3) * value2 field))
    (((+ 9) * value0 field) - ((+ 3) * value1 field) - ((+ 6) * value2 field))

fieldExtensional :
  (left right : TriangleField) →
  value0 left ≡ value0 right →
  value1 left ≡ value1 right →
  value2 left ≡ value2 right →
  left ≡ right
fieldExtensional
  (triangleField a b c)
  (triangleField x y z)
  refl refl refl = refl

constantKernel :
  (x : ℤ) → signedResidualDelta0 (constantField x) ≡ zeroField
constantKernel x =
  fieldExtensional
    (signedResidualDelta0 (constantField x))
    zeroField
    (RingZ.solve 1
      (λ a →
        (((Κ (- (+ 8)) ⊗ a) ⊕ (⊝ a)) ⊕ (Κ (+ 9) ⊗ a) , Κ (+ 0)))
      refl x)
    (RingZ.solve 1
      (λ a →
        (((⊝ a) ⊕ (Κ (+ 4) ⊗ a)) ⊕ (⊝ (Κ (+ 3) ⊗ a)) , Κ (+ 0)))
      refl x)
    (RingZ.solve 1
      (λ a →
        (((Κ (+ 9) ⊗ a) ⊕ (⊝ (Κ (+ 3) ⊗ a))) ⊕ (⊝ (Κ (+ 6) ⊗ a)) , Κ (+ 0)))
      refl x)

------------------------------------------------------------------------
-- Incidence-energy identity: x^T Delta_0 x equals the signed edge energy
--
--   (x1-x0)^2 + 3(x2-x1)^2 - 9(x0-x2)^2.
------------------------------------------------------------------------

dot : TriangleField → TriangleField → ℤ
dot left right =
  value0 left * value0 right
  + value1 left * value1 right
  + value2 left * value2 right

square : ℤ → ℤ
square x = x * x

signedEdgeEnergy : TriangleField → ℤ
signedEdgeEnergy field =
  square (value1 field - value0 field)
  + ((+ 3) * square (value2 field - value1 field))
  - ((+ 9) * square (value0 field - value2 field))

signedIncidenceEnergyIdentity :
  (field : TriangleField) →
  dot field (signedResidualDelta0 field) ≡ signedEdgeEnergy field
signedIncidenceEnergyIdentity (triangleField a b c) =
  RingZ.solve 3
    (λ a b c →
      ( (a ⊗ (((Κ (- (+ 8)) ⊗ a) ⊕ (⊝ b)) ⊕ (Κ (+ 9) ⊗ c)))
        ⊕ (b ⊗ (((⊝ a) ⊕ (Κ (+ 4) ⊗ b)) ⊕ (⊝ (Κ (+ 3) ⊗ c))))
        ⊕ (c ⊗ (((Κ (+ 9) ⊗ a) ⊕ (⊝ (Κ (+ 3) ⊗ b))) ⊕ (⊝ (Κ (+ 6) ⊗ c))))
      , (((b ⊕ (⊝ a)) ⊗ (b ⊕ (⊝ a)))
        ⊕ (Κ (+ 3) ⊗ ((c ⊕ (⊝ b)) ⊗ (c ⊕ (⊝ b))))
        ⊕ (⊝ (Κ (+ 9) ⊗ ((a ⊕ (⊝ c)) ⊗ (a ⊕ (⊝ c)))))))
    refl a b c

fieldSum : TriangleField → ℤ
fieldSum field = value0 field + value1 field + value2 field

negativeDirection : TriangleField
negativeDirection = triangleField (+ 1) (- (+ 1)) (+ 0)

positiveDirection : TriangleField
positiveDirection = triangleField (+ 0) (+ 1) (- (+ 1))

negativeDirectionZeroSum : fieldSum negativeDirection ≡ + 0
negativeDirectionZeroSum = refl

positiveDirectionZeroSum : fieldSum positiveDirection ≡ + 0
positiveDirectionZeroSum = refl

negativeDirectionEnergyIsMinusTwo :
  dot negativeDirection (signedResidualDelta0 negativeDirection) ≡ - (+ 2)
negativeDirectionEnergyIsMinusTwo = refl

positiveDirectionEnergyIsFour :
  dot positiveDirection (signedResidualDelta0 positiveDirection) ≡ + 4
positiveDirectionEnergyIsFour = refl

record SignedIndefiniteWitness : Set where
  constructor signedIndefiniteWitness
  field
    negativeField : TriangleField
    positiveField : TriangleField
    negativeFieldZeroSum : fieldSum negativeField ≡ + 0
    positiveFieldZeroSum : fieldSum positiveField ≡ + 0
    negativeEnergy :
      dot negativeField (signedResidualDelta0 negativeField) ≡ - (+ 2)
    positiveEnergy :
      dot positiveField (signedResidualDelta0 positiveField) ≡ + 4

canonicalSignedIndefiniteWitness : SignedIndefiniteWitness
canonicalSignedIndefiniteWitness =
  signedIndefiniteWitness
    negativeDirection
    positiveDirection
    negativeDirectionZeroSum
    positiveDirectionZeroSum
    negativeDirectionEnergyIsMinusTwo
    positiveDirectionEnergyIsFour

------------------------------------------------------------------------
-- Exact comparison with the unsigned C3 calculation.
------------------------------------------------------------------------

unsignedZeroSumModeHasEigenvalueThree :
  (u v : ℤ) →
  Unsigned.cycleLaplacian (Unsigned.zeroSumField u v)
  ≡ Unsigned.scaleField (+ 3) (Unsigned.zeroSumField u v)
unsignedZeroSumModeHasEigenvalueThree = Unsigned.zeroSumFieldEigenvalueThree

record PNFSignedResidualDelta0Boundary : Set where
  constructor pnfSignedResidualDelta0Boundary
  field
    canonicalSignedWeightsInstantiated : Bool
    literalBTWBConstructed : Bool
    constantKernelConstructed : Bool
    zeroSumSectorHasBothEnergySigns : Bool
    equalsUnsignedC3Laplacian : Bool
    positiveSemidefiniteClaimed : Bool
    continuumHodgeAuthorityGranted : Bool

canonicalPNFSignedResidualDelta0Boundary : PNFSignedResidualDelta0Boundary
canonicalPNFSignedResidualDelta0Boundary =
  pnfSignedResidualDelta0Boundary
    true true true true false false false
