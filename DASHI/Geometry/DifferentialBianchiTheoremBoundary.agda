module DASHI.Geometry.DifferentialBianchiTheoremBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Differential Bianchi theorem boundary.
--
-- The second Bianchi identity is a differential identity for the curvature of
-- a connection.  Its contracted form gives divergence freedom of the Einstein
-- tensor for a Levi-Civita connection.  We keep the full and contracted steps
-- distinct so a finite continuity residual cannot be mistaken for the general
-- theorem.

record CurvatureCalculus : Set₁ where
  constructor mkCurvatureCalculus
  field
    Index : Set
    Scalar : Set
    Curvature : Index → Index → Index → Index → Scalar
    CovariantDerivativeCurvature :
      Index → Index → Index → Index → Index → Scalar
    add : Scalar → Scalar → Scalar
    zero : Scalar
    cyclicBianchiExpression : Index → Index → Index → Index → Index → Scalar
    EinsteinTensor : Index → Index → Scalar
    CovariantDivergenceEinstein : Index → Scalar
    calculusLabel : String

open CurvatureCalculus public

record DifferentialBianchiWitness (C : CurvatureCalculus) : Set where
  constructor mkDifferentialBianchiWitness
  field
    curvatureBuiltFromConnection : Bool
    connectionIsLeviCivita : Bool
    covariantDerivativeDefined : Bool
    cyclicIdentity :
      (a b c d e : Index C) →
      cyclicBianchiExpression C a b c d e ≡ zero C
    fullIdentityScope : String

open DifferentialBianchiWitness public

record ContractionWitness
  (C : CurvatureCalculus)
  (full : DifferentialBianchiWitness C) : Set where
  constructor mkContractionWitness
  field
    inverseMetricAvailable : Bool
    contractionWellDefined : Bool
    derivativeCommutesWithContraction : Bool
    contractedIdentity :
      (b : Index C) → CovariantDivergenceEinstein C b ≡ zero C
    contractionScope : String

open ContractionWitness public

record DifferentialBianchiReceipt (C : CurvatureCalculus) : Set where
  constructor mkDifferentialBianchiReceipt
  field
    fullWitness : DifferentialBianchiWitness C
    contraction : ContractionWitness C fullWitness
    receiptScope : String

open DifferentialBianchiReceipt public

contractedBianchi :
  (C : CurvatureCalculus) →
  (receipt : DifferentialBianchiReceipt C) →
  (b : Index C) →
  CovariantDivergenceEinstein C b ≡ zero C
contractedBianchi C receipt b = contractedIdentity (contraction receipt) b

record BianchiPromotionBoundary : Set where
  constructor mkBianchiPromotionBoundary
  field
    theoremSchemaImplemented : Bool
    finiteContinuityModelAvailable : Bool
    generalCurvatureSymmetryProof : Bool
    generalSecondBianchiProof : Bool
    generalContractedBianchiProof : Bool
    boundaryStatement : String

open BianchiPromotionBoundary public

canonicalBianchiPromotionBoundary : BianchiPromotionBoundary
canonicalBianchiPromotionBoundary =
  mkBianchiPromotionBoundary
    true true false false false
    "full and contracted theorem interfaces are implemented; the repository still lacks a general covariant-derivative curvature proof"

canonicalDifferentialBianchiNotYetProved :
  generalSecondBianchiProof canonicalBianchiPromotionBoundary ≡ false
canonicalDifferentialBianchiNotYetProved = refl
