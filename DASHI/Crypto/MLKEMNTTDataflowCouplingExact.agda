module DASHI.Crypto.MLKEMNTTDataflowCouplingExact where

------------------------------------------------------------------------
-- FIPS-203 NTT DATAFLOW COUPLING
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS 203 Algorithm 9 has seven butterfly stages with lengths
-- 128,64,32,16,8,4,2. Equation (4.12) represents one NTT polynomial as 128
-- quadratic residues; each scalar coefficient of a *secret NTT residue* is a
-- linear combination of one parity class of 128 source coefficients.
--
-- Important correction: a scalar coefficient of the PUBLIC noisy equation
-- t-hat = A-hat o s-hat + e-hat is not restricted to one secret parity class.
-- Algorithm 12 BaseCaseMultiply couples both local components, so either public
-- scalar component can structurally depend on both 128-coefficient parity
-- classes of each secret polynomial. Thus one public scalar equation can span
-- all 256*k source secret coefficients, not merely 128*k.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.List.Base using (length)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; z≤n; s≤s)

------------------------------------------------------------------------
-- Algorithm-9 butterfly-stage arithmetic.
------------------------------------------------------------------------

algorithm9StageLengths : List Nat
algorithm9StageLengths =
  128 ∷ 64 ∷ 32 ∷ 16 ∷ 8 ∷ 4 ∷ 2 ∷ []

algorithm9StageCount : length algorithm9StageLengths ≡ 7
algorithm9StageCount = refl

dependencyWidthAfterStages : Nat → Nat
dependencyWidthAfterStages zero = 1
dependencyWidthAfterStages (suc n) = 2 * dependencyWidthAfterStages n

sevenStageScalarDependencyWidth : dependencyWidthAfterStages 7 ≡ 128
sevenStageScalarDependencyWidth = refl

------------------------------------------------------------------------
-- Exact bounded index for the 128 quadratic coordinates / parity positions.
------------------------------------------------------------------------

record Index128 : Set where
  constructor index128
  field
    value : Nat
    within128 : value < 128

open Index128 public

zeroIndex128 : Index128
zeroIndex128 = index128 0 (s≤s z≤n)

------------------------------------------------------------------------
-- Source parity classes and scalar SECRET-NTT target coordinates.
------------------------------------------------------------------------

data ResidueComponent : Set where
  constantPart linearPart : ResidueComponent

record NTTScalarCoordinate : Set where
  constructor scalarCoordinate
  field
    residueIndex : Index128
    component : ResidueComponent

open NTTScalarCoordinate public

record SourceCoefficient : Set where
  constructor sourceCoefficient
  field
    parityIndex : Index128
    sourceComponent : ResidueComponent

open SourceCoefficient public

data StructurallyDependsOn : NTTScalarCoordinate → SourceCoefficient → Set where
  constantDependency : ∀ outputIndex sourceIndex →
    StructurallyDependsOn
      (scalarCoordinate outputIndex constantPart)
      (sourceCoefficient sourceIndex constantPart)
  linearDependency : ∀ outputIndex sourceIndex →
    StructurallyDependsOn
      (scalarCoordinate outputIndex linearPart)
      (sourceCoefficient sourceIndex linearPart)

record SharesSourceDependency
    (left right : NTTScalarCoordinate) : Set where
  constructor sharesSourceDependency
  field
    source : SourceCoefficient
    leftDepends : StructurallyDependsOn left source
    rightDepends : StructurallyDependsOn right source

open SharesSourceDependency public

constantCoordinatesShareSource : ∀ i j →
  SharesSourceDependency
    (scalarCoordinate i constantPart)
    (scalarCoordinate j constantPart)
constantCoordinatesShareSource i j =
  sharesSourceDependency
    (sourceCoefficient zeroIndex128 constantPart)
    (constantDependency i zeroIndex128)
    (constantDependency j zeroIndex128)

linearCoordinatesShareSource : ∀ i j →
  SharesSourceDependency
    (scalarCoordinate i linearPart)
    (scalarCoordinate j linearPart)
linearCoordinatesShareSource i j =
  sharesSourceDependency
    (sourceCoefficient zeroIndex128 linearPart)
    (linearDependency i zeroIndex128)
    (linearDependency j zeroIndex128)

crossComponentsDoNotShareSource : ∀ i j →
  SharesSourceDependency
    (scalarCoordinate i constantPart)
    (scalarCoordinate j linearPart) → ⊥
crossComponentsDoNotShareSource i j
  (sharesSourceDependency (sourceCoefficient s constantPart) _ ())
crossComponentsDoNotShareSource i j
  (sharesSourceDependency (sourceCoefficient s linearPart) () _)

sourceCoefficientsPerSecretScalarNTTCoordinate : Nat
sourceCoefficientsPerSecretScalarNTTCoordinate = 128

sourceCoefficientsPerSecretQuadraticNTTCoordinate : Nat
sourceCoefficientsPerSecretQuadraticNTTCoordinate =
  2 * sourceCoefficientsPerSecretScalarNTTCoordinate

secretQuadraticCoordinateSeesWholePolynomial :
  sourceCoefficientsPerSecretQuadraticNTTCoordinate ≡ 256
secretQuadraticCoordinateSeesWholePolynomial = refl

------------------------------------------------------------------------
-- Secret representation widths versus PUBLIC equation widths.
------------------------------------------------------------------------

secretScalarSourceDependencyWidth : Nat → Nat
secretScalarSourceDependencyWidth k =
  k * sourceCoefficientsPerSecretScalarNTTCoordinate

secretQuadraticSourceDependencyWidth : Nat → Nat
secretQuadraticSourceDependencyWidth k =
  k * sourceCoefficientsPerSecretQuadraticNTTCoordinate

mlKem512SecretScalarSourceWidth : secretScalarSourceDependencyWidth 2 ≡ 256
mlKem512SecretScalarSourceWidth = refl

mlKem768SecretScalarSourceWidth : secretScalarSourceDependencyWidth 3 ≡ 384
mlKem768SecretScalarSourceWidth = refl

mlKem1024SecretScalarSourceWidth : secretScalarSourceDependencyWidth 4 ≡ 512
mlKem1024SecretScalarSourceWidth = refl

mlKem512SecretQuadraticSourceWidth : secretQuadraticSourceDependencyWidth 2 ≡ 512
mlKem512SecretQuadraticSourceWidth = refl

mlKem768SecretQuadraticSourceWidth : secretQuadraticSourceDependencyWidth 3 ≡ 768
mlKem768SecretQuadraticSourceWidth = refl

mlKem1024SecretQuadraticSourceWidth : secretQuadraticSourceDependencyWidth 4 ≡ 1024
mlKem1024SecretQuadraticSourceWidth = refl

------------------------------------------------------------------------
-- Public equation recoupling.
--
-- BaseCaseMultiply uses both local secret components to produce either output
-- component. Therefore either scalar component of one public quadratic equation
-- can depend on the entire 256-coefficient source polynomial for every secret
-- module coordinate participating in that row.
------------------------------------------------------------------------

publicEquationScalarSourceDependencyWidth : Nat → Nat
publicEquationScalarSourceDependencyWidth k =
  k * sourceCoefficientsPerSecretQuadraticNTTCoordinate

publicEquationQuadraticSourceDependencyWidth : Nat → Nat
publicEquationQuadraticSourceDependencyWidth =
  publicEquationScalarSourceDependencyWidth

mlKem512PublicScalarSourceWidth :
  publicEquationScalarSourceDependencyWidth 2 ≡ 512
mlKem512PublicScalarSourceWidth = refl

mlKem768PublicScalarSourceWidth :
  publicEquationScalarSourceDependencyWidth 3 ≡ 768
mlKem768PublicScalarSourceWidth = refl

mlKem1024PublicScalarSourceWidth :
  publicEquationScalarSourceDependencyWidth 4 ≡ 1024
mlKem1024PublicScalarSourceWidth = refl

mlKem512PublicQuadraticSourceWidth :
  publicEquationQuadraticSourceDependencyWidth 2 ≡ 512
mlKem512PublicQuadraticSourceWidth = refl

mlKem768PublicQuadraticSourceWidth :
  publicEquationQuadraticSourceDependencyWidth 3 ≡ 768
mlKem768PublicQuadraticSourceWidth = refl

mlKem1024PublicQuadraticSourceWidth :
  publicEquationQuadraticSourceDependencyWidth 4 ≡ 1024
mlKem1024PublicQuadraticSourceWidth = refl

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record NTTDataflowBoundary : Set where
  constructor nttDataflowBoundary
  field
    localMultiplicationMeansLocalSourcePrior : Bool
    localMultiplicationMeansLocalSourcePriorIsFalse :
      localMultiplicationMeansLocalSourcePrior ≡ false
    structuralSharedVariablesProveStatisticalDependence : Bool
    structuralSharedVariablesProveStatisticalDependenceIsFalse :
      structuralSharedVariablesProveStatisticalDependence ≡ false
    structuralSharedVariablesProveHardness : Bool
    structuralSharedVariablesProveHardnessIsFalse :
      structuralSharedVariablesProveHardness ≡ false
    secretQuadraticCoordinateSpansWholeSourcePolynomial : Bool
    secretQuadraticCoordinateSpansWholeSourcePolynomialIsTrue :
      secretQuadraticCoordinateSpansWholeSourcePolynomial ≡ true
    publicScalarEquationRecouplesBothParityBlocks : Bool
    publicScalarEquationRecouplesBothParityBlocksIsTrue :
      publicScalarEquationRecouplesBothParityBlocks ≡ true

open NTTDataflowBoundary public

canonicalNTTDataflowBoundary : NTTDataflowBoundary
canonicalNTTDataflowBoundary =
  nttDataflowBoundary false refl false refl false refl true refl true refl
