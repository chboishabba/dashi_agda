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
-- quadratic residues; each scalar coefficient of a quadratic residue is a
-- linear combination of one parity class of 128 source coefficients.
--
-- This module records the exact structural consequence needed for blue-team
-- search analysis: local multiplication in T_q does not imply a local source
-- prior. Each public scalar NTT coordinate structurally sees 128 source
-- coefficients per secret polynomial, and a complete quadratic coordinate
-- pair sees all 256 coefficients of each secret polynomial.
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
-- Source parity classes and scalar target coordinates.
--
-- Reducing f modulo X^2-gamma sends even source powers to the constant part
-- and odd source powers to the linear part. There are exactly 128 coefficients
-- in either parity class.
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

sourceCoefficientsPerScalarNTTCoordinate : Nat
sourceCoefficientsPerScalarNTTCoordinate = 128

sourceCoefficientsPerQuadraticNTTCoordinate : Nat
sourceCoefficientsPerQuadraticNTTCoordinate =
  2 * sourceCoefficientsPerScalarNTTCoordinate

quadraticCoordinateSeesWholePolynomial :
  sourceCoefficientsPerQuadraticNTTCoordinate ≡ 256
quadraticCoordinateSeesWholePolynomial = refl

------------------------------------------------------------------------
-- K-PKE public-vector dependence across module dimension k.
--
-- A scalar public coordinate sums over k secret-polynomial coordinates in
-- t-hat = A-hat o s-hat + e-hat. Structurally, therefore, one scalar target
-- coordinate can depend on 128*k source-domain secret coefficients; the pair
-- forming one quadratic residue can depend on all 256*k source coefficients.
------------------------------------------------------------------------

publicScalarSourceDependencyWidth : Nat → Nat
publicScalarSourceDependencyWidth k =
  k * sourceCoefficientsPerScalarNTTCoordinate

publicQuadraticSourceDependencyWidth : Nat → Nat
publicQuadraticSourceDependencyWidth k =
  2 * publicScalarSourceDependencyWidth k

mlKem512ScalarSourceWidth : publicScalarSourceDependencyWidth 2 ≡ 256
mlKem512ScalarSourceWidth = refl

mlKem768ScalarSourceWidth : publicScalarSourceDependencyWidth 3 ≡ 384
mlKem768ScalarSourceWidth = refl

mlKem1024ScalarSourceWidth : publicScalarSourceDependencyWidth 4 ≡ 512
mlKem1024ScalarSourceWidth = refl

mlKem512QuadraticSourceWidth : publicQuadraticSourceDependencyWidth 2 ≡ 512
mlKem512QuadraticSourceWidth = refl

mlKem768QuadraticSourceWidth : publicQuadraticSourceDependencyWidth 3 ≡ 768
mlKem768QuadraticSourceWidth = refl

mlKem1024QuadraticSourceWidth : publicQuadraticSourceDependencyWidth 4 ≡ 1024
mlKem1024QuadraticSourceWidth = refl

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
    quadraticTargetCoordinateSpansWholeSourcePolynomial : Bool
    quadraticTargetCoordinateSpansWholeSourcePolynomialIsTrue :
      quadraticTargetCoordinateSpansWholeSourcePolynomial ≡ true

open NTTDataflowBoundary public

canonicalNTTDataflowBoundary : NTTDataflowBoundary
canonicalNTTDataflowBoundary =
  nttDataflowBoundary false refl false refl false refl true refl
