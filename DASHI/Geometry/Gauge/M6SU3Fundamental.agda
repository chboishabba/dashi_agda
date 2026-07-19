module DASHI.Geometry.Gauge.M6SU3Fundamental where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_; _*_)

open import DASHI.Geometry.Gauge.M6BitensorRepresentation

-- Dynkin labels for finite-dimensional SU(3) irreducibles.
record SU3HighestWeight : Set where
  constructor dynkin
  field
    p : Nat
    q : Nat

fundamental3 : SU3HighestWeight
fundamental3 = dynkin 1 0

antiFundamental3 : SU3HighestWeight
antiFundamental3 = dynkin 0 1

symmetric6 : SU3HighestWeight
symmetric6 = dynkin 2 0

adjoint8 : SU3HighestWeight
adjoint8 = dynkin 1 1

singlet1 : SU3HighestWeight
singlet1 = dynkin 0 0

-- The three weights of the defining representation and their mirrors.
data FundamentalWeight : Set where
  ε₁ ε₂ ε₃ : FundamentalWeight

data AntiFundamentalWeight : Set where
  -ε₁ -ε₂ -ε₃ : AntiFundamentalWeight

-- Difference weights in 3 ⊗ 3*. The zero weight occurs three times in the
-- tensor basis; each of the six roots occurs once.
data SU3DifferenceWeight : Set where
  zeroWeight : SU3DifferenceWeight
  α₁₂ α₁₃ α₂₁ α₂₃ α₃₁ α₃₂ : SU3DifferenceWeight

fundamentalDifference : FundamentalWeight → FundamentalWeight → SU3DifferenceWeight
fundamentalDifference ε₁ ε₁ = zeroWeight
fundamentalDifference ε₁ ε₂ = α₁₂
fundamentalDifference ε₁ ε₃ = α₁₃
fundamentalDifference ε₂ ε₁ = α₂₁
fundamentalDifference ε₂ ε₂ = zeroWeight
fundamentalDifference ε₂ ε₃ = α₂₃
fundamentalDifference ε₃ ε₁ = α₃₁
fundamentalDifference ε₃ ε₂ = α₃₂
fundamentalDifference ε₃ ε₃ = zeroWeight

su3WeightDifference : WeightDifference FundamentalWeight
su3WeightDifference = record { _−w_ = fundamentalDifference }

zeroWeightTensorMultiplicity : Nat
zeroWeightTensorMultiplicity = 3

rootWeightTensorMultiplicity : SU3DifferenceWeight → Nat
rootWeightTensorMultiplicity zeroWeight = 3
rootWeightTensorMultiplicity α₁₂ = 1
rootWeightTensorMultiplicity α₁₃ = 1
rootWeightTensorMultiplicity α₂₁ = 1
rootWeightTensorMultiplicity α₂₃ = 1
rootWeightTensorMultiplicity α₃₁ = 1
rootWeightTensorMultiplicity α₃₂ = 1

-- Diagonal SU(3) shells of the mirror M6 carrier 3 ⊗ 3*.
data MirrorM6Shell : Set where
  invariantSinglet : MirrorM6Shell
  tracelessAdjoint : MirrorM6Shell

mirrorM6ShellDimension : MirrorM6Shell → ShellDimension
mirrorM6ShellDimension invariantSinglet = shell-dimension 1 1
mirrorM6ShellDimension tracelessAdjoint = shell-dimension 8 1

mirrorM6DimensionCloses : 3 * 3 ≡ 1 + 8
mirrorM6DimensionCloses = refl

-- The three tensor-basis zero weights split into the singlet zero weight and
-- the rank-two Cartan zero-weight space of the adjoint.
zeroWeightShellSplit : zeroWeightTensorMultiplicity ≡ 1 + 2
zeroWeightShellSplit = refl

adjointRootCount : Nat
adjointRootCount = 6

adjointWeightCountCloses : 8 ≡ 2 + adjointRootCount
adjointWeightCountCloses = refl

-- Same-orientation M6 carrier 3 ⊗ 3.
data SameOrientationM6Shell : Set where
  symmetricSixShell : SameOrientationM6Shell
  antisymmetricMirrorShell : SameOrientationM6Shell

sameOrientationShellDimension : SameOrientationM6Shell → ShellDimension
sameOrientationShellDimension symmetricSixShell = shell-dimension 6 1
sameOrientationShellDimension antisymmetricMirrorShell = shell-dimension 3 1

sameOrientationM6DimensionCloses : 3 * 3 ≡ 6 + 3
sameOrientationM6DimensionCloses = refl

-- Representation-level decomposition witnesses. They deliberately distinguish
-- the mirror bitensor End(3) from the same-orientation tensor square.
record SU3MirrorM6Decomposition : Set where
  field
    sourceLeft  : SU3HighestWeight
    sourceRight : SU3HighestWeight
    invariant   : SU3HighestWeight
    residue     : SU3HighestWeight
    sourceLeftIsFundamental : sourceLeft ≡ fundamental3
    sourceRightIsMirror : sourceRight ≡ antiFundamental3
    invariantIsSinglet : invariant ≡ singlet1
    residueIsAdjoint : residue ≡ adjoint8

canonicalSU3MirrorM6 : SU3MirrorM6Decomposition
canonicalSU3MirrorM6 = record
  { sourceLeft = fundamental3
  ; sourceRight = antiFundamental3
  ; invariant = singlet1
  ; residue = adjoint8
  ; sourceLeftIsFundamental = refl
  ; sourceRightIsMirror = refl
  ; invariantIsSinglet = refl
  ; residueIsAdjoint = refl
  }

record SU3SameOrientationM6Decomposition : Set where
  field
    sourceLeft sourceRight : SU3HighestWeight
    symmetricPart antisymmetricPart : SU3HighestWeight
    sourcesAreFundamental : sourceLeft ≡ fundamental3 × sourceRight ≡ fundamental3
    symmetricPartIsSix : symmetricPart ≡ symmetric6
    antisymmetricPartIsMirror : antisymmetricPart ≡ antiFundamental3

open import Data.Product using (_×_; _,_)

canonicalSU3SameOrientationM6 : SU3SameOrientationM6Decomposition
canonicalSU3SameOrientationM6 = record
  { sourceLeft = fundamental3
  ; sourceRight = fundamental3
  ; symmetricPart = symmetric6
  ; antisymmetricPart = antiFundamental3
  ; sourcesAreFundamental = refl , refl
  ; symmetricPartIsSix = refl
  ; antisymmetricPartIsMirror = refl
  }
