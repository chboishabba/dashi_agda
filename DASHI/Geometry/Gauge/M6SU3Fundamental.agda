module DASHI.Geometry.Gauge.M6SU3Fundamental where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_+_; _*_)
open import Data.Product using (_×_; _,_)

open import DASHI.Geometry.Gauge.M6BitensorRepresentation

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

data FundamentalWeight : Set where
  epsilon1 epsilon2 epsilon3 : FundamentalWeight

data AntiFundamentalWeight : Set where
  barEpsilon1 barEpsilon2 barEpsilon3 : AntiFundamentalWeight

data SU3DifferenceWeight : Set where
  zeroWeight : SU3DifferenceWeight
  alpha12 alpha13 alpha21 alpha23 alpha31 alpha32 : SU3DifferenceWeight

fundamentalDifference : FundamentalWeight → FundamentalWeight → SU3DifferenceWeight
fundamentalDifference epsilon1 epsilon1 = zeroWeight
fundamentalDifference epsilon1 epsilon2 = alpha12
fundamentalDifference epsilon1 epsilon3 = alpha13
fundamentalDifference epsilon2 epsilon1 = alpha21
fundamentalDifference epsilon2 epsilon2 = zeroWeight
fundamentalDifference epsilon2 epsilon3 = alpha23
fundamentalDifference epsilon3 epsilon1 = alpha31
fundamentalDifference epsilon3 epsilon2 = alpha32
fundamentalDifference epsilon3 epsilon3 = zeroWeight

su3WeightDifference : WeightDifference FundamentalWeight
su3WeightDifference = record { _−w_ = fundamentalDifference }

zeroWeightTensorMultiplicity : Nat
zeroWeightTensorMultiplicity = 3

weightMultiplicityInMirrorTensor : SU3DifferenceWeight → Nat
weightMultiplicityInMirrorTensor zeroWeight = 3
weightMultiplicityInMirrorTensor alpha12 = 1
weightMultiplicityInMirrorTensor alpha13 = 1
weightMultiplicityInMirrorTensor alpha21 = 1
weightMultiplicityInMirrorTensor alpha23 = 1
weightMultiplicityInMirrorTensor alpha31 = 1
weightMultiplicityInMirrorTensor alpha32 = 1

data MirrorM6Shell : Set where
  invariantSinglet : MirrorM6Shell
  tracelessAdjoint : MirrorM6Shell

mirrorM6ShellDimension : MirrorM6Shell → ShellDimension
mirrorM6ShellDimension invariantSinglet = shell-dimension 1 1
mirrorM6ShellDimension tracelessAdjoint = shell-dimension 8 1

mirrorM6DimensionCloses : 3 * 3 ≡ 1 + 8
mirrorM6DimensionCloses = refl

zeroWeightShellSplit : zeroWeightTensorMultiplicity ≡ 1 + 2
zeroWeightShellSplit = refl

adjointRootCount : Nat
adjointRootCount = 6

adjointWeightCountCloses : 8 ≡ 2 + adjointRootCount
adjointWeightCountCloses = refl

data SameOrientationM6Shell : Set where
  symmetricSixShell : SameOrientationM6Shell
  antisymmetricMirrorShell : SameOrientationM6Shell

sameOrientationShellDimension : SameOrientationM6Shell → ShellDimension
sameOrientationShellDimension symmetricSixShell = shell-dimension 6 1
sameOrientationShellDimension antisymmetricMirrorShell = shell-dimension 3 1

sameOrientationM6DimensionCloses : 3 * 3 ≡ 6 + 3
sameOrientationM6DimensionCloses = refl

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
