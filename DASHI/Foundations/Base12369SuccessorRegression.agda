module DASHI.Foundations.Base12369SuccessorRegression where

open import Agda.Builtin.Equality using (_≡_)

open import Base369 using (HexTruth; hex-0; hex-1; hex-5)
open import DASHI.Foundations.Base12369RoleHierarchy
open import DASHI.Foundations.MixedPrimeResolution
open import DASHI.Foundations.Moonshine196883Boundary
open import DASHI.Foundations.JChartSuccessorBoundary

------------------------------------------------------------------------
-- Focused checked witnesses.

crtHexOneFiveChecks :
  hexAddViaCRT hex-1 hex-5 ≡ Base369.hexXor hex-1 hex-5
crtHexOneFiveChecks = hexAddViaCRT-agrees-15

resolution27Checks : mixedSectorCount resolution27 ≡ 27
resolution27Checks = resolution27-count

factor475971Checks : 47 * (59 * 71) ≡ 196883
factor475971Checks = moonshineLargeFactor-factorisation

plusOneDimensionChecks : moonshineLargeFactor + 1 ≡ 196884
plusOneDimensionChecks = moonshinePlusIdentity-value

chartSuccessorZeroChecks :
  successorChart (mkOverflowStep (chart 0)) ≡ chart 1
chartSuccessorZeroChecks = refl

record Base12369SuccessorReceipt : Set where
  field
    roleHierarchy : NumberRoleHierarchy
    crtBoundary : CRT23Boundary
    mixedResolutionBoundary : MixedPrimeResolutionBoundary
    moonshineBoundary : Moonshine196883Boundary
    jBoundary : JRoleBoundary
    identitySuccessorBoundary : IdentitySuccessorSplit

base12369SuccessorReceipt : Base12369SuccessorReceipt
base12369SuccessorReceipt =
  record
    { roleHierarchy = base12369RoleHierarchy
    ; crtBoundary = base369CRT23Boundary
    ; mixedResolutionBoundary = mixedPrimeResolutionBoundary
    ; moonshineBoundary = canonicalMoonshine196883Boundary
    ; jBoundary = canonicalJRoleBoundary
    ; identitySuccessorBoundary = canonicalIdentitySuccessorSplit
    }
