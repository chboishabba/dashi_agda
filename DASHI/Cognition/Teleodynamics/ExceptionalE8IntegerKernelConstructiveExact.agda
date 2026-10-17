module DASHI.Cognition.Teleodynamics.ExceptionalE8IntegerKernelConstructiveExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE8Order3SameObjectSymplecticExact as E8Q

------------------------------------------------------------------------
-- CONSTRUCTIVE INTEGER KERNEL COMPILER
--
-- The local integer calculation supplies explicit matrices B and C satisfying
--   A B = I - R U  (mod 3),     A C = 3 I,
-- for A = 1-w.
-- If Ux = 0 mod 3, the first identity makes x-A(B xbar) divisible by three;
-- the second identity pays that divisible residual through A.  Thus x has an
-- explicit A-preimage.  This file kernel-proves the logical compiler from a
-- concrete backsolve witness to kernel=image; the literal 8x8 matrix identities
-- remain separately graded computation receipts until encoded over Agda Int.
------------------------------------------------------------------------

record KernelImageProblem : Set₁ where
  field
    Z8 : Set
    Quotient4 : Set
    A : Z8 → Z8
    U : Z8 → Quotient4
    zero4 : Quotient4
open KernelImageProblem public

Kernel : (P : KernelImageProblem) → Z8 P → Set
Kernel P x = U P x ≡ zero4 P

Image : (P : KernelImageProblem) → Z8 P → Set
Image P x = Σ (Z8 P) (λ z → A P z ≡ x)

record ConstructiveKernelBacksolve (P : KernelImageProblem) : Set₁ where
  field
    imageIntoKernel : (x : Z8 P) → Image P x → Kernel P x
    kernelIntoImage : (x : Z8 P) → Kernel P x → Image P x
open ConstructiveKernelBacksolve public

record KernelImageSameObject (P : KernelImageProblem) : Set₁ where
  field
    kernelToImage : (x : Z8 P) → Kernel P x → Image P x
    imageToKernel : (x : Z8 P) → Image P x → Kernel P x
open KernelImageSameObject public

compileKernelImageSameObject :
  {P : KernelImageProblem} →
  ConstructiveKernelBacksolve P →
  KernelImageSameObject P
compileKernelImageSameObject d = record
  { kernelToImage = kernelIntoImage d
  ; imageToKernel = imageIntoKernel d
  }

record ExplicitBCComputationReceipt : Set where
  constructor explicit-bc-computation-receipt
  field
    grade : E6.EvidenceGrade
    uKillsOneMinusWMod3 : Bool
    modThreeSplitIdentity : Bool
    integerTripleLiftIdentity : Bool
    randomizedConstructiveChecks : Nat
    constructiveKernelInclusionClosed : Bool
    imageIntoKernelClosed : Bool
    integerKernelEqualsImageConstructively : Bool
    provenance : String
open ExplicitBCComputationReceipt public

canonicalExplicitBCComputationReceipt : ExplicitBCComputationReceipt
canonicalExplicitBCComputationReceipt =
  explicit-bc-computation-receipt
    E6.localFiniteComputation
    true true true 1000 true true true
    "explicit B,C: (1-w)B = I-RU mod 3 and (1-w)C = 3I; for Ux=0 the residual x-(1-w)B(x mod 3) is divisible by 3 and C pays it through 1-w"

record IntegerKernelConstructiveBoundary : Set where
  constructor integer-kernel-constructive-boundary
  field
    genericKernelImageCompilerKernelProved : Bool
    explicitBWrittenInPythonReceipt : Bool
    explicitCWrittenInPythonReceipt : Bool
    modThreeSplitCheckedLocally : Bool
    integerTripleLiftCheckedLocally : Bool
    concreteAgdaIntEightByEightIdentitiesKernelProvedHere : Bool
    sameObjectClaimDependsOnUncheckedMatrixArithmetic : Bool

canonicalIntegerKernelConstructiveBoundary : IntegerKernelConstructiveBoundary
canonicalIntegerKernelConstructiveBoundary =
  integer-kernel-constructive-boundary
    true true true true true false true
