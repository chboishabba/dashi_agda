module DASHI.Analysis.PrincipalComplexLogRealization where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.PrincipalComplexLog

------------------------------------------------------------------------
-- Exact realization theorem.  Ordinary complex analysis need only establish
-- the polar/branch facts below; the resulting package is definitionally the
-- principal-log interface consumed by EML and calculator correctness.

record PrincipalPolarAuthority
  (C : ConstructedComplexPackage) : Set₁ where

  private
    R = real (realPackage C)
    E = exponential (realPackage C)
    CE = complexExponential C

  field
    Domain : ComplexPair R → Set
    PrincipalStrip : ComplexPair R → Set
    NotOnNonPositiveRealAxis : ComplexPair R → Set

    domainImpliesCutAvoidance :
      ∀ {z} → Domain z → NotOnNonPositiveRealAxis z

    argument : (z : ComplexPair R) → Domain z → Real R
    argumentLower : ∀ z dz → _<_ R (neg R (pi CE)) (argument z dz)
    argumentUpper : ∀ z dz → _≤_ R (argument z dz) (pi CE)

    principalLog : (z : ComplexPair R) → Domain z → ComplexPair R
    exponentialOfPrincipalLog :
      ∀ z dz → expC CE (principalLog z dz) ≡ z

    exponentialInDomain :
      ∀ z → PrincipalStrip z → Domain (expC CE z)

    principalLogOfExponential :
      ∀ z sz →
      principalLog (expC CE z) (exponentialInDomain z sz) ≡ z

    principalSqrt :
      (z : ComplexPair R) → Domain z → ComplexPair R

    principalSqrtSquares :
      ∀ z dz →
      _*C_ (principalSqrt z dz) (principalSqrt z dz) ≡ z

    minusOne : ComplexPair R
    minusOneInDomain : Domain minusOne

    principalSqrtMinusOne :
      principalSqrt minusOne minusOneInDomain ≡ imaginaryUnit

    principalLogMinusOne :
      principalLog minusOne minusOneInDomain
      ≡ _*C_ imaginaryUnit (complex (pi CE) (zero R))

open PrincipalPolarAuthority public

principalLogBranchFromPolar :
  ∀ {C : ConstructedComplexPackage} →
  PrincipalPolarAuthority C →
  PrincipalComplexLogBranch C
principalLogBranchFromPolar A =
  record
    { Domain = Domain A
    ; PrincipalStrip = PrincipalStrip A
    ; NotOnNonPositiveRealAxis = NotOnNonPositiveRealAxis A
    ; domainImpliesCutAvoidance = domainImpliesCutAvoidance A
    ; argument = argument A
    ; principalArgumentLower = argumentLower A
    ; principalArgumentUpper = argumentUpper A
    ; logC = principalLog A
    ; expLog = exponentialOfPrincipalLog A
    ; expInDomain = exponentialInDomain A
    ; logExp = principalLogOfExponential A
    ; principalSqrt = principalSqrt A
    ; sqrtSquare = principalSqrtSquares A
    ; minusOne = minusOne A
    ; minusOneInDomain = minusOneInDomain A
    ; sqrtMinusOneIsPositiveI = principalSqrtMinusOne A
    ; logMinusOneIsIPi = principalLogMinusOne A
    }

principalComplexPackageFromPolar :
  ∀ {C : ConstructedComplexPackage} →
  PrincipalPolarAuthority C →
  PrincipalComplexAnalyticPackage
principalComplexPackageFromPolar {C} A =
  record
    { complexPackage = C
    ; principalLog = principalLogBranchFromPolar A
    }
