module DASHI.Analysis.PrincipalComplexLog where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex

record PrincipalComplexLogBranch
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
    principalArgumentLower : ∀ z dz → _<_ R (neg R (pi CE)) (argument z dz)
    principalArgumentUpper : ∀ z dz → _≤_ R (argument z dz) (pi CE)

    logC : (z : ComplexPair R) → Domain z → ComplexPair R

    expLog : ∀ z dz → expC CE (logC z dz) ≡ z

    expInDomain :
      ∀ z → PrincipalStrip z → Domain (expC CE z)

    logExp :
      ∀ z sz →
      logC (expC CE z) (expInDomain z sz) ≡ z

    principalSqrt :
      (z : ComplexPair R) → Domain z → ComplexPair R

    sqrtSquare :
      ∀ z dz →
      _*C_ (principalSqrt z dz) (principalSqrt z dz) ≡ z

    minusOne : ComplexPair R
    minusOneInDomain : Domain minusOne
    sqrtMinusOneIsPositiveI :
      principalSqrt minusOne minusOneInDomain ≡ imaginaryUnit

    logMinusOneIsIPi :
      logC minusOne minusOneInDomain
      ≡ _*C_ imaginaryUnit (complex (pi CE) (zero R))

open PrincipalComplexLogBranch public

record PrincipalComplexAnalyticPackage : Set₁ where
  field
    complexPackage : ConstructedComplexPackage
    principalLog : PrincipalComplexLogBranch complexPackage

open PrincipalComplexAnalyticPackage public
