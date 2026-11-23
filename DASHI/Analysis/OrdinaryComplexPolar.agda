module DASHI.Analysis.OrdinaryComplexPolar where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.PrincipalComplexLogRealization

------------------------------------------------------------------------
-- Algebraic complex-field completion.

record RealDivisionAndSquareRoot
  (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    Nonzero : Real R → Set
    Positive : Real R → Set
    reciprocal : (x : Real R) → Nonzero x → Real R
    reciprocalLeft : ∀ x nx → _*_ R (reciprocal x nx) x ≡ one R
    reciprocalRight : ∀ x nx → _*_ R x (reciprocal x nx) ≡ one R

    sqrtNonnegative : (x : Real R) → _≤_ R (zero R) x → Real R
    sqrtSquare : ∀ x px →
      _*_ R (sqrtNonnegative x px) (sqrtNonnegative x px) ≡ x
    sqrtNonnegativeResult : ∀ x px →
      _≤_ R (zero R) (sqrtNonnegative x px)

    half : Real R
    halfDouble : _+_ R half half ≡ one R

open RealDivisionAndSquareRoot public

record ComplexFieldAuthority
  (R : ConstructedOrderedCompleteReal)
  (D : RealDivisionAndSquareRoot R) : Set₁ where
  field
    NonzeroC : ComplexPair R → Set
    normSqNonnegative : ∀ z → _≤_ R (zero R) (normSqC z)
    nonzeroNormSq : ∀ z → NonzeroC z → Nonzero D (normSqC z)

  modulus : ComplexPair R → Real R
  modulus z = sqrtNonnegative D (normSqC z) (normSqNonnegative z)

  inverseC : (z : ComplexPair R) → NonzeroC z → ComplexPair R
  inverseC z nz =
    let invNorm = reciprocal D (normSqC z) (nonzeroNormSq z nz)
    in complex
         (_*_ R invNorm (re z))
         (_*_ R invNorm (neg R (im z)))

  field
    inverseLeftC : ∀ z nz → _*C_ (inverseC z nz) z ≡ oneC
    inverseRightC : ∀ z nz → _*C_ z (inverseC z nz) ≡ oneC

open ComplexFieldAuthority public

scaleComplex :
  ∀ {R : ConstructedOrderedCompleteReal} →
  Real R → ComplexPair R → ComplexPair R
scaleComplex {R} scalar (complex x y) =
  complex (_*_ R scalar x) (_*_ R scalar y)

------------------------------------------------------------------------
-- Principal polar data.  `argument` is not an arbitrary branch-valued field:
-- it must reconstruct each admitted complex number through the unit-circle
-- parametrization supplied by the already constructed sine and cosine.

record OrdinaryPolarData
  (C : ConstructedComplexPackage)
  (D : RealDivisionAndSquareRoot (real (realPackage C)))
  (F : ComplexFieldAuthority (real (realPackage C)) D) : Set₁ where

  private
    R = real (realPackage C)
    E = exponential (realPackage C)
    L = logarithm (realPackage C)
    CE = complexExponential C

  field
    Domain : ComplexPair R → Set
    PrincipalStrip : ComplexPair R → Set
    NotOnNonPositiveRealAxis : ComplexPair R → Set
    domainImpliesCutAvoidance : ∀ {z} → Domain z → NotOnNonPositiveRealAxis z
    domainImpliesNonzero : ∀ {z} → Domain z → NonzeroC F z

    modulusPositive : ∀ z → Domain z → Positive E (modulus F z)

    argument : (z : ComplexPair R) → Domain z → Real R
    argumentLower : ∀ z dz → _<_ R (neg R (pi CE)) (argument z dz)
    argumentUpper : ∀ z dz → _≤_ R (argument z dz) (pi CE)

    polarDecomposition : ∀ z dz →
      z ≡ scaleComplex
            (modulus F z)
            (complex
              (cos CE (argument z dz))
              (sin CE (argument z dz)))

    exponentialInDomain : ∀ z → PrincipalStrip z → Domain (expC CE z)

  principalLog : (z : ComplexPair R) → Domain z → ComplexPair R
  principalLog z dz =
    complex
      (log L (modulus F z) (modulusPositive z dz))
      (argument z dz)

open OrdinaryPolarData public

record OrdinaryPrincipalBranchLaws
  (C : ConstructedComplexPackage)
  (D : RealDivisionAndSquareRoot (real (realPackage C)))
  (F : ComplexFieldAuthority (real (realPackage C)) D)
  (P : OrdinaryPolarData C D F) : Set₁ where

  private
    R = real (realPackage C)
    CE = complexExponential C

  field
    exponentialOfPrincipalLog : ∀ z dz →
      expC CE (principalLog P z dz) ≡ z

    principalLogOfExponential : ∀ z sz →
      principalLog P (expC CE z) (exponentialInDomain P z sz) ≡ z

  principalSqrt : (z : ComplexPair R) → Domain P z → ComplexPair R
  principalSqrt z dz =
    expC CE (scaleComplex (half D) (principalLog P z dz))

  field
    principalSqrtSquares : ∀ z dz →
      _*C_ (principalSqrt z dz) (principalSqrt z dz) ≡ z

    minusOne : ComplexPair R
    minusOneInDomain : Domain P minusOne
    principalSqrtMinusOne :
      principalSqrt minusOne minusOneInDomain ≡ imaginaryUnit
    principalLogMinusOne :
      principalLog P minusOne minusOneInDomain
      ≡ _*C_ imaginaryUnit (complex (pi CE) (zero R))

open OrdinaryPrincipalBranchLaws public

ordinaryPrincipalPolarAuthority :
  ∀ {C : ConstructedComplexPackage}
    {D : RealDivisionAndSquareRoot (real (realPackage C))}
    {F : ComplexFieldAuthority (real (realPackage C)) D}
    (P : OrdinaryPolarData C D F) →
  OrdinaryPrincipalBranchLaws C D F P →
  PrincipalPolarAuthority C
ordinaryPrincipalPolarAuthority {C} {D} P B =
  record
    { Domain = Domain P
    ; PrincipalStrip = PrincipalStrip P
    ; NotOnNonPositiveRealAxis = NotOnNonPositiveRealAxis P
    ; domainImpliesCutAvoidance = domainImpliesCutAvoidance P
    ; argument = argument P
    ; argumentLower = argumentLower P
    ; argumentUpper = argumentUpper P
    ; principalLog = principalLog P
    ; exponentialOfPrincipalLog = exponentialOfPrincipalLog B
    ; exponentialInDomain = exponentialInDomain P
    ; principalLogOfExponential = principalLogOfExponential B
    ; principalSqrt = principalSqrt B
    ; principalSqrtSquares = principalSqrtSquares B
    ; minusOne = minusOne B
    ; minusOneInDomain = minusOneInDomain B
    ; principalSqrtMinusOne = principalSqrtMinusOne B
    ; principalLogMinusOne = principalLogMinusOne B
    }
