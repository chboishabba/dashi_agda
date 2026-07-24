module DASHI.Foundations.OrdinaryCalculatorLedger where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorDomains

------------------------------------------------------------------------
-- Side conditions for the ordinary principal-complex interpretation.  They are
-- operation-specific: there is deliberately no claim that one global subset of
-- C is closed under every calculator constructor.

record OrdinaryCalculatorSideConditions
  (M : CalculatorDomainModel) : Set₁ where
  field
    NonZero : Value M → Set
    Positive : Value M → Set
    PrincipalLogDomain : Value M → Set
    PrincipalSqrtDomain : Value M → Set

    RationalLiteralAdmissible : RationalLiteral → Set

    ArcSinDomain ArcCosDomain ArcTanDomain : Value M → Set
    ArcSinhDomain ArcCoshDomain ArcTanhDomain : Value M → Set

open OrdinaryCalculatorSideConditions public

------------------------------------------------------------------------
-- Complete source-domain derivation for the calculator syntax.

data OrdinaryCalculatorDefined
  (M : CalculatorDomainModel)
  (C : OrdinaryCalculatorSideConditions M)
  (ρ : Environment M) :
  CalculatorExpr → Set where

  variableDefinedO : ∀ x →
    OrdinaryCalculatorDefined M C ρ (variable x)

  integerDefinedO : ∀ n →
    OrdinaryCalculatorDefined M C ρ (integer n)

  rationalDefinedO : ∀ q →
    RationalLiteralAdmissible C q →
    OrdinaryCalculatorDefined M C ρ (rational q)

  piDefinedO eDefinedO iDefinedO minusOneDefinedO oneDefinedO twoDefinedO :
    OrdinaryCalculatorDefined M C ρ constantPi

  expDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ (calcExp x)

  logDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcLog x)

  inverseDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    NonZero C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcInverse x)

  halfDefinedO negateDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ (calcHalf x)

  sqrtDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    PrincipalSqrtDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcSqrt x)

  squareDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcSquare x)

  sigmoidDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    NonZero C (evaluateSource M ρ (calcAdd constantOne (calcExp (calcNegate x)))) →
    OrdinaryCalculatorDefined M C ρ (calcSigmoid x)

  sinDefinedO cosDefinedO sinhDefinedO coshDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ (calcSin x)

  tanDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    NonZero C (evaluateSource M ρ (calcCos x)) →
    OrdinaryCalculatorDefined M C ρ (calcTan x)

  tanhDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    NonZero C (evaluateSource M ρ (calcCosh x)) →
    OrdinaryCalculatorDefined M C ρ (calcTanh x)

  arcSinDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcSinDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcSin x)

  arcCosDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcCosDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcCos x)

  arcTanDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcTanDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcTan x)

  arcSinhDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcSinhDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcSinh x)

  arcCoshDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcCoshDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcCosh x)

  arcTanhDefinedO : ∀ {x} →
    OrdinaryCalculatorDefined M C ρ x →
    ArcTanhDomain C (evaluateSource M ρ x) →
    OrdinaryCalculatorDefined M C ρ (calcArcTanh x)

  addDefinedO subtractDefinedO averageDefinedO : ∀ {x y} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ y →
    OrdinaryCalculatorDefined M C ρ (calcAdd x y)

  multiplyDefinedO : ∀ {x y} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ y →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    PrincipalLogDomain C (evaluateSource M ρ y) →
    OrdinaryCalculatorDefined M C ρ (calcMultiply x y)

  divideDefinedO : ∀ {x y} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ y →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    PrincipalLogDomain C (evaluateSource M ρ y) →
    NonZero C (evaluateSource M ρ y) →
    OrdinaryCalculatorDefined M C ρ (calcDivide x y)

  logBaseDefinedO : ∀ {base x} →
    OrdinaryCalculatorDefined M C ρ base →
    OrdinaryCalculatorDefined M C ρ x →
    PrincipalLogDomain C (evaluateSource M ρ base) →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    NonZero C (evaluateSource M ρ (calcLog base)) →
    OrdinaryCalculatorDefined M C ρ (calcLogBase base x)

  powerDefinedO : ∀ {base exponent} →
    OrdinaryCalculatorDefined M C ρ base →
    OrdinaryCalculatorDefined M C ρ exponent →
    PrincipalLogDomain C (evaluateSource M ρ base) →
    OrdinaryCalculatorDefined M C ρ (calcPower base exponent)

  hypotenuseDefinedO : ∀ {x y} →
    OrdinaryCalculatorDefined M C ρ x →
    OrdinaryCalculatorDefined M C ρ y →
    PrincipalLogDomain C (evaluateSource M ρ x) →
    PrincipalLogDomain C (evaluateSource M ρ y) →
    PrincipalSqrtDomain C
      (evaluateSource M ρ (calcAdd (calcSquare x) (calcSquare y))) →
    OrdinaryCalculatorDefined M C ρ (calcHypotenuse x y)

------------------------------------------------------------------------
-- The semantic and compiled evaluators remain those selected by the concrete
-- ordinary-complex model.  A receipt promotes each source-domain derivation to
-- compiled definedness and a semantic identity.

record OrdinaryCalculatorClosure
  (M : CalculatorDomainModel)
  (C : OrdinaryCalculatorSideConditions M) : Set₁ where
  field
    compiledDefined : ∀ ρ t →
      OrdinaryCalculatorDefined M C ρ t →
      DefinedCompiled M ρ t

    compilationCorrect : ∀ ρ t →
      OrdinaryCalculatorDefined M C ρ t →
      evaluateCompiled M ρ t ≡ evaluateSource M ρ t

  certified : ∀ ρ t →
    OrdinaryCalculatorDefined M C ρ t →
    Σ (DefinedCompiled M ρ t)
      (λ _ → evaluateCompiled M ρ t ≡ evaluateSource M ρ t)
  certified ρ t domain =
    compiledDefined ρ t domain , compilationCorrect ρ t domain

open OrdinaryCalculatorClosure public

------------------------------------------------------------------------
-- Family projections make it possible to close and audit the ledger in stages.

data CalculatorPrimitiveFamily : Set where
  literalsAndConstants : CalculatorPrimitiveFamily
  entireFunctions : CalculatorPrimitiveFamily
  positiveLogArithmetic : CalculatorPrimitiveFamily
  meromorphicFunctions : CalculatorPrimitiveFamily
  principalInverseFunctions : CalculatorPrimitiveFamily

primitiveFamily : CalculatorExpr → CalculatorPrimitiveFamily
primitiveFamily (variable _) = literalsAndConstants
primitiveFamily (integer _) = literalsAndConstants
primitiveFamily (rational _) = literalsAndConstants
primitiveFamily constantPi = literalsAndConstants
primitiveFamily constantE = literalsAndConstants
primitiveFamily constantI = literalsAndConstants
primitiveFamily constantMinusOne = literalsAndConstants
primitiveFamily constantOne = literalsAndConstants
primitiveFamily constantTwo = literalsAndConstants
primitiveFamily (calcExp _) = entireFunctions
primitiveFamily (calcSin _) = entireFunctions
primitiveFamily (calcCos _) = entireFunctions
primitiveFamily (calcSinh _) = entireFunctions
primitiveFamily (calcCosh _) = entireFunctions
primitiveFamily (calcLog _) = positiveLogArithmetic
primitiveFamily (calcHalf _) = positiveLogArithmetic
primitiveFamily (calcNegate _) = positiveLogArithmetic
primitiveFamily (calcSqrt _) = positiveLogArithmetic
primitiveFamily (calcSquare _) = positiveLogArithmetic
primitiveFamily (calcAdd _ _) = positiveLogArithmetic
primitiveFamily (calcSubtract _ _) = positiveLogArithmetic
primitiveFamily (calcMultiply _ _) = positiveLogArithmetic
primitiveFamily (calcPower _ _) = positiveLogArithmetic
primitiveFamily (calcAverage _ _) = positiveLogArithmetic
primitiveFamily (calcHypotenuse _ _) = positiveLogArithmetic
primitiveFamily (calcInverse _) = meromorphicFunctions
primitiveFamily (calcSigmoid _) = meromorphicFunctions
primitiveFamily (calcTan _) = meromorphicFunctions
primitiveFamily (calcTanh _) = meromorphicFunctions
primitiveFamily (calcDivide _ _) = meromorphicFunctions
primitiveFamily (calcLogBase _ _) = meromorphicFunctions
primitiveFamily (calcArcSin _) = principalInverseFunctions
primitiveFamily (calcArcCos _) = principalInverseFunctions
primitiveFamily (calcArcTan _) = principalInverseFunctions
primitiveFamily (calcArcSinh _) = principalInverseFunctions
primitiveFamily (calcArcCosh _) = principalInverseFunctions
primitiveFamily (calcArcTanh _) = principalInverseFunctions
