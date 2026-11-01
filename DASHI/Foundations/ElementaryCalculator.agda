module DASHI.Foundations.ElementaryCalculator where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- Literal carriers.  The denominator is syntactic; analytic definedness is
-- tracked separately and rejects zero denominators on concrete models.

data LiteralSign : Set where
  positiveLiteral : LiteralSign
  negativeLiteral : LiteralSign

record IntegerLiteral : Set where
  constructor integerLiteral
  field
    literalSign : LiteralSign
    literalMagnitude : Nat

open IntegerLiteral public

record RationalLiteral : Set where
  constructor rationalLiteral
  field
    numeratorLiteral : IntegerLiteral
    denominatorLiteral : Nat

open RationalLiteral public

------------------------------------------------------------------------
-- The Table-1 calculator surface from arXiv:2603.21852v2.

data CalculatorExpr : Set where
  variable : Var → CalculatorExpr
  integer : IntegerLiteral → CalculatorExpr
  rational : RationalLiteral → CalculatorExpr

  constantPi constantE constantI : CalculatorExpr
  constantMinusOne constantOne constantTwo : CalculatorExpr

  calcExp calcLog calcInverse calcHalf calcNegate calcSqrt calcSquare
    calcSigmoid calcSin calcCos calcTan
    calcArcSin calcArcCos calcArcTan
    calcSinh calcCosh calcTanh
    calcArcSinh calcArcCosh calcArcTanh :
      CalculatorExpr → CalculatorExpr

  calcAdd calcSubtract calcMultiply calcDivide
    calcLogBase calcPower calcAverage calcHypotenuse :
      CalculatorExpr → CalculatorExpr → CalculatorExpr

------------------------------------------------------------------------
-- Exp/log/sub kernel combinators.

zeroK : ExpLogSubExpr
zeroK = subE oneE oneE

negK : ExpLogSubExpr → ExpLogSubExpr
negK x = subE zeroK x

addK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
addK x y = subE x (negK y)

twoK : ExpLogSubExpr
twoK = addK oneE oneE

mulK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
mulK x y = expE (addK (logE x) (logE y))

divK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
divK x y = expE (subE (logE x) (logE y))

halfK : ExpLogSubExpr
halfK = divK oneE twoK

powK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
powK x y = expE (mulK y (logE x))

sqrtK : ExpLogSubExpr → ExpLogSubExpr
sqrtK x = powK x halfK

squareK : ExpLogSubExpr → ExpLogSubExpr
squareK x = mulK x x

minusOneK : ExpLogSubExpr
minusOneK = negK oneE

eK : ExpLogSubExpr
eK = expE oneE

iK : ExpLogSubExpr
iK = sqrtK minusOneK

piK : ExpLogSubExpr
piK = negK (mulK iK (logE minusOneK))

reciprocalK : ExpLogSubExpr → ExpLogSubExpr
reciprocalK x = divK oneE x

sigmoidK : ExpLogSubExpr → ExpLogSubExpr
sigmoidK x = divK oneE (addK oneE (expE (negK x)))

sinK : ExpLogSubExpr → ExpLogSubExpr
sinK x =
  divK
    (subE
      (expE (mulK iK x))
      (expE (negK (mulK iK x))))
    (mulK twoK iK)

cosK : ExpLogSubExpr → ExpLogSubExpr
cosK x =
  divK
    (addK
      (expE (mulK iK x))
      (expE (negK (mulK iK x))))
    twoK

tanK : ExpLogSubExpr → ExpLogSubExpr
tanK x = divK (sinK x) (cosK x)

arcSinK : ExpLogSubExpr → ExpLogSubExpr
arcSinK x =
  negK
    (mulK iK
      (logE
        (addK
          (mulK iK x)
          (sqrtK (subE oneE (squareK x))))))

arcCosK : ExpLogSubExpr → ExpLogSubExpr
arcCosK x = subE (divK piK twoK) (arcSinK x)

arcTanK : ExpLogSubExpr → ExpLogSubExpr
arcTanK x =
  mulK
    (divK iK twoK)
    (subE
      (logE (subE oneE (mulK iK x)))
      (logE (addK oneE (mulK iK x))))

sinhK : ExpLogSubExpr → ExpLogSubExpr
sinhK x = divK (subE (expE x) (expE (negK x))) twoK

coshK : ExpLogSubExpr → ExpLogSubExpr
coshK x = divK (addK (expE x) (expE (negK x))) twoK

tanhK : ExpLogSubExpr → ExpLogSubExpr
tanhK x = divK (sinhK x) (coshK x)

arcSinhK : ExpLogSubExpr → ExpLogSubExpr
arcSinhK x = logE (addK x (sqrtK (addK (squareK x) oneE)))

arcCoshK : ExpLogSubExpr → ExpLogSubExpr
arcCoshK x =
  logE
    (addK x
      (mulK
        (sqrtK (subE x oneE))
        (sqrtK (addK x oneE))))

arcTanhK : ExpLogSubExpr → ExpLogSubExpr
arcTanhK x =
  mulK halfK
    (subE
      (logE (addK oneE x))
      (logE (subE oneE x)))

logBaseK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
logBaseK base x = divK (logE x) (logE base)

averageK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
averageK x y = divK (addK x y) twoK

hypotenuseK : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr
hypotenuseK x y = sqrtK (addK (squareK x) (squareK y))

natK : Nat → ExpLogSubExpr
natK zero = zeroK
natK (suc n) = addK oneE (natK n)

integerK : IntegerLiteral → ExpLogSubExpr
integerK (integerLiteral positiveLiteral n) = natK n
integerK (integerLiteral negativeLiteral n) = negK (natK n)

rationalK : RationalLiteral → ExpLogSubExpr
rationalK (rationalLiteral n d) = divK (integerK n) (natK d)

------------------------------------------------------------------------
-- Complete lowering.  The branch/domain theorem is deliberately separate:
-- these formulas are syntactically total but analytically partial.

lowerCalculator : CalculatorExpr → ExpLogSubExpr
lowerCalculator (variable x) = varE x
lowerCalculator (integer n) = integerK n
lowerCalculator (rational q) = rationalK q
lowerCalculator constantPi = piK
lowerCalculator constantE = eK
lowerCalculator constantI = iK
lowerCalculator constantMinusOne = minusOneK
lowerCalculator constantOne = oneE
lowerCalculator constantTwo = twoK
lowerCalculator (calcExp x) = expE (lowerCalculator x)
lowerCalculator (calcLog x) = logE (lowerCalculator x)
lowerCalculator (calcInverse x) = reciprocalK (lowerCalculator x)
lowerCalculator (calcHalf x) = mulK halfK (lowerCalculator x)
lowerCalculator (calcNegate x) = negK (lowerCalculator x)
lowerCalculator (calcSqrt x) = sqrtK (lowerCalculator x)
lowerCalculator (calcSquare x) = squareK (lowerCalculator x)
lowerCalculator (calcSigmoid x) = sigmoidK (lowerCalculator x)
lowerCalculator (calcSin x) = sinK (lowerCalculator x)
lowerCalculator (calcCos x) = cosK (lowerCalculator x)
lowerCalculator (calcTan x) = tanK (lowerCalculator x)
lowerCalculator (calcArcSin x) = arcSinK (lowerCalculator x)
lowerCalculator (calcArcCos x) = arcCosK (lowerCalculator x)
lowerCalculator (calcArcTan x) = arcTanK (lowerCalculator x)
lowerCalculator (calcSinh x) = sinhK (lowerCalculator x)
lowerCalculator (calcCosh x) = coshK (lowerCalculator x)
lowerCalculator (calcTanh x) = tanhK (lowerCalculator x)
lowerCalculator (calcArcSinh x) = arcSinhK (lowerCalculator x)
lowerCalculator (calcArcCosh x) = arcCoshK (lowerCalculator x)
lowerCalculator (calcArcTanh x) = arcTanhK (lowerCalculator x)
lowerCalculator (calcAdd x y) = addK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcSubtract x y) = subE (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcMultiply x y) = mulK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcDivide x y) = divK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcLogBase x y) = logBaseK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcPower x y) = powK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcAverage x y) = averageK (lowerCalculator x) (lowerCalculator y)
lowerCalculator (calcHypotenuse x y) = hypotenuseK (lowerCalculator x) (lowerCalculator y)

evalCalculator :
  (M : ExpLogSubModel) →
  Env M →
  CalculatorExpr →
  Carrier M
evalCalculator M ρ t = evalSource M ρ (lowerCalculator t)

calculatorFrontEnd :
  (M : ExpLogSubModel) →
  ElementaryFrontEnd M
calculatorFrontEnd M =
  record
    { Syntax = CalculatorExpr
    ; eval = evalCalculator M
    ; lower = lowerCalculator
    ; lower-correct = λ ρ t → refl
    }

compileCalculator : CalculatorExpr → EMLExpr
compileCalculator t = compileEML (lowerCalculator t)

compileCalculator-correct :
  ∀ {M : ExpLogSubModel} →
  EMLCompilerLaws M →
  (ρ : Env M) →
  (t : CalculatorExpr) →
  evalEML M ρ (compileCalculator t) ≡ evalCalculator M ρ t
compileCalculator-correct laws ρ t =
  compileEML-correct _ laws ρ (lowerCalculator t)

DefinedCalculator :
  ∀ (M : ExpLogSubModel) →
  EMLAdmissibility M →
  Env M →
  CalculatorExpr → Set
DefinedCalculator M D ρ t =
  DefinedSource M D ρ (lowerCalculator t)

------------------------------------------------------------------------
-- An independent semantic interpretation must prove that the lowering really
-- has the advertised arithmetic/transcendental meaning on its chosen domain.

record CalculatorMeaning (M : ExpLogSubModel) : Set₁ where
  field
    meaning : Env M → CalculatorExpr → Carrier M
    loweringHasMeaning :
      ∀ ρ t →
      evalCalculator M ρ t ≡ meaning ρ t

open CalculatorMeaning public

calculatorMeaningCompiles :
  ∀ {M : ExpLogSubModel} →
  EMLCompilerLaws M →
  (S : CalculatorMeaning M) →
  ∀ ρ t →
  evalEML M ρ (compileCalculator t) ≡ meaning S ρ t
calculatorMeaningCompiles laws S ρ t
  rewrite compileCalculator-correct laws ρ t =
  loweringHasMeaning S ρ t
