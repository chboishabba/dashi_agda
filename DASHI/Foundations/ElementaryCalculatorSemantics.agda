module DASHI.Foundations.ElementaryCalculatorSemantics where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.ElementaryCalculator

------------------------------------------------------------------------
-- Carrier-level readings of the concrete source-kernel formulas.

zeroV : (M : ExpLogSubModel) → Carrier M
zeroV M = sub M (one M) (one M)

negV : (M : ExpLogSubModel) → Carrier M → Carrier M
negV M x = sub M (zeroV M) x

addV : (M : ExpLogSubModel) → Carrier M → Carrier M → Carrier M
addV M x y = sub M x (negV M y)

twoV : (M : ExpLogSubModel) → Carrier M
twoV M = addV M (one M) (one M)

mulV : (M : ExpLogSubModel) → Carrier M → Carrier M → Carrier M
mulV M x y = exp M (addV M (log M x) (log M y))

divV : (M : ExpLogSubModel) → Carrier M → Carrier M → Carrier M
divV M x y = exp M (sub M (log M x) (log M y))

halfV : (M : ExpLogSubModel) → Carrier M
halfV M = divV M (one M) (twoV M)

powV : (M : ExpLogSubModel) → Carrier M → Carrier M → Carrier M
powV M x y = exp M (mulV M y (log M x))

sqrtV squareV reciprocalV sigmoidV :
  (M : ExpLogSubModel) → Carrier M → Carrier M
sqrtV M x = powV M x (halfV M)
squareV M x = mulV M x x
reciprocalV M x = divV M (one M) x
sigmoidV M x = divV M (one M) (addV M (one M) (exp M (negV M x)))

minusOneV eV iV piV : (M : ExpLogSubModel) → Carrier M
minusOneV M = negV M (one M)
eV M = exp M (one M)
iV M = sqrtV M (minusOneV M)
piV M = negV M (mulV M (iV M) (log M (minusOneV M)))

sinV cosV tanV arcSinV arcCosV arcTanV :
  (M : ExpLogSubModel) → Carrier M → Carrier M
sinV M x =
  divV M
    (sub M
      (exp M (mulV M (iV M) x))
      (exp M (negV M (mulV M (iV M) x))))
    (mulV M (twoV M) (iV M))
cosV M x =
  divV M
    (addV M
      (exp M (mulV M (iV M) x))
      (exp M (negV M (mulV M (iV M) x))))
    (twoV M)
tanV M x = divV M (sinV M x) (cosV M x)
arcSinV M x =
  negV M
    (mulV M (iV M)
      (log M
        (addV M
          (mulV M (iV M) x)
          (sqrtV M (sub M (one M) (squareV M x))))))
arcCosV M x = sub M (divV M (piV M) (twoV M)) (arcSinV M x)
arcTanV M x =
  mulV M
    (divV M (iV M) (twoV M))
    (sub M
      (log M (sub M (one M) (mulV M (iV M) x)))
      (log M (addV M (one M) (mulV M (iV M) x))))

sinhV coshV tanhV arcSinhV arcCoshV arcTanhV :
  (M : ExpLogSubModel) → Carrier M → Carrier M
sinhV M x = divV M (sub M (exp M x) (exp M (negV M x))) (twoV M)
coshV M x = divV M (addV M (exp M x) (exp M (negV M x))) (twoV M)
tanhV M x = divV M (sinhV M x) (coshV M x)
arcSinhV M x = log M (addV M x (sqrtV M (addV M (squareV M x) (one M))))
arcCoshV M x =
  log M
    (addV M x
      (mulV M
        (sqrtV M (sub M x (one M)))
        (sqrtV M (addV M x (one M)))))
arcTanhV M x =
  mulV M (halfV M)
    (sub M
      (log M (addV M (one M) x))
      (log M (sub M (one M) x)))

logBaseV averageV hypotenuseV :
  (M : ExpLogSubModel) → Carrier M → Carrier M → Carrier M
logBaseV M base x = divV M (log M x) (log M base)
averageV M x y = divV M (addV M x y) (twoV M)
hypotenuseV M x y = sqrtV M (addV M (squareV M x) (squareV M y))

natV : (M : ExpLogSubModel) → Nat → Carrier M
natV M zero = zeroV M
natV M (suc n) = addV M (one M) (natV M n)

integerV : (M : ExpLogSubModel) → IntegerLiteral → Carrier M
integerV M (integerLiteral positiveLiteral n) = natV M n
integerV M (integerLiteral negativeLiteral n) = negV M (natV M n)

rationalV : (M : ExpLogSubModel) → RationalLiteral → Carrier M
rationalV M (rationalLiteral n d) = divV M (integerV M n) (natV M d)

------------------------------------------------------------------------
-- Independent named calculator semantics.

record CalculatorSemanticModel (M : ExpLogSubModel) : Set₁ where
  field
    integerS : IntegerLiteral → Carrier M
    rationalS : RationalLiteral → Carrier M

    piS eS iS minusOneS oneS twoS : Carrier M

    expS logS inverseS halfS negateS sqrtS squareS sigmoidS
      sinS cosS tanS arcSinS arcCosS arcTanS
      sinhS coshS tanhS arcSinhS arcCoshS arcTanhS :
        Carrier M → Carrier M

    addS subtractS multiplyS divideS logBaseS powerS averageS hypotenuseS :
      Carrier M → Carrier M → Carrier M

open CalculatorSemanticModel public

evalSemanticCalculator :
  ∀ {M : ExpLogSubModel} →
  CalculatorSemanticModel M →
  Env M →
  CalculatorExpr →
  Carrier M
evalSemanticCalculator S ρ (variable x) = ρ x
evalSemanticCalculator S ρ (integer n) = integerS S n
evalSemanticCalculator S ρ (rational q) = rationalS S q
evalSemanticCalculator S ρ constantPi = piS S
evalSemanticCalculator S ρ constantE = eS S
evalSemanticCalculator S ρ constantI = iS S
evalSemanticCalculator S ρ constantMinusOne = minusOneS S
evalSemanticCalculator S ρ constantOne = oneS S
evalSemanticCalculator S ρ constantTwo = twoS S
evalSemanticCalculator S ρ (calcExp x) = expS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcLog x) = logS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcInverse x) = inverseS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcHalf x) = halfS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcNegate x) = negateS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcSqrt x) = sqrtS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcSquare x) = squareS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcSigmoid x) = sigmoidS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcSin x) = sinS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcCos x) = cosS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcTan x) = tanS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcSin x) = arcSinS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcCos x) = arcCosS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcTan x) = arcTanS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcSinh x) = sinhS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcCosh x) = coshS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcTanh x) = tanhS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcSinh x) = arcSinhS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcCosh x) = arcCoshS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcArcTanh x) = arcTanhS S (evalSemanticCalculator S ρ x)
evalSemanticCalculator S ρ (calcAdd x y) = addS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcSubtract x y) = subtractS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcMultiply x y) = multiplyS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcDivide x y) = divideS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcLogBase x y) = logBaseS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcPower x y) = powerS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcAverage x y) = averageS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)
evalSemanticCalculator S ρ (calcHypotenuse x y) = hypotenuseS S (evalSemanticCalculator S ρ x) (evalSemanticCalculator S ρ y)

------------------------------------------------------------------------
-- Exact primitive laws.  These are the only calculator-specific mathematical
-- obligations; the complete lowering theorem below is structural.

record CalculatorPrimitiveLaws
  (M : ExpLogSubModel)
  (S : CalculatorSemanticModel M) : Set₁ where
  field
    integerLaw : ∀ n → integerV M n ≡ integerS S n
    rationalLaw : ∀ q → rationalV M q ≡ rationalS S q

    piLaw : piV M ≡ piS S
    eLaw : eV M ≡ eS S
    iLaw : iV M ≡ iS S
    minusOneLaw : minusOneV M ≡ minusOneS S
    oneLaw : one M ≡ oneS S
    twoLaw : twoV M ≡ twoS S

    expLaw : ∀ x → exp M x ≡ expS S x
    logLaw : ∀ x → log M x ≡ logS S x
    inverseLaw : ∀ x → reciprocalV M x ≡ inverseS S x
    halfLaw : ∀ x → mulV M (halfV M) x ≡ halfS S x
    negateLaw : ∀ x → negV M x ≡ negateS S x
    sqrtLaw : ∀ x → sqrtV M x ≡ sqrtS S x
    squareLaw : ∀ x → squareV M x ≡ squareS S x
    sigmoidLaw : ∀ x → sigmoidV M x ≡ sigmoidS S x
    sinLaw : ∀ x → sinV M x ≡ sinS S x
    cosLaw : ∀ x → cosV M x ≡ cosS S x
    tanLaw : ∀ x → tanV M x ≡ tanS S x
    arcSinLaw : ∀ x → arcSinV M x ≡ arcSinS S x
    arcCosLaw : ∀ x → arcCosV M x ≡ arcCosS S x
    arcTanLaw : ∀ x → arcTanV M x ≡ arcTanS S x
    sinhLaw : ∀ x → sinhV M x ≡ sinhS S x
    coshLaw : ∀ x → coshV M x ≡ coshS S x
    tanhLaw : ∀ x → tanhV M x ≡ tanhS S x
    arcSinhLaw : ∀ x → arcSinhV M x ≡ arcSinhS S x
    arcCoshLaw : ∀ x → arcCoshV M x ≡ arcCoshS S x
    arcTanhLaw : ∀ x → arcTanhV M x ≡ arcTanhS S x

    addLaw : ∀ x y → addV M x y ≡ addS S x y
    subtractLaw : ∀ x y → sub M x y ≡ subtractS S x y
    multiplyLaw : ∀ x y → mulV M x y ≡ multiplyS S x y
    divideLaw : ∀ x y → divV M x y ≡ divideS S x y
    logBaseLaw : ∀ x y → logBaseV M x y ≡ logBaseS S x y
    powerLaw : ∀ x y → powV M x y ≡ powerS S x y
    averageLaw : ∀ x y → averageV M x y ≡ averageS S x y
    hypotenuseLaw : ∀ x y → hypotenuseV M x y ≡ hypotenuseS S x y

open CalculatorPrimitiveLaws public

lowerCalculator-semantics :
  ∀ {M : ExpLogSubModel} {S : CalculatorSemanticModel M} →
  CalculatorPrimitiveLaws M S →
  ∀ ρ t →
  evalCalculator M ρ t ≡ evalSemanticCalculator S ρ t
lowerCalculator-semantics L ρ (variable x) = Agda.Builtin.Equality.refl
lowerCalculator-semantics L ρ (integer n) = integerLaw L n
lowerCalculator-semantics L ρ (rational q) = rationalLaw L q
lowerCalculator-semantics L ρ constantPi = piLaw L
lowerCalculator-semantics L ρ constantE = eLaw L
lowerCalculator-semantics L ρ constantI = iLaw L
lowerCalculator-semantics L ρ constantMinusOne = minusOneLaw L
lowerCalculator-semantics L ρ constantOne = oneLaw L
lowerCalculator-semantics L ρ constantTwo = twoLaw L
lowerCalculator-semantics L ρ (calcExp x)
  rewrite lowerCalculator-semantics L ρ x = expLaw L _
lowerCalculator-semantics L ρ (calcLog x)
  rewrite lowerCalculator-semantics L ρ x = logLaw L _
lowerCalculator-semantics L ρ (calcInverse x)
  rewrite lowerCalculator-semantics L ρ x = inverseLaw L _
lowerCalculator-semantics L ρ (calcHalf x)
  rewrite lowerCalculator-semantics L ρ x = halfLaw L _
lowerCalculator-semantics L ρ (calcNegate x)
  rewrite lowerCalculator-semantics L ρ x = negateLaw L _
lowerCalculator-semantics L ρ (calcSqrt x)
  rewrite lowerCalculator-semantics L ρ x = sqrtLaw L _
lowerCalculator-semantics L ρ (calcSquare x)
  rewrite lowerCalculator-semantics L ρ x = squareLaw L _
lowerCalculator-semantics L ρ (calcSigmoid x)
  rewrite lowerCalculator-semantics L ρ x = sigmoidLaw L _
lowerCalculator-semantics L ρ (calcSin x)
  rewrite lowerCalculator-semantics L ρ x = sinLaw L _
lowerCalculator-semantics L ρ (calcCos x)
  rewrite lowerCalculator-semantics L ρ x = cosLaw L _
lowerCalculator-semantics L ρ (calcTan x)
  rewrite lowerCalculator-semantics L ρ x = tanLaw L _
lowerCalculator-semantics L ρ (calcArcSin x)
  rewrite lowerCalculator-semantics L ρ x = arcSinLaw L _
lowerCalculator-semantics L ρ (calcArcCos x)
  rewrite lowerCalculator-semantics L ρ x = arcCosLaw L _
lowerCalculator-semantics L ρ (calcArcTan x)
  rewrite lowerCalculator-semantics L ρ x = arcTanLaw L _
lowerCalculator-semantics L ρ (calcSinh x)
  rewrite lowerCalculator-semantics L ρ x = sinhLaw L _
lowerCalculator-semantics L ρ (calcCosh x)
  rewrite lowerCalculator-semantics L ρ x = coshLaw L _
lowerCalculator-semantics L ρ (calcTanh x)
  rewrite lowerCalculator-semantics L ρ x = tanhLaw L _
lowerCalculator-semantics L ρ (calcArcSinh x)
  rewrite lowerCalculator-semantics L ρ x = arcSinhLaw L _
lowerCalculator-semantics L ρ (calcArcCosh x)
  rewrite lowerCalculator-semantics L ρ x = arcCoshLaw L _
lowerCalculator-semantics L ρ (calcArcTanh x)
  rewrite lowerCalculator-semantics L ρ x = arcTanhLaw L _
lowerCalculator-semantics L ρ (calcAdd x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = addLaw L _ _
lowerCalculator-semantics L ρ (calcSubtract x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = subtractLaw L _ _
lowerCalculator-semantics L ρ (calcMultiply x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = multiplyLaw L _ _
lowerCalculator-semantics L ρ (calcDivide x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = divideLaw L _ _
lowerCalculator-semantics L ρ (calcLogBase x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = logBaseLaw L _ _
lowerCalculator-semantics L ρ (calcPower x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = powerLaw L _ _
lowerCalculator-semantics L ρ (calcAverage x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = averageLaw L _ _
lowerCalculator-semantics L ρ (calcHypotenuse x y)
  rewrite lowerCalculator-semantics L ρ x
        | lowerCalculator-semantics L ρ y = hypotenuseLaw L _ _

compileCalculator-semantics :
  ∀ {M : ExpLogSubModel} {S : CalculatorSemanticModel M} →
  EMLCompilerLaws M →
  CalculatorPrimitiveLaws M S →
  ∀ ρ t →
  evalEML M ρ (compileCalculator t) ≡ evalSemanticCalculator S ρ t
compileCalculator-semantics emlLaws calculatorLaws ρ t
  rewrite compileCalculator-correct emlLaws ρ t =
  lowerCalculator-semantics calculatorLaws ρ t
