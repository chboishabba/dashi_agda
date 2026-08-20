module DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Marc Daumas, David Lester and César Muñoz, "Verified Real Number
-- Calculations: A Library for Interval Arithmetic", IEEE Trans. Computers 58
-- (2009), 226--237. DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
--
-- DASHI CONTRIBUTION
--
-- This closes the semantic mismatch discovered in Round55: the rational
-- interval evaluator is a CERTIFICATE arithmetic, while literal trigonometric
-- atoms live in Bishop reals.  We prove that the same rational interval
-- constructors soundly enclose actual Bishop-real expression values under
-- +,-,negation,multiplication and strictly-positive division.
--
-- Multiplication uses the constructive convex four-corner theorem; division
-- uses the constructed positive reciprocal interval and proves that the exact
-- reciprocal-product box is contained in the existing sign-aware rational
-- `divideInterval`.  No field says "the desired expression lies in this box";
-- only physical atom enclosures and denominator positivity remain leaf data.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
import DASHI.Physics.YangMills.BalabanClayT4BishopPositiveReciprocalIntervalExact as Reciprocal
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Additive interval semantics.
------------------------------------------------------------------------

addIntervalBishopSound : ∀ {x y left right} →
  Product.BishopLiesIn x left → Product.BishopLiesIn y right →
  Product.BishopLiesIn (x Bishop.+ y) (Typed.addInterval left right)
addIntervalBishopSound {x} {y} {left} {right} xIn yIn =
  Product.bishopLiesIn
    (BishopP.≤-respˡ-≃
      (Carrier.bishopEmbedAdd (Eval.lower left) (Eval.lower right))
      (BishopP.+-mono-≤
        (Product.lowerSound xIn) (Product.lowerSound yIn)))
    (BishopP.≤-respʳ-≃
      (Carrier.bishopEmbedAdd (Eval.upper left) (Eval.upper right))
      (BishopP.+-mono-≤
        (Product.upperSound xIn) (Product.upperSound yIn)))

negateIntervalBishopSound : ∀ {x box} →
  Product.BishopLiesIn x box →
  Product.BishopLiesIn (Bishop.- x) (Typed.negateInterval box)
negateIntervalBishopSound {x} {box} inside =
  Product.bishopLiesIn
    (BishopP.≤-respˡ-≃
      (Product.embedNeg (Eval.upper box))
      (BishopP.neg-mono-≤ (Product.upperSound inside)))
    (BishopP.≤-respʳ-≃
      (Product.embedNeg (Eval.lower box))
      (BishopP.neg-mono-≤ (Product.lowerSound inside)))

subtractIntervalBishopSound : ∀ {x y left right} →
  Product.BishopLiesIn x left → Product.BishopLiesIn y right →
  Product.BishopLiesIn (x Bishop.- y) (Typed.subtractInterval left right)
subtractIntervalBishopSound xIn yIn =
  addIntervalBishopSound xIn (negateIntervalBishopSound yIn)

------------------------------------------------------------------------
-- Rational interval containment.
------------------------------------------------------------------------

record IntervalContained
    (inner outer : Eval.RationalInterval) : Set where
  constructor intervalContained
  field
    lowerContained : Eval.lower outer ≤ Eval.lower inner
    upperContained : Eval.upper inner ≤ Eval.upper outer
open IntervalContained public

transportContained : ∀ {value inner outer} →
  Product.BishopLiesIn value inner → IntervalContained inner outer →
  Product.BishopLiesIn value outer
transportContained {value} {inner} {outer} inside containment =
  Product.bishopLiesIn
    (BishopP.≤-trans
      (Product.embedOrder (lowerContained containment))
      (Product.lowerSound inside))
    (BishopP.≤-trans
      (Product.upperSound inside)
      (Product.embedOrder (upperContained containment)))

endpointLowerIn : ∀ box → Eval.LiesIn (Eval.lower box) box
endpointLowerIn box =
  Eval.liesIn ℚP.≤-refl (Eval.ordered box)

endpointUpperIn : ∀ box → Eval.LiesIn (Eval.upper box) box
endpointUpperIn box =
  Eval.liesIn (Eval.ordered box) ℚP.≤-refl

lowerBelowMin4 : ∀ lower a b c d →
  lower ≤ a → lower ≤ b → lower ≤ c → lower ≤ d →
  lower ≤ Typed.min4 a b c d
lowerBelowMin4 lower a b c d l≤a l≤b l≤c l≤d =
  ℚP.⊓-glb (ℚP.⊓-glb l≤a l≤b) (ℚP.⊓-glb l≤c l≤d)

max4BelowUpper : ∀ upper a b c d →
  a ≤ upper → b ≤ upper → c ≤ upper → d ≤ upper →
  Typed.max4 a b c d ≤ upper
max4BelowUpper upper a b c d a≤u b≤u c≤u d≤u =
  ℚP.⊔-lub (ℚP.⊔-lub a≤u b≤u) (ℚP.⊔-lub c≤u d≤u)

------------------------------------------------------------------------
-- The exact reciprocal-product interval is contained in the existing
-- sign-aware divideInterval.
------------------------------------------------------------------------

divisionProductContained : ∀ numerator denominator
  (lowerPositive : 0ℚ < Eval.lower denominator) →
  let
    reciprocalBox = Eval.rationalInterval
      (Quotient.positiveReciprocal (Eval.upper denominator)
        (ℚP.<-≤-trans lowerPositive (Eval.ordered denominator)))
      (Quotient.positiveReciprocal (Eval.lower denominator) lowerPositive)
      (Quotient.reciprocalAntitonePositive
        (Eval.lower denominator) (Eval.upper denominator)
        lowerPositive
        (ℚP.<-≤-trans lowerPositive (Eval.ordered denominator))
        (Eval.ordered denominator))
  in
  IntervalContained
    (Typed.multiplyInterval numerator reciprocalBox)
    (Typed.divideInterval numerator denominator lowerPositive)
divisionProductContained numerator denominator lowerPositive =
  let
    upperPositive = ℚP.<-≤-trans lowerPositive (Eval.ordered denominator)
    qLower = Quotient.positiveReciprocal (Eval.upper denominator) upperPositive
    qUpper = Quotient.positiveReciprocal (Eval.lower denominator) lowerPositive
    reciprocalOrder = Quotient.reciprocalAntitonePositive
      (Eval.lower denominator) (Eval.upper denominator)
      lowerPositive upperPositive (Eval.ordered denominator)
    reciprocalBox = Eval.rationalInterval qLower qUpper reciprocalOrder
    divideBox = Typed.divideInterval numerator denominator lowerPositive

    ll = Eval.lower numerator * qLower
    lu = Eval.lower numerator * qUpper
    ul = Eval.upper numerator * qLower
    uu = Eval.upper numerator * qUpper

    lowerNumeratorIn = endpointLowerIn numerator
    upperNumeratorIn = endpointUpperIn numerator
    lowerDenominatorIn = endpointLowerIn denominator
    upperDenominatorIn = endpointUpperIn denominator

    llIn : Eval.LiesIn ll divideBox
    llIn = Typed.divideIntervalSound
      (Eval.lower numerator) (Eval.upper denominator)
      numerator denominator lowerNumeratorIn upperDenominatorIn lowerPositive

    luIn : Eval.LiesIn lu divideBox
    luIn = Typed.divideIntervalSound
      (Eval.lower numerator) (Eval.lower denominator)
      numerator denominator lowerNumeratorIn lowerDenominatorIn lowerPositive

    ulIn : Eval.LiesIn ul divideBox
    ulIn = Typed.divideIntervalSound
      (Eval.upper numerator) (Eval.upper denominator)
      numerator denominator upperNumeratorIn upperDenominatorIn lowerPositive

    uuIn : Eval.LiesIn uu divideBox
    uuIn = Typed.divideIntervalSound
      (Eval.upper numerator) (Eval.lower denominator)
      numerator denominator upperNumeratorIn lowerDenominatorIn lowerPositive
  in
  intervalContained
    (lowerBelowMin4 (Eval.lower divideBox) ll lu ul uu
      (Eval.lowerSound llIn) (Eval.lowerSound luIn)
      (Eval.lowerSound ulIn) (Eval.lowerSound uuIn))
    (max4BelowUpper (Eval.upper divideBox) ll lu ul uu
      (Eval.upperSound llIn) (Eval.upperSound luIn)
      (Eval.upperSound ulIn) (Eval.upperSound uuIn))

divideIntervalBishopSound : ∀ {numeratorValue denominatorValue numerator denominator}
  (numeratorIn : Product.BishopLiesIn numeratorValue numerator)
  (denominatorIn : Product.BishopLiesIn denominatorValue denominator)
  (lowerPositive : 0ℚ < Eval.lower denominator) →
  let
    positive = Reciprocal.positiveBishopInterval denominatorIn lowerPositive
  in
  Product.BishopLiesIn
    (numeratorValue Bishop.* Reciprocal.valueInverse positive)
    (Typed.divideInterval numerator denominator lowerPositive)
divideIntervalBishopSound {numeratorValue} {denominatorValue} {numerator} {denominator}
    numeratorIn denominatorIn lowerPositive =
  let
    positive = Reciprocal.positiveBishopInterval denominatorIn lowerPositive
    reciprocalIn = Reciprocal.reciprocalIntervalSound positive
    productIn = Product.multiplyIntervalBishopSound numeratorIn reciprocalIn
  in
  transportContained productIn
    (divisionProductContained numerator denominator lowerPositive)

------------------------------------------------------------------------
-- Compositional Bishop-real expression certificates.
------------------------------------------------------------------------

record BishopAtomEnvironment : Set₁ where
  field
    atomValue : Eval.TrigAtom → Bishop.ℝ
    atomInterval : Eval.TrigAtom → Eval.RationalInterval
    atomSound : ∀ atom →
      Product.BishopLiesIn (atomValue atom) (atomInterval atom)
open BishopAtomEnvironment public

record CertifiedBishopExpression
    (environment : BishopAtomEnvironment)
    (expression : Eval.DiagramExpression) : Set₁ where
  constructor certifiedBishopExpression
  field
    value : Bishop.ℝ
    interval : Eval.RationalInterval
    sound : Product.BishopLiesIn value interval
open CertifiedBishopExpression public

constantCertificate : ∀ environment rational →
  CertifiedBishopExpression environment (Eval.rationalConstant rational)
constantCertificate environment rational =
  certifiedBishopExpression
    (Product.embed rational)
    (Eval.rationalInterval rational rational ℚP.≤-refl)
    (Product.bishopLiesIn BishopP.≤-refl BishopP.≤-refl)

atomCertificate : ∀ environment atom →
  CertifiedBishopExpression environment (Eval.atom atom)
atomCertificate environment atom =
  certifiedBishopExpression
    (atomValue environment atom)
    (atomInterval environment atom)
    (atomSound environment atom)

addCertificate : ∀ {environment left right} →
  CertifiedBishopExpression environment left →
  CertifiedBishopExpression environment right →
  CertifiedBishopExpression environment (Eval.add left right)
addCertificate leftCertified rightCertified =
  certifiedBishopExpression
    (value leftCertified Bishop.+ value rightCertified)
    (Typed.addInterval (interval leftCertified) (interval rightCertified))
    (addIntervalBishopSound (sound leftCertified) (sound rightCertified))

subtractCertificate : ∀ {environment left right} →
  CertifiedBishopExpression environment left →
  CertifiedBishopExpression environment right →
  CertifiedBishopExpression environment (Eval.subtract left right)
subtractCertificate leftCertified rightCertified =
  certifiedBishopExpression
    (value leftCertified Bishop.- value rightCertified)
    (Typed.subtractInterval (interval leftCertified) (interval rightCertified))
    (subtractIntervalBishopSound (sound leftCertified) (sound rightCertified))

multiplyCertificate : ∀ {environment left right} →
  CertifiedBishopExpression environment left →
  CertifiedBishopExpression environment right →
  CertifiedBishopExpression environment (Eval.multiply left right)
multiplyCertificate leftCertified rightCertified =
  certifiedBishopExpression
    (value leftCertified Bishop.* value rightCertified)
    (Typed.multiplyInterval (interval leftCertified) (interval rightCertified))
    (Product.multiplyIntervalBishopSound (sound leftCertified) (sound rightCertified))

negateCertificate : ∀ {environment expression} →
  CertifiedBishopExpression environment expression →
  CertifiedBishopExpression environment (Eval.negate expression)
negateCertificate certified =
  certifiedBishopExpression
    (Bishop.- value certified)
    (Typed.negateInterval (interval certified))
    (negateIntervalBishopSound (sound certified))

divideCertificate : ∀ {environment numerator denominator} →
  (numeratorCertified : CertifiedBishopExpression environment numerator) →
  (denominatorCertified : CertifiedBishopExpression environment denominator) →
  (lowerPositive : 0ℚ < Eval.lower (interval denominatorCertified)) →
  CertifiedBishopExpression environment (Eval.divide numerator denominator)
divideCertificate numeratorCertified denominatorCertified lowerPositive =
  let
    positive = Reciprocal.positiveBishopInterval
      (sound denominatorCertified) lowerPositive
  in
  certifiedBishopExpression
    (value numeratorCertified Bishop.* Reciprocal.valueInverse positive)
    (Typed.divideInterval
      (interval numeratorCertified) (interval denominatorCertified)
      lowerPositive)
    (divideIntervalBishopSound
      (sound numeratorCertified) (sound denominatorCertified) lowerPositive)

bishopAddSubtractNegateIntervalSemanticsLevel : ProofLevel
bishopAddSubtractNegateIntervalSemanticsLevel = machineChecked

bishopExactMultiplyIntervalSemanticsLevel : ProofLevel
bishopExactMultiplyIntervalSemanticsLevel = machineChecked

bishopPositiveDivideIntervalSemanticsLevel : ProofLevel
bishopPositiveDivideIntervalSemanticsLevel = machineChecked

bishopDiagramCertificateCompositionalityLevel : ProofLevel
bishopDiagramCertificateCompositionalityLevel = machineChecked

-- Remaining L3 semantic leaves are now physical rather than arithmetic:
--   * actual Bishop sine/cosine/momentum values for each box atom;
--   * rational Taylor/interlacing enclosures for those atoms;
--   * positive lower bounds for the literal propagator denominators;
--   * construction of the literal Wilson/ghost/Haar DiagramExpression AST.
literalBishopOneLoopAtomEnvironmentLevel : ProofLevel
literalBishopOneLoopAtomEnvironmentLevel = conditional
