module DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact where

------------------------------------------------------------------------
-- ROUND443 / FINITE RATIONAL CAUCHY KERNEL: DIVISION-FREE SCHUR COMPLEMENT
--
-- The R290 resolvent on two positive cell decay rates x,y is the literal
-- rational Cauchy entry
--
--                       K(x,y) = 1 / (x+y).
--
-- R297 had left positivity of the corresponding full finite Cauchy form as an
-- analytic producer, historically motivating a Laplace/heat representation.
-- That representation is not necessary.  On positive rational rates the
-- Cauchy kernel has the exact finite Schur-complement identity
--
-- K(a,b)
--   = 2 x K(x,a) K(x,b)
--     + ((a-x)K(x,a)) K(a,b) ((b-x)K(x,b)).
--
-- Equivalently, eliminating the first rate leaves another Cauchy kernel after
-- diagonal coefficient rescaling.  Iterating therefore gives an LDL^T / sum
-- of nonnegative squares certificate using only finite rational arithmetic.
--
-- PROVENANCE
-- ----------
-- Errett Bishop and Douglas Bridges, Constructive Analysis, Springer, 1985,
-- DOI 10.1007/978-3-642-61667-9: constructive reciprocal background.
-- The Schur-complement factorisation below is a DASHI finite-rational
-- reconstruction; no external positivity theorem is used as proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _-_; _*_; _≤_; _<_; 1/_; _≟_;
   positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

positivePlusPositive :
  ∀ {left right : ℚ} → Positive left → Positive right → Positive (left + right)
positivePlusPositive {left} {right} leftPositive rightPositive =
  positive
    (subst
      (λ lower → lower < left + right)
      (ℚP.+-identityˡ 0ℚ)
      (ℚP.+-mono-<-<
        (ℚP.positive⁻¹ left)
        (ℚP.positive⁻¹ right)))

cauchyEntry : ℚ → ℚ → ℚ
cauchyEntry left right = Reciprocal.safeRationalReciprocal (left + right)

cauchyEntryInverseLaw :
  (left right : ℚ) →
  Positive left → Positive right →
  cauchyEntry left right * (left + right) ≡ 1ℚ
cauchyEntryInverseLaw left right leftPositive rightPositive =
  Reciprocal.safeRationalReciprocalTimesPositive
    (left + right)
    (positivePlusPositive leftPositive rightPositive)

cauchyEntrySymmetric :
  (left right : ℚ) →
  cauchyEntry left right ≡ cauchyEntry right left
cauchyEntrySymmetric left right =
  cong Reciprocal.safeRationalReciprocal (ℚP.+-comm left right)

safeIsLiteralInverse :
  (value : ℚ) → Positive value →
  Reciprocal.safeRationalReciprocal value ≡ ℚ.1/_ value
safeIsLiteralInverse value valuePositive with value ℚ.≟ 0ℚ
... | yes valueZero =
  Reciprocal.emptyEliminate
    (Reciprocal.positiveZeroImpossible
      (subst Positive valueZero valuePositive))
... | no valueNonzero = refl

cauchyEntryPositive :
  (left right : ℚ) →
  Positive left → Positive right →
  Positive (cauchyEntry left right)
cauchyEntryPositive left right leftPositive rightPositive =
  let
    sumPositive = positivePlusPositive leftPositive rightPositive
    instance
      sumPositiveI : Positive (left + right)
      sumPositiveI = sumPositive
      sumNonzeroI = ℚP.pos⇒nonZero (left + right)
      inversePositiveI = ℚP.1/pos⇒pos (left + right)
  in
  subst Positive
    (sym (safeIsLiteralInverse (left + right) sumPositive))
    inversePositiveI

------------------------------------------------------------------------
-- Exact pointwise Schur complement.

cauchySchurEntryIdentity :
  (x a b : ℚ) →
  Positive x → Positive a → Positive b →
  cauchyEntry a b
  ≡
  ((1ℚ + 1ℚ) * x) * cauchyEntry x a * cauchyEntry x b
  + ((a - x) * cauchyEntry x a)
      * cauchyEntry a b
      * ((b - x) * cauchyEntry x b)
cauchySchurEntryIdentity x a b xPositive aPositive bPositive =
  let
    ixa = cauchyEntry x a
    ixb = cauchyEntry x b
    iab = cauchyEntry a b

    lawXA : ixa * (x + a) ≡ 1ℚ
    lawXA = cauchyEntryInverseLaw x a xPositive aPositive

    lawXB : ixb * (x + b) ≡ 1ℚ
    lawXB = cauchyEntryInverseLaw x b xPositive bPositive

    lawAB : iab * (a + b) ≡ 1ℚ
    lawAB = cauchyEntryInverseLaw a b aPositive bPositive

    rhs =
      ((1ℚ + 1ℚ) * x) * ixa * ixb
      + ((a - x) * ixa) * iab * ((b - x) * ixb)

    insertAB :
      rhs
      ≡
      ((1ℚ + 1ℚ) * x) * ixa * ixb * (iab * (a + b))
      + ((a - x) * ixa) * iab * ((b - x) * ixb)
    insertAB =
      trans
        (solve (x ∷ a ∷ b ∷ ixa ∷ ixb ∷ iab ∷ []))
        (cong
          (λ selected →
            ((1ℚ + 1ℚ) * x) * ixa * ixb * selected
            + ((a - x) * ixa) * iab * ((b - x) * ixb))
          (sym lawAB))

    factorDenominators :
      ((1ℚ + 1ℚ) * x) * ixa * ixb * (iab * (a + b))
      + ((a - x) * ixa) * iab * ((b - x) * ixb)
      ≡ (ixa * (x + a)) * (ixb * (x + b)) * iab
    factorDenominators = solve (x ∷ a ∷ b ∷ ixa ∷ ixb ∷ iab ∷ [])

    killXA :
      (ixa * (x + a)) * (ixb * (x + b)) * iab
      ≡ 1ℚ * (ixb * (x + b)) * iab
    killXA = cong (λ selected → selected * (ixb * (x + b)) * iab) lawXA

    killXB :
      1ℚ * (ixb * (x + b)) * iab ≡ 1ℚ * 1ℚ * iab
    killXB = cong (λ selected → 1ℚ * selected * iab) lawXB
  in
  sym
    (trans insertAB
      (trans factorDenominators
        (trans killXA
          (trans killXB (solve (iab ∷ []))))))

------------------------------------------------------------------------
-- Finite certificate interface.

record PositiveRateCoefficient : Set where
  constructor positive-rate-coefficient
  field
    rate coefficient : ℚ
    ratePositive : Positive rate

open PositiveRateCoefficient public

scaleCoefficientFromHead :
  PositiveRateCoefficient → PositiveRateCoefficient → PositiveRateCoefficient
scaleCoefficientFromHead head cell =
  positive-rate-coefficient
    (rate cell)
    (((rate cell - rate head) * cauchyEntry (rate head) (rate cell))
      * coefficient cell)
    (ratePositive cell)

scaleTailFromHead :
  PositiveRateCoefficient → List PositiveRateCoefficient → List PositiveRateCoefficient
scaleTailFromHead head [] = []
scaleTailFromHead head (cell ∷ rest) =
  scaleCoefficientFromHead head cell ∷ scaleTailFromHead head rest

sumHeadCouplings :
  PositiveRateCoefficient → List PositiveRateCoefficient → ℚ
sumHeadCouplings head [] = 0ℚ
sumHeadCouplings head (cell ∷ rest) =
  cauchyEntry (rate head) (rate cell) * coefficient cell
  + sumHeadCouplings head rest

cauchyQuadratic : List PositiveRateCoefficient → ℚ
cauchyQuadratic [] = 0ℚ
cauchyQuadratic (head ∷ rest) =
  cauchyEntry (rate head) (rate head) * coefficient head * coefficient head
  + (1ℚ + 1ℚ) * coefficient head * sumHeadCouplings head rest
  + cauchyQuadratic rest

pivotLinearForm :
  PositiveRateCoefficient → List PositiveRateCoefficient → ℚ
pivotLinearForm head rest =
  coefficient head
  + ((1ℚ + 1ℚ) * rate head) * sumHeadCouplings head rest

pivotSquareTerm :
  PositiveRateCoefficient → List PositiveRateCoefficient → ℚ
pivotSquareTerm head rest =
  cauchyEntry (rate head) (rate head)
    * pivotLinearForm head rest * pivotLinearForm head rest

record FiniteCauchySchurCertificate
    (cells : List PositiveRateCoefficient) : Set where
  constructor finite-cauchy-schur-certificate
  field
    decomposedValue : ℚ
    valueExact : cauchyQuadratic cells ≡ decomposedValue
    decomposedNonnegative : 0ℚ ≤ decomposedValue

open FiniteCauchySchurCertificate public

emptyCauchyCertificate : FiniteCauchySchurCertificate []
emptyCauchyCertificate = finite-cauchy-schur-certificate 0ℚ refl ℚP.≤-refl

record HeadSchurDecomposition
    (head : PositiveRateCoefficient)
    (rest : List PositiveRateCoefficient) : Set where
  constructor head-schur-decomposition
  field
    exactDecomposition :
      cauchyQuadratic (head ∷ rest)
      ≡ pivotSquareTerm head rest
        + cauchyQuadratic (scaleTailFromHead head rest)

open HeadSchurDecomposition public

pivotSquareNonnegative :
  (head : PositiveRateCoefficient) →
  (rest : List PositiveRateCoefficient) →
  0ℚ ≤ pivotSquareTerm head rest
pivotSquareNonnegative head rest =
  let
    entry = cauchyEntry (rate head) (rate head)
    form = pivotLinearForm head rest
    entryPositive = cauchyEntryPositive
      (rate head) (rate head) (ratePositive head) (ratePositive head)
    entryNN = ℚP.<⇒≤ (ℚP.positive⁻¹ entry)
    squareNN = Rational.squareNonnegative form
    instance
      entryNNI : NonNegative entry
      entryNNI = nonNegative entryNN
      squareNNI : NonNegative (form * form)
      squareNNI = nonNegative squareNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg entry (form * form)
    rawNN : 0ℚ ≤ entry * (form * form)
    rawNN = ℚP.nonNegative⁻¹ (entry * (form * form))
    reassociate : entry * (form * form) ≡ entry * form * form
    reassociate = solve (entry ∷ form ∷ [])
  in
  subst (0ℚ ≤_) reassociate rawNN

schurStepBuildsCertificate :
  (head : PositiveRateCoefficient) →
  (rest : List PositiveRateCoefficient) →
  HeadSchurDecomposition head rest →
  FiniteCauchySchurCertificate (scaleTailFromHead head rest) →
  FiniteCauchySchurCertificate (head ∷ rest)
schurStepBuildsCertificate head rest step tail =
  let
    pivotNN = pivotSquareNonnegative head rest
    tailNN = subst
      (0ℚ ≤_)
      (sym (valueExact tail))
      (decomposedNonnegative tail)
    totalNN = Rational.addNonnegative pivotNN tailNN
  in
  finite-cauchy-schur-certificate
    (pivotSquareTerm head rest + cauchyQuadratic (scaleTailFromHead head rest))
    (exactDecomposition step)
    totalNN

certificatePaysCauchyQuadratic :
  ∀ {cells} → FiniteCauchySchurCertificate cells → 0ℚ ≤ cauchyQuadratic cells
certificatePaysCauchyQuadratic C =
  subst (0ℚ ≤_) (sym (valueExact C)) (decomposedNonnegative C)

round443LiteralRationalCauchyEntryUsesR384Reciprocal : Bool
round443LiteralRationalCauchyEntryUsesR384Reciprocal = true

round443PointwiseSchurComplementIdentityClosed : Bool
round443PointwiseSchurComplementIdentityClosed = true

round443FinitePSDCompilerCarriesExactValueEquality : Bool
round443FinitePSDCompilerCarriesExactValueEquality = true

round443HeadDecompositionAutomaticallyConstructed : Bool
round443HeadDecompositionAutomaticallyConstructed = false

round443ImproperIntegralUsed : Bool
round443ImproperIntegralUsed = false

round443ExponentialUsed : Bool
round443ExponentialUsed = false

round443PhysicalNSCauchyCertificateConstructed : Bool
round443PhysicalNSCauchyCertificateConstructed = false

round443PackageAClosed : Bool
round443PackageAClosed = false

round443ClayPromotion : Bool
round443ClayPromotion = false

round443ImproperIntegralUsedIsFalse : round443ImproperIntegralUsed ≡ false
round443ImproperIntegralUsedIsFalse = refl

round443HeadDecompositionAutomaticallyConstructedIsFalse :
  round443HeadDecompositionAutomaticallyConstructed ≡ false
round443HeadDecompositionAutomaticallyConstructedIsFalse = refl

round443PhysicalNSCauchyCertificateConstructedIsFalse :
  round443PhysicalNSCauchyCertificateConstructed ≡ false
round443PhysicalNSCauchyCertificateConstructedIsFalse = refl
