module DASHI.Physics.YangMills.BalabanClayCommonElementaryRealInhabitantsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonRationalSincCertificateExact as Sinc
import DASHI.Physics.YangMills.BalabanClayCommonLogSixteenCertificateExact as Log16

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: checked elementary-function interval enclosures and explicit
-- separation of exact polynomial arithmetic from analytic remainder bounds.
--
-- The module below reduces the configured endpoint inequalities to four
-- primitive calculus mechanisms only: signed Taylor remainders, division by a
-- positive point, -log(1-u) <= u/(1-u), and positivity of the exponential tail.
------------------------------------------------------------------------

record ConfiguredElementaryRealData (Real : Set) : Set₁ where
  field
    rational : Data.Rational.ℚ → Real
    zero one : Real
    add multiply divide subtract negate : Real → Real → Real
    sine cosine logarithm exponential : Real → Real

    LessEqual StrictLess : Real → Real → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d → LessEqual (add a c) (add b d)
    divideOrderByPositive : ∀ {a b x} →
      LessEqual a b → StrictLess zero x →
      LessEqual (divide a x) (divide b x)

    InConfiguredRadius : Real → Set
    configuredPointZeroOrPositive : ∀ point → InConfiguredRadius point →
      point ≡ zero ⊎ StrictLess zero point

    polynomialReal : Agda.Builtin.List.List Data.Rational.ℚ → Real → Real

    sineCubicRemainder sineQuinticRemainder : Real → Real
    cosineQuadraticRemainder cosineQuarticRemainder : Real → Real

    sineCubicDecomposition : ∀ point →
      sine point ≡ add
        (polynomialReal Sinc.sineLowerCoefficients point)
        (sineCubicRemainder point)
    sineCubicRemainderNonnegative : ∀ point → InConfiguredRadius point →
      LessEqual zero (sineCubicRemainder point)

    sineQuinticDecomposition : ∀ point →
      add (sine point) (sineQuinticRemainder point)
      ≡ polynomialReal Sinc.sineUpperCoefficients point
    sineQuinticRemainderNonnegative : ∀ point → InConfiguredRadius point →
      LessEqual zero (sineQuinticRemainder point)

    cosineQuadraticDecomposition : ∀ point →
      cosine point ≡ add
        (polynomialReal Sinc.cosineLowerCoefficients point)
        (cosineQuadraticRemainder point)
    cosineQuadraticRemainderNonnegative : ∀ point → InConfiguredRadius point →
      LessEqual zero (cosineQuadraticRemainder point)

    cosineQuarticDecomposition : ∀ point →
      add (cosine point) (cosineQuarticRemainder point)
      ≡ polynomialReal Sinc.cosineUpperCoefficients point
    cosineQuarticRemainderNonnegative : ∀ point → InConfiguredRadius point →
      LessEqual zero (cosineQuarticRemainder point)

    sinc negativeLogSinc : Real → Real
    sincAtZero : sinc zero ≡ one
    sincAtPositive : ∀ point → StrictLess zero point →
      sinc point ≡ divide (sine point) point

    sineLowerDivideExact : ∀ point → StrictLess zero point →
      divide (polynomialReal Sinc.sineLowerCoefficients point) point
      ≡ polynomialReal Sinc.sincLowerCoefficients point
    sineUpperDivideExact : ∀ point → StrictLess zero point →
      divide (polynomialReal Sinc.sineUpperCoefficients point) point
      ≡ polynomialReal Sinc.sincUpperCoefficients point

    sincLowerAtZeroExact :
      polynomialReal Sinc.sincLowerCoefficients zero ≡ one
    sincUpperAtZeroExact :
      polynomialReal Sinc.sincUpperCoefficients zero ≡ one

    sincStrictlyPositiveFromLower : ∀ point → InConfiguredRadius point →
      LessEqual (polynomialReal Sinc.sincLowerCoefficients point) (sinc point) →
      StrictLess zero (sinc point)

    inverseSincMonotoneFromLower : ∀ point → InConfiguredRadius point →
      LessEqual (polynomialReal Sinc.sincLowerCoefficients point) (sinc point) → Set

    u : Real → Real
    uDefinition : ∀ point →
      u point ≡ subtract one (sinc point)
    uInUnitInterval : ∀ point → InConfiguredRadius point →
      LessEqual zero (u point) × StrictLess (u point) one

    negativeLogSincDefinition : ∀ point →
      negativeLogSinc point ≡ negate zero (logarithm (sinc point))

    negativeLogOneMinusBound : ∀ point → InConfiguredRadius point →
      LessEqual
        (negate zero (logarithm (subtract one (u point))))
        (divide (u point) (subtract one (u point)))

    sincToOneMinusUExact : ∀ point →
      sinc point ≡ subtract one (u point)

    configuredRatioBelowQuartic : ∀ point → InConfiguredRadius point →
      LessEqual
        (divide (u point) (subtract one (u point)))
        (polynomialReal Sinc.negativeLogSincUpperCoefficients point)

    negativeLogSincNonnegative : ∀ point → InConfiguredRadius point →
      LessEqual
        (polynomialReal Sinc.negativeLogSincLowerCoefficients point)
        (negativeLogSinc point)

    rationalOrderEmbedding : ∀ {left right} →
      Data.Rational._≤_ left right →
      LessEqual (rational left) (rational right)

    exponentialThreeAboveFourthPartialSum :
      LessEqual (rational Log16.expThreeFourthPartialSum)
        (exponential (rational Log16.threeℚ))
    logarithmMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (logarithm left) (logarithm right)
    logarithmExponentialThree :
      logarithm (exponential (rational Log16.threeℚ))
      ≡ rational Log16.threeℚ

open ConfiguredElementaryRealData public

sineLowerCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet
    (polynomialReal dataSet Sinc.sineLowerCoefficients point)
    (sine dataSet point)
sineLowerCorrect dataSet point inRadius =
  subst
    (λ upper → LessEqual dataSet
      (polynomialReal dataSet Sinc.sineLowerCoefficients point) upper)
    (sym (sineCubicDecomposition dataSet point))
    (addMonotone dataSet
      (reflexive dataSet
        (polynomialReal dataSet Sinc.sineLowerCoefficients point))
      (sineCubicRemainderNonnegative dataSet point inRadius))

sineUpperCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet (sine dataSet point)
    (polynomialReal dataSet Sinc.sineUpperCoefficients point)
sineUpperCorrect dataSet point inRadius =
  subst
    (λ upper → LessEqual dataSet (sine dataSet point) upper)
    (sineQuinticDecomposition dataSet point)
    (addMonotone dataSet
      (reflexive dataSet (sine dataSet point))
      (sineQuinticRemainderNonnegative dataSet point inRadius))

cosineLowerCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet
    (polynomialReal dataSet Sinc.cosineLowerCoefficients point)
    (cosine dataSet point)
cosineLowerCorrect dataSet point inRadius =
  subst
    (λ upper → LessEqual dataSet
      (polynomialReal dataSet Sinc.cosineLowerCoefficients point) upper)
    (sym (cosineQuadraticDecomposition dataSet point))
    (addMonotone dataSet
      (reflexive dataSet
        (polynomialReal dataSet Sinc.cosineLowerCoefficients point))
      (cosineQuadraticRemainderNonnegative dataSet point inRadius))

cosineUpperCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet (cosine dataSet point)
    (polynomialReal dataSet Sinc.cosineUpperCoefficients point)
cosineUpperCorrect dataSet point inRadius =
  subst
    (λ upper → LessEqual dataSet (cosine dataSet point) upper)
    (cosineQuarticDecomposition dataSet point)
    (addMonotone dataSet
      (reflexive dataSet (cosine dataSet point))
      (cosineQuarticRemainderNonnegative dataSet point inRadius))

sincLowerCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet
    (polynomialReal dataSet Sinc.sincLowerCoefficients point)
    (sinc dataSet point)
sincLowerCorrect dataSet point inRadius
  with configuredPointZeroOrPositive dataSet point inRadius
... | inj₁ pointZero =
  subst
    (λ p → LessEqual dataSet
      (polynomialReal dataSet Sinc.sincLowerCoefficients p)
      (sinc dataSet p))
    (sym pointZero)
    (subst
      (λ lower → LessEqual dataSet lower (sinc dataSet (zero dataSet)))
      (sym (sincLowerAtZeroExact dataSet))
      (subst
        (λ upper → LessEqual dataSet (one dataSet) upper)
        (sym (sincAtZero dataSet))
        (reflexive dataSet (one dataSet))))
... | inj₂ pointPositive =
  subst
    (λ lower → LessEqual dataSet lower (sinc dataSet point))
    (sineLowerDivideExact dataSet point pointPositive)
    (subst
      (λ upper → LessEqual dataSet
        (divide dataSet
          (polynomialReal dataSet Sinc.sineLowerCoefficients point) point)
        upper)
      (sym (sincAtPositive dataSet point pointPositive))
      (divideOrderByPositive dataSet
        (sineLowerCorrect dataSet point inRadius) pointPositive))

sincUpperCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet (sinc dataSet point)
    (polynomialReal dataSet Sinc.sincUpperCoefficients point)
sincUpperCorrect dataSet point inRadius
  with configuredPointZeroOrPositive dataSet point inRadius
... | inj₁ pointZero =
  subst
    (λ p → LessEqual dataSet (sinc dataSet p)
      (polynomialReal dataSet Sinc.sincUpperCoefficients p))
    (sym pointZero)
    (subst
      (λ lower → LessEqual dataSet lower (one dataSet))
      (sincAtZero dataSet)
      (subst
        (λ upper → LessEqual dataSet (one dataSet) upper)
        (sym (sincUpperAtZeroExact dataSet))
        (reflexive dataSet (one dataSet))))
... | inj₂ pointPositive =
  subst
    (λ upper → LessEqual dataSet (sinc dataSet point) upper)
    (sineUpperDivideExact dataSet point pointPositive)
    (subst
      (λ lower → LessEqual dataSet lower
        (divide dataSet
          (polynomialReal dataSet Sinc.sineUpperCoefficients point) point))
      (sincAtPositive dataSet point pointPositive)
      (divideOrderByPositive dataSet
        (sineUpperCorrect dataSet point inRadius) pointPositive))

negativeLogSincUpperCorrect :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point →
  LessEqual dataSet (negativeLogSinc dataSet point)
    (polynomialReal dataSet Sinc.negativeLogSincUpperCoefficients point)
negativeLogSincUpperCorrect dataSet point inRadius =
  transitive dataSet
    (subst
      (λ lower → LessEqual dataSet lower
        (divide dataSet (u dataSet point)
          (subtract dataSet (one dataSet) (u dataSet point))))
      (negativeLogSincDefinition dataSet point)
      (subst
        (λ argument → LessEqual dataSet
          (negate dataSet (zero dataSet) (logarithm dataSet argument))
          (divide dataSet (u dataSet point)
            (subtract dataSet (one dataSet) (u dataSet point))))
        (sincToOneMinusUExact dataSet point)
        (negativeLogOneMinusBound dataSet point inRadius)))
    (configuredRatioBelowQuartic dataSet point inRadius)

negativeLogSincLowerCorrect = negativeLogSincNonnegative

sincPositiveOnConfiguredRadius :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point → StrictLess dataSet (zero dataSet) (sinc dataSet point)
sincPositiveOnConfiguredRadius dataSet point inRadius =
  sincStrictlyPositiveFromLower dataSet point inRadius
    (sincLowerCorrect dataSet point inRadius)

inverseSincMonotoneConfiguredRadiusBound :
  ∀ {Real} (dataSet : ConfiguredElementaryRealData Real) point →
  InConfiguredRadius dataSet point → Set
inverseSincMonotoneConfiguredRadiusBound dataSet point inRadius =
  inverseSincMonotoneFromLower dataSet point inRadius
    (sincLowerCorrect dataSet point inRadius)

negativeLogSincQuadraticConfigured = negativeLogSincUpperCorrect

asConfiguredSincAnalyticAuthority :
  ∀ {Real} → ConfiguredElementaryRealData Real →
  Sinc.ConfiguredSincAnalyticAuthority Real
asConfiguredSincAnalyticAuthority dataSet = record
  { rational = rational dataSet
  ; sine = sine dataSet
  ; cosine = cosine dataSet
  ; logarithm = logarithm dataSet
  ; divide = divide dataSet
  ; multiply = multiply dataSet
  ; subtract = subtract dataSet
  ; negate = negate dataSet
  ; zero = zero dataSet
  ; one = one dataSet
  ; InConfiguredRadius = InConfiguredRadius dataSet
  ; LessEqual = LessEqual dataSet
  ; StrictLess = StrictLess dataSet
  ; sinc = sinc dataSet
  ; negativeLogSinc = negativeLogSinc dataSet
  ; polynomialReal = polynomialReal dataSet
  ; polynomialRealAgreesWithRationalHorner = λ coefficients point → Set
  ; sineLowerCorrect = sineLowerCorrect dataSet
  ; sineUpperCorrect = sineUpperCorrect dataSet
  ; cosineLowerCorrect = cosineLowerCorrect dataSet
  ; cosineUpperCorrect = cosineUpperCorrect dataSet
  ; sincLowerCorrect = sincLowerCorrect dataSet
  ; sincUpperCorrect = sincUpperCorrect dataSet
  ; negativeLogSincLowerCorrect = negativeLogSincLowerCorrect dataSet
  ; negativeLogSincUpperCorrect = negativeLogSincUpperCorrect dataSet
  ; sincPositiveOnConfiguredRadius = sincPositiveOnConfiguredRadius dataSet
  ; inverseSincMonotoneConfiguredRadiusBound =
      inverseSincMonotoneConfiguredRadiusBound dataSet
  ; negativeLogSincQuadraticConfigured =
      negativeLogSincQuadraticConfigured dataSet
  }

asLogSixteenAnalyticAuthority :
  ∀ {Real} → ConfiguredElementaryRealData Real →
  Log16.LogSixteenAnalyticAuthority Real
asLogSixteenAnalyticAuthority dataSet = record
  { rational = rational dataSet
  ; exponential = exponential dataSet
  ; logarithm = logarithm dataSet
  ; LessEqual = LessEqual dataSet
  ; transitive = transitive dataSet
  ; rationalOrderEmbedding = rationalOrderEmbedding dataSet
  ; exponentialThreeAboveFourthPartialSum =
      exponentialThreeAboveFourthPartialSum dataSet
  ; logarithmMonotone = logarithmMonotone dataSet
  ; logarithmExponentialThree = logarithmExponentialThree dataSet
  }

configuredSineCosineReductionLevel : ProofLevel
configuredSineCosineReductionLevel = machineChecked

configuredSincDivisionReductionLevel : ProofLevel
configuredSincDivisionReductionLevel = machineChecked

configuredNegativeLogReductionLevel : ProofLevel
configuredNegativeLogReductionLevel = machineChecked

configuredLogSixteenAuthorityAdapterLevel : ProofLevel
configuredLogSixteenAuthorityAdapterLevel = machineChecked

elementaryTaylorLogExpInputsLevel : ProofLevel
elementaryTaylorLogExpInputsLevel = conditional
