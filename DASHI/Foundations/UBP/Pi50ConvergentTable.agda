module DASHI.Foundations.UBP.Pi50ConvergentTable where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_+_; _*_)
open import Data.Rational using (ℚ; _+_; _*_; _/_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance
import DASHI.Foundations.UBP.SourceAtlas as Sources

------------------------------------------------------------------------
-- Attributed source table versus the actual simple continued fraction of pi.
--
-- DigitalEuan/UBP_Repo labels get_pi(50) as a 50-term pi continued-fraction
-- approximation. The source list agrees with OEIS A001203 through term 47,
-- then diverges at term 48:
--
--   source:    ..., 1, 7, 1, 6, 1, 99
--   canonical: ..., 1, 7, 1, 2, 3, 7
--
-- Both rationals are retained. The attributed UBP value must not be renamed
-- the 50th convergent of pi.
------------------------------------------------------------------------

infix 4 _≢_

data _≢_ {A : Set} (left right : A) : Set where
  impossible : (left ≡ right → ⊥) → left ≢ right

_≢_-elim :
  ∀ {A : Set} {left right : A} →
  left ≢ right →
  left ≡ right →
  ⊥
_≢_-elim (impossible notEqual) equality = notEqual equality

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

take : ∀ {A : Set} → Nat → List A → List A
take zero xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

sourceFirst50 : List Nat
sourceFirst50 =
  3 ∷ 7 ∷ 15 ∷ 1 ∷ 292 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷
  3 ∷ 1 ∷ 14 ∷ 2 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷
  1 ∷ 84 ∷ 2 ∷ 1 ∷ 1 ∷ 15 ∷ 3 ∷ 13 ∷ 1 ∷ 4 ∷
  2 ∷ 6 ∷ 6 ∷ 99 ∷ 1 ∷ 2 ∷ 2 ∷ 6 ∷ 3 ∷ 5 ∷
  1 ∷ 1 ∷ 6 ∷ 8 ∷ 1 ∷ 7 ∷ 1 ∷ 6 ∷ 1 ∷ 99 ∷ []

canonicalPiFirst50 : List Nat
canonicalPiFirst50 =
  3 ∷ 7 ∷ 15 ∷ 1 ∷ 292 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷
  3 ∷ 1 ∷ 14 ∷ 2 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷
  1 ∷ 84 ∷ 2 ∷ 1 ∷ 1 ∷ 15 ∷ 3 ∷ 13 ∷ 1 ∷ 4 ∷
  2 ∷ 6 ∷ 6 ∷ 99 ∷ 1 ∷ 2 ∷ 2 ∷ 6 ∷ 3 ∷ 5 ∷
  1 ∷ 1 ∷ 6 ∷ 8 ∷ 1 ∷ 7 ∷ 1 ∷ 2 ∷ 3 ∷ 7 ∷ []

canonicalPiFirst51 : List Nat
canonicalPiFirst51 =
  3 ∷ 7 ∷ 15 ∷ 1 ∷ 292 ∷ 1 ∷ 1 ∷ 1 ∷ 2 ∷ 1 ∷
  3 ∷ 1 ∷ 14 ∷ 2 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷
  1 ∷ 84 ∷ 2 ∷ 1 ∷ 1 ∷ 15 ∷ 3 ∷ 13 ∷ 1 ∷ 4 ∷
  2 ∷ 6 ∷ 6 ∷ 99 ∷ 1 ∷ 2 ∷ 2 ∷ 6 ∷ 3 ∷ 5 ∷
  1 ∷ 1 ∷ 6 ∷ 8 ∷ 1 ∷ 7 ∷ 1 ∷ 2 ∷ 3 ∷ 7 ∷
  1 ∷ []

sourceFirst50Count : listCount sourceFirst50 ≡ 50
sourceFirst50Count = refl

canonicalFirst50Count : listCount canonicalPiFirst50 ≡ 50
canonicalFirst50Count = refl

canonicalFirst51Count : listCount canonicalPiFirst51 ≡ 51
canonicalFirst51Count = refl

first47CoefficientsAgree :
  take 47 sourceFirst50 ≡ take 47 canonicalPiFirst50
first47CoefficientsAgree = refl

sourceCoefficient48 : Nat
sourceCoefficient48 = 6

canonicalCoefficient48 : Nat
canonicalCoefficient48 = 2

sourceCoefficient48IsSix : sourceCoefficient48 ≡ 6
sourceCoefficient48IsSix = refl

canonicalCoefficient48IsTwo : canonicalCoefficient48 ≡ 2
canonicalCoefficient48IsTwo = refl

coefficient48Mismatch :
  sourceCoefficient48 ≢ canonicalCoefficient48
coefficient48Mismatch = impossible (λ ())

------------------------------------------------------------------------
-- Exact convergent recurrence.
------------------------------------------------------------------------

record ConvergentState : Set where
  constructor convergentState
  field
    pPreviousPrevious : Nat
    pPrevious : Nat
    qPreviousPrevious : Nat
    qPrevious : Nat

open ConvergentState public

initialConvergentState : ConvergentState
initialConvergentState = convergentState 0 1 1 0

convergentStep : Nat → ConvergentState → ConvergentState
convergentStep coefficient state =
  convergentState
    (pPrevious state)
    (coefficient * pPrevious state + pPreviousPrevious state)
    (qPrevious state)
    (coefficient * qPrevious state + qPreviousPrevious state)

runConvergents : List Nat → ConvergentState → ConvergentState
runConvergents [] state = state
runConvergents (coefficient ∷ coefficients) state =
  runConvergents coefficients (convergentStep coefficient state)

sourceState50 : ConvergentState
sourceState50 = runConvergents sourceFirst50 initialConvergentState

canonicalState50 : ConvergentState
canonicalState50 =
  runConvergents canonicalPiFirst50 initialConvergentState

canonicalState51 : ConvergentState
canonicalState51 =
  runConvergents canonicalPiFirst51 initialConvergentState

sourceP50 : Nat
sourceP50 = pPrevious sourceState50

sourceQ50 : Nat
sourceQ50 = qPrevious sourceState50

canonicalP50 : Nat
canonicalP50 = pPrevious canonicalState50

canonicalQ50 : Nat
canonicalQ50 = qPrevious canonicalState50

canonicalP51 : Nat
canonicalP51 = pPrevious canonicalState51

canonicalQ51 : Nat
canonicalQ51 = qPrevious canonicalState51

sourceP50Exact :
  sourceP50 ≡ 183157143516396120473427579101
sourceP50Exact = refl

sourceQ50Exact :
  sourceQ50 ≡ 58300729506452262642556705291
sourceQ50Exact = refl

canonicalP50Exact :
  canonicalP50 ≡ 16397605394050964443746106649
canonicalP50Exact = refl

canonicalQ50Exact :
  canonicalQ50 ≡ 5219519906667074477262822481
canonicalQ50Exact = refl

canonicalP51Exact :
  canonicalP51 ≡ 18644210947563865148979297792
canonicalP51Exact = refl

canonicalQ51Exact :
  canonicalQ51 ≡ 5934636664705637943635533097
canonicalQ51Exact = refl

sourceNumeratorDiffersFromCanonical :
  sourceP50 ≢ canonicalP50
sourceNumeratorDiffersFromCanonical = impossible (λ ())

canonicalErrorBoundDenominator : Nat
canonicalErrorBoundDenominator = canonicalQ50 * canonicalQ51

canonicalErrorBoundDenominatorExact :
  canonicalErrorBoundDenominator
  ≡ 30975954210267369528087864730966858500331494237311153657
canonicalErrorBoundDenominatorExact = refl

------------------------------------------------------------------------
-- Exact rational observer constants for both tables.
------------------------------------------------------------------------

sourcePi50 : ℚ
sourcePi50 =
  183157143516396120473427579101 /
  58300729506452262642556705291

canonicalPi50 : ℚ
canonicalPi50 =
  16397605394050964443746106649 /
  5219519906667074477262822481

sourceY50 : ℚ
sourceY50 =
  sourcePi50 / (sourcePi50 * sourcePi50 + 2)

canonicalY50 : ℚ
canonicalY50 =
  canonicalPi50 / (canonicalPi50 * canonicalPi50 + 2)

sourceY50NormalForm : ℚ
sourceY50NormalForm =
  10678195081323867029398952980491706367345312803032847723391 /
  40344489343054752407088436891842371820968160890283666757563

canonicalY50NormalForm : ℚ
canonicalY50NormalForm =
  85587627775920406939229606214235442123216034256580776169 /
  323368238771197016635670695332535842359492259206719999923

sourceY50Normalises :
  sourceY50 ≡ sourceY50NormalForm
sourceY50Normalises = refl

canonicalY50Normalises :
  canonicalY50 ≡ canonicalY50NormalForm
canonicalY50Normalises = refl

record ContinuedFractionErrorInterface (ExactReal : Set) : Set₁ where
  field
    piExact : ExactReal
    embedRational : ℚ → ExactReal
    absoluteDifference : ExactReal → ExactReal → ExactReal
    lessThan : ExactReal → ExactReal → Set
    reciprocalErrorBound : ExactReal
    reciprocalErrorBoundDefinition :
      reciprocalErrorBound
      ≡ embedRational
          (1 /
            30975954210267369528087864730966858500331494237311153657)
    canonicalConvergentBound :
      lessThan
        (absoluteDifference piExact (embedRational canonicalPi50))
        reciprocalErrorBound

open ContinuedFractionErrorInterface public

record Pi50TableStatus : Set where
  constructor pi50TableStatus
  field
    externalRepository : String
    externalAuthor : String
    externalSourcePath : String
    sourceRequestedTerms : Nat
    sourceRequestedTermsIs50 : sourceRequestedTerms ≡ 50
    firstMismatchPositionOneBased : Nat
    firstMismatchPositionIs48 : firstMismatchPositionOneBased ≡ 48
    sourceTableMatchesCanonicalPiCFThrough47 : Bool
    sourceTableMatchesCanonicalPiCFThrough47IsTrue :
      sourceTableMatchesCanonicalPiCFThrough47 ≡ true
    sourceTableIsCanonicalPiCFThrough50 : Bool
    sourceTableIsCanonicalPiCFThrough50IsFalse :
      sourceTableIsCanonicalPiCFThrough50 ≡ false
    sourceRationalRetained : Bool
    sourceRationalRetainedIsTrue : sourceRationalRetained ≡ true
    canonicalRationalAdded : Bool
    canonicalRationalAddedIsTrue : canonicalRationalAdded ≡ true
    eightyDecimalDigitAccuracyEstablished : Bool
    eightyDecimalDigitAccuracyEstablishedIsFalse :
      eightyDecimalDigitAccuracyEstablished ≡ false
    oeisAuthor : String
    oeisTitle : String
    oeisURL : String
    reading : String

canonicalPi50TableStatus : Pi50TableStatus
canonicalPi50TableStatus =
  pi50TableStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    "core_studio_v4.0/core/ubp_unified_v5.py"
    50 refl
    48 refl
    true refl
    false refl
    true refl
    true refl
    false refl
    (Sources.author Sources.oeisPiContinuedFraction)
    (Sources.title Sources.oeisPiContinuedFraction)
    (Sources.canonicalURL Sources.oeisPiContinuedFraction)
    "the attributed UBP get_pi(50) rational is preserved exactly, but it is separated from the genuine 50-coefficient simple continued-fraction convergent of pi because the tables first disagree at coefficient 48"

pi50GenericReceipt : GenericReceipt.GenericReceipt
pi50GenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "UBP source and canonical pi 50-term tables"
    "DASHI.Foundations.UBP.Pi50ConvergentTable"
    "canonicalPi50TableStatus"
    "the attributed source coefficients, canonical OEIS coefficients, first mismatch, exact source/canonical convergents, exact observer rationals, and standard q50*q51 error-bound denominator are recorded"
    "the source value is not renamed a pi convergent; a constructive-real pi and the analytic continued-fraction error theorem remain explicit imports"
    "agda -i . DASHI/Foundations/UBP/Pi50ConvergentTable.agda"

pi50GenericReceiptNonPromoting :
  GenericReceipt.promotesClaim pi50GenericReceipt ≡ false
pi50GenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse pi50GenericReceipt
