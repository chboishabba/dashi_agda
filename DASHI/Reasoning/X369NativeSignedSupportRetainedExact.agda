module DASHI.Reasoning.X369NativeSignedSupportRetainedExact where

-- SLR native optional signed view answer. Reuse the actual four-valued
-- evidence owner (Belnap/Dunn precedent) and ternary stage word.
-- Native unavailable answer is not the observed (false,false) answer.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Core.RequiredAxisSupportSquareExact as Required
import DASHI.Foundations.TernaryThirteenFibreSplitExact as F

data ZeroResidual : Set where
  unavailable neitherSupport bothSupport : ZeroResidual

data SupportChart : Set where
  positiveOnly negativeOnly : SupportChart
  zeroWith : ZeroResidual → SupportChart

encode : Maybe Four.PolarAssessment → SupportChart
encode nothing = zeroWith unavailable
encode (just (Four.assess false false)) = zeroWith neitherSupport
encode (just (Four.assess true true)) = zeroWith bothSupport
encode (just (Four.assess true false)) = positiveOnly
encode (just (Four.assess false true)) = negativeOnly

reopen : SupportChart → Maybe Four.PolarAssessment
reopen (zeroWith unavailable) = nothing
reopen (zeroWith neitherSupport) = just (Four.assess false false)
reopen (zeroWith bothSupport) = just (Four.assess true true)
reopen positiveOnly = just (Four.assess true false)
reopen negativeOnly = just (Four.assess false true)

sourceRoundTrip : (x : Maybe Four.PolarAssessment) → reopen (encode x) ≡ x
sourceRoundTrip nothing = refl
sourceRoundTrip (just (Four.assess false false)) = refl
sourceRoundTrip (just (Four.assess false true)) = refl
sourceRoundTrip (just (Four.assess true false)) = refl
sourceRoundTrip (just (Four.assess true true)) = refl

chartRoundTrip : (x : SupportChart) → encode (reopen x) ≡ x
chartRoundTrip positiveOnly = refl
chartRoundTrip negativeOnly = refl
chartRoundTrip (zeroWith unavailable) = refl
chartRoundTrip (zeroWith neitherSupport) = refl
chartRoundTrip (zeroWith bothSupport) = refl

project : SupportChart → F.Trit
project positiveOnly = F.positive
project negativeOnly = F.negative
project (zeroWith r) = F.neutral

sameZero : project (zeroWith unavailable) ≡ project (zeroWith bothSupport)
sameZero = refl

differentEvidence :
  reopen (zeroWith unavailable) ≡ reopen (zeroWith bothSupport) → ⊥
differentEvidence ()

missingNotObservedNeither :
  reopen (zeroWith unavailable) ≡ reopen (zeroWith neitherSupport) → ⊥
missingNotObservedNeither ()

-- A pure trit cannot carry the original evidence consumer, even
-- though it is useful as a bounded support projection.
tritOnlyCannotReopen :
  (read : F.Trit → Maybe Four.PolarAssessment) →
  ((x : SupportChart) → read (project x) ≡ reopen x) → ⊥
tritOnlyCannotReopen read exact =
  differentEvidence (join (exact (zeroWith unavailable)) (exact (zeroWith bothSupport)))
  where
    join : ∀ {A : Set} {x y z : A} → x ≡ y → x ≡ z → y ≡ z
    join refl q = q

-- The existing required-axis rule applies to observed evidence only.
-- Native missing answer stays outside the actual observed support square.
observedConflictNotPositive :
  Required.ResolvedPositive (Four.assess true true) → ⊥
observedConflictNotPositive =
  Required.conflictingCannotBeResolvedPositive (refl , refl)
  where
    open import Data.Product using (_,_)

-- No declaration manufactures an actual native SLR licence, a
-- Stage13 interpretation or proof of a proposition from this codec.
