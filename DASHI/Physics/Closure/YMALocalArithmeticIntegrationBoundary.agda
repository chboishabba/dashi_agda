module DASHI.Physics.Closure.YMALocalArithmeticIntegrationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic
import DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic
import DASHI.Physics.Closure.YMAKingBochnerAuthorityBoundary
import DASHI.Physics.Closure.YMAFiniteDominationArithmeticComposite
import DASHI.Physics.Closure.ClaySubmissionCandidateMathBoundary

------------------------------------------------------------------------
-- YM-A local arithmetic integration boundary.
--
-- This receipt typechecks only when the local arithmetic child receipts
-- expected by the current round are present.  It records integration as
-- input capture, not Clay promotion.

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMALocalArithmeticIntegrationBoundary.agda"

boundaryName : String
boundaryName =
  "YM-A local arithmetic integration boundary"

data LocalArithmeticInput : Set where
  KillingBoundaryLocalArithmetic :
    LocalArithmeticInput
  HolonomyWilsonLocalArithmetic :
    LocalArithmeticInput
  KingBochnerAuthorityBoundary :
    LocalArithmeticInput
  FiniteDominationArithmeticComposite :
    LocalArithmeticInput
  ClaySubmissionCandidateMath :
    LocalArithmeticInput

record LocalArithmeticInputReceipt : Set where
  constructor mkLocalArithmeticInputReceipt
  field
    input :
      LocalArithmeticInput
    moduleName :
      String
    inputRecorded :
      Bool
    inputRecordedIsTrue :
      inputRecorded ≡ true
    promotesClay :
      Bool
    promotesClayIsFalse :
      promotesClay ≡ false
    receiptText :
      String

open LocalArithmeticInputReceipt public

killingBoundaryLocalArithmeticReceipt : LocalArithmeticInputReceipt
killingBoundaryLocalArithmeticReceipt =
  mkLocalArithmeticInputReceipt
    KillingBoundaryLocalArithmetic
    "DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic"
    true
    refl
    false
    refl
    "YM-A Killing boundary local arithmetic is recorded as an input receipt only; promotesClay=false."

holonomyWilsonLocalArithmeticReceipt : LocalArithmeticInputReceipt
holonomyWilsonLocalArithmeticReceipt =
  mkLocalArithmeticInputReceipt
    HolonomyWilsonLocalArithmetic
    "DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic"
    true
    refl
    false
    refl
    "YM-A holonomy/Wilson local arithmetic is recorded as an input receipt only; promotesClay=false."

kingBochnerAuthorityBoundaryReceipt : LocalArithmeticInputReceipt
kingBochnerAuthorityBoundaryReceipt =
  mkLocalArithmeticInputReceipt
    KingBochnerAuthorityBoundary
    "DASHI.Physics.Closure.YMAKingBochnerAuthorityBoundary"
    true
    refl
    false
    refl
    "YM-A King/Bochner authority boundary is recorded as an input receipt only; promotesClay=false."

finiteDominationArithmeticCompositeReceipt : LocalArithmeticInputReceipt
finiteDominationArithmeticCompositeReceipt =
  mkLocalArithmeticInputReceipt
    FiniteDominationArithmeticComposite
    "DASHI.Physics.Closure.YMAFiniteDominationArithmeticComposite"
    true
    refl
    false
    refl
    "YM-A finite domination arithmetic composite is recorded as an input receipt only; promotesClay=false."

claySubmissionCandidateMathReceipt : LocalArithmeticInputReceipt
claySubmissionCandidateMathReceipt =
  mkLocalArithmeticInputReceipt
    ClaySubmissionCandidateMath
    "DASHI.Physics.Closure.ClaySubmissionCandidateMathBoundary"
    true
    refl
    false
    refl
    "Existing Clay submission candidate math boundary is integrated as fail-closed candidate evidence only; promotesClay=false."

localArithmeticInputReceipts : List LocalArithmeticInputReceipt
localArithmeticInputReceipts =
  killingBoundaryLocalArithmeticReceipt
  ∷ holonomyWilsonLocalArithmeticReceipt
  ∷ kingBochnerAuthorityBoundaryReceipt
  ∷ finiteDominationArithmeticCompositeReceipt
  ∷ claySubmissionCandidateMathReceipt
  ∷ []

killingBoundaryPromotesClay : Bool
killingBoundaryPromotesClay = false

killingBoundaryPromotesClayIsFalse :
  killingBoundaryPromotesClay ≡ false
killingBoundaryPromotesClayIsFalse = refl

holonomyWilsonPromotesClay : Bool
holonomyWilsonPromotesClay = false

holonomyWilsonPromotesClayIsFalse :
  holonomyWilsonPromotesClay ≡ false
holonomyWilsonPromotesClayIsFalse = refl

kingBochnerPromotesClay : Bool
kingBochnerPromotesClay = false

kingBochnerPromotesClayIsFalse :
  kingBochnerPromotesClay ≡ false
kingBochnerPromotesClayIsFalse = refl

finiteDominationPromotesClay : Bool
finiteDominationPromotesClay = false

finiteDominationPromotesClayIsFalse :
  finiteDominationPromotesClay ≡ false
finiteDominationPromotesClayIsFalse = refl

claySubmissionCandidatePromotesClay : Bool
claySubmissionCandidatePromotesClay = false

claySubmissionCandidatePromotesClayIsFalse :
  claySubmissionCandidatePromotesClay ≡ false
claySubmissionCandidatePromotesClayIsFalse = refl

allLocalArithmeticInputsRecorded : Bool
allLocalArithmeticInputsRecorded = true

allLocalArithmeticInputsRecordedIsTrue :
  allLocalArithmeticInputsRecorded ≡ true
allLocalArithmeticInputsRecordedIsTrue = refl

arithmeticPromotesClay : Bool
arithmeticPromotesClay = false

arithmeticPromotesClayIsFalse :
  arithmeticPromotesClay ≡ false
arithmeticPromotesClayIsFalse = refl

integrationBoundaryRecorded : Bool
integrationBoundaryRecorded = true

integrationBoundaryRecordedIsTrue :
  integrationBoundaryRecorded ≡ true
integrationBoundaryRecordedIsTrue = refl

integrationControlCard : String
integrationControlCard =
  "O: Worker 6 / R: aggregate YM-A local arithmetic inputs / C: YMALocalArithmeticIntegrationBoundary / S: child imports required / L: imported -> recorded -> non-promoting / P: receipt surface / G: agda typecheck plus pytest text assertions / F: missing child modules block promotion."
