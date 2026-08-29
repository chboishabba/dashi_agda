module DASHI.Physics.Closure.NSTriadKNPackageASelfExternalSignedProductionCompilerRound216Exact where

------------------------------------------------------------------------
-- ROUND216 / BIDI CAPSTONE: TWO OWNER PAYMENTS -> ONE ROUND104 PAYMENT
--
-- The backward search from Round104 does not require separate FL/HH/CC sign
-- theorems.  It requires one estimate on the COMPLETE signed critical
-- production:
--
--   N <= a D + F.
--
-- Rounds192--194 split the literal physical forcing work exactly into self and
-- external owners.  Consequently, if those two owners admit
--
--   N_self <= a_self D + F_self
--   N_ext  <= a_ext  D + F_ext,
--
-- then the complete signed production is paid by
--
--   N_self + N_ext
--     <= (a_self + a_ext) D + (F_self + F_ext).
--
-- This is the exact algebraic weld needed to turn the old three-class view into
-- the sharper current BIDI frontier:
--
--   * self owner: finite/internal Waleffe payment (Agda same-object port gap);
--   * external owner: one genuine signed-network companion-budget theorem.
--
-- No positivity, shell count, fibre cardinality, or cellwise absolute value is
-- introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record SplitSignedCriticalPayment : Set where
  constructor split-signed-critical-payment
  field
    criticalDissipation : ℚ

    selfProduction externalProduction : ℚ
    selfAbsorbed externalAbsorbed : ℚ
    selfRemainder externalRemainder : ℚ

    selfPayment :
      selfProduction
      ≤ selfAbsorbed * criticalDissipation + selfRemainder

    externalPayment :
      externalProduction
      ≤ externalAbsorbed * criticalDissipation + externalRemainder

open SplitSignedCriticalPayment public

combinedProduction combinedAbsorbed combinedRemainder :
  SplitSignedCriticalPayment → ℚ
combinedProduction P = selfProduction P + externalProduction P
combinedAbsorbed P = selfAbsorbed P + externalAbsorbed P
combinedRemainder P = selfRemainder P + externalRemainder P

selfExternalPaymentsCombine :
  (P : SplitSignedCriticalPayment) →
  combinedProduction P
  ≤ combinedAbsorbed P * criticalDissipation P + combinedRemainder P
selfExternalPaymentsCombine P =
  let
    summed :
      selfProduction P + externalProduction P
      ≤
      (selfAbsorbed P * criticalDissipation P + selfRemainder P)
      + (externalAbsorbed P * criticalDissipation P + externalRemainder P)
    summed = ℚP.+-mono-≤ (selfPayment P) (externalPayment P)

    endpoint :
      (selfAbsorbed P * criticalDissipation P + selfRemainder P)
      + (externalAbsorbed P * criticalDissipation P + externalRemainder P)
      ≡ combinedAbsorbed P * criticalDissipation P + combinedRemainder P
    endpoint = solve
      ( selfAbsorbed P ∷ externalAbsorbed P ∷ criticalDissipation P
      ∷ selfRemainder P ∷ externalRemainder P ∷ [])
  in
  subst
    (λ upper → combinedProduction P ≤ upper)
    endpoint
    summed

round216SelfExternalSignedProductionCompilerClosed : Bool
round216SelfExternalSignedProductionCompilerClosed = true

round216RequiresClasswiseGramNegativity : Bool
round216RequiresClasswiseGramNegativity = false

round216RequiresCellwiseAbsoluteValues : Bool
round216RequiresCellwiseAbsoluteValues = false

-- Honest physical receipt boundary.
round216PhysicalInternalSelfPaymentAgdaPortClosed : Bool
round216PhysicalInternalSelfPaymentAgdaPortClosed = false

round216PhysicalExternalSignedNetworkPaymentClosed : Bool
round216PhysicalExternalSignedNetworkPaymentClosed = false

round216PackageAClosed : Bool
round216PackageAClosed = false

round216ClayPromotion : Bool
round216ClayPromotion = false

round216SelfExternalSignedProductionCompilerClosedIsTrue :
  round216SelfExternalSignedProductionCompilerClosed ≡ true
round216SelfExternalSignedProductionCompilerClosedIsTrue = refl

round216PhysicalInternalSelfPaymentAgdaPortClosedIsFalse :
  round216PhysicalInternalSelfPaymentAgdaPortClosed ≡ false
round216PhysicalInternalSelfPaymentAgdaPortClosedIsFalse = refl

round216PhysicalExternalSignedNetworkPaymentClosedIsFalse :
  round216PhysicalExternalSignedNetworkPaymentClosed ≡ false
round216PhysicalExternalSignedNetworkPaymentClosedIsFalse = refl

round216PackageAClosedIsFalse : round216PackageAClosed ≡ false
round216PackageAClosedIsFalse = refl
