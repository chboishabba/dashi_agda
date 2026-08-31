module DASHI.Core.MultiaxialResidualBundleExact where

------------------------------------------------------------------------
-- MULTIAXIAL RESIDUAL BUNDLE
--
-- Residuals are typed by what kind of incompleteness they record.  A consumer
-- contract states which residual values it can accept/carry.  Qualification is
-- therefore not identical to zeroing every residual coordinate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record ResidualBundle
    (Phenomenon Epistemic Political Responsibility Category : Set) : Set where
  constructor residualBundle
  field
    phenomenonResidual : Phenomenon
    epistemicResidual : Epistemic
    politicalResidual : Political
    responsibilityResidual : Responsibility
    categoryResidual : Category

open ResidualBundle public

record ConsumerResidualContract
    (Phenomenon Epistemic Political Responsibility Category : Set) : Set₁ where
  constructor consumerResidualContract
  field
    AcceptPhenomenon : Phenomenon → Set
    AcceptEpistemic : Epistemic → Set
    AcceptPolitical : Political → Set
    AcceptResponsibility : Responsibility → Set
    AcceptCategory : Category → Set

open ConsumerResidualContract public

record ResidualCarriageReceipt
    {Phenomenon Epistemic Political Responsibility Category : Set}
    (contract : ConsumerResidualContract
      Phenomenon Epistemic Political Responsibility Category)
    (bundle : ResidualBundle
      Phenomenon Epistemic Political Responsibility Category) : Set₁ where
  constructor residualCarriageReceipt
  field
    phenomenonAccepted : AcceptPhenomenon contract (phenomenonResidual bundle)
    epistemicAccepted : AcceptEpistemic contract (epistemicResidual bundle)
    politicalAccepted : AcceptPolitical contract (politicalResidual bundle)
    responsibilityAccepted :
      AcceptResponsibility contract (responsibilityResidual bundle)
    categoryAccepted : AcceptCategory contract (categoryResidual bundle)

open ResidualCarriageReceipt public

record MultiaxialResidualBoundary : Set where
  constructor multiaxialResidualBoundary
  field
    phenomenonResidualEqualsEpistemicResidual : Bool
    phenomenonResidualEqualsEpistemicResidualIsFalse :
      phenomenonResidualEqualsEpistemicResidual ≡ false
    epistemicResidualEqualsPoliticalResidual : Bool
    epistemicResidualEqualsPoliticalResidualIsFalse :
      epistemicResidualEqualsPoliticalResidual ≡ false
    politicalResidualEqualsResponsibilityResidual : Bool
    politicalResidualEqualsResponsibilityResidualIsFalse :
      politicalResidualEqualsResponsibilityResidual ≡ false
    responsibilityResidualEqualsCategoryResidual : Bool
    responsibilityResidualEqualsCategoryResidualIsFalse :
      responsibilityResidualEqualsCategoryResidual ≡ false
    qualifiedUseRequiresAllResidualsToBeZero : Bool
    qualifiedUseRequiresAllResidualsToBeZeroIsFalse :
      qualifiedUseRequiresAllResidualsToBeZero ≡ false
    consumerMustDeclareResidualAcceptance : Bool
    consumerMustDeclareResidualAcceptanceIsTrue :
      consumerMustDeclareResidualAcceptance ≡ true

canonicalMultiaxialResidualBoundary : MultiaxialResidualBoundary
canonicalMultiaxialResidualBoundary =
  multiaxialResidualBoundary false refl false refl false refl false refl false refl true refl
