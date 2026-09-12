module DASHI.Governance.AustralianSenateAutismInquiryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.AustralianSenateAutismInquiryExact as Autism

------------------------------------------------------------------------
-- Focused regression surface for the parliamentary autism tranche.
------------------------------------------------------------------------

acquisitionCanRunAhead : Autism.acquisitionMayRunAheadOfPayment ≡ true
acquisitionCanRunAhead = refl

strategyDoesNotPayImplementation : Autism.strategyExistencePaysImplementation ≡ false
strategyDoesNotPayImplementation = refl

strategyDoesNotPayOutcome : Autism.strategyExistencePaysOutcome ≡ false
strategyDoesNotPayOutcome = refl

oeisCannotSupplyAuthorityHere : Autism.oeisSuppliesNoAuthority ≡ false
oeisCannotSupplyAuthorityHere = refl

canonicalBoundaryRegression :
  Autism.AutismInquiryBoundary
canonicalBoundaryRegression = Autism.canonicalAutismInquiryBoundary

intersectionalNonCollapseRegression :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Autism.autismOnlyObserver
    Autism.situatedSupportNeed →
  Data.Empty.⊥
intersectionalNonCollapseRegression = Autism.autismLabelCannotRecoverSituatedNeed
