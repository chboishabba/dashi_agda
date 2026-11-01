module DASHI.Governance.AustralianSenateAutismInquiryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
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

canonicalBoundaryRegression : Autism.AutismInquiryBoundary
canonicalBoundaryRegression = Autism.canonicalAutismInquiryBoundary

intersectionalNonCollapseRegression :
  INF.FactorsThrough Autism.autismOnlyObserver Autism.situatedSupportNeed → ⊥
intersectionalNonCollapseRegression = Autism.autismLabelCannotRecoverSituatedNeed
