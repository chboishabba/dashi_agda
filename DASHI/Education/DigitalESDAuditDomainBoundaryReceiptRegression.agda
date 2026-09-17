module DASHI.Education.DigitalESDAuditDomainBoundaryReceiptRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDAuditDomainBoundaryReceiptExact as Boundary

------------------------------------------------------------------------
-- Source-order RED contract for the thin domain-boundary adapter.
--
-- The production owner must provide all seven Digital-ESD audit-domain
-- families without importing the heavyweight domain owners into the source
-- audit dependency closure.
------------------------------------------------------------------------

allSevenFamiliesRequired : Boundary.DomainBoundaryCoverageBoundary
allSevenFamiliesRequired = Boundary.canonicalDomainBoundaryCoverageBoundary

boundaryReceiptsDoNotCreateEvidence :
  Boundary.DomainBoundaryReceiptCreatesEmpiricalEvidence → ⊥
boundaryReceiptsDoNotCreateEvidence = Boundary.domainBoundaryReceiptDoesNotCreateEmpiricalEvidence

boundaryReceiptsDoNotCreateAuthority :
  Boundary.DomainBoundaryReceiptCreatesAuthority → ⊥
boundaryReceiptsDoNotCreateAuthority = Boundary.domainBoundaryReceiptDoesNotCreateAuthority
