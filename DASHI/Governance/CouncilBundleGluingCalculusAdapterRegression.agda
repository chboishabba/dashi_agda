module DASHI.Governance.CouncilBundleGluingCalculusAdapterRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.LocalGlobalCouncilGluing as Council
import DASHI.Interop.LocalGlobalBundleGluingExact as Gluing
import DASHI.Governance.CouncilBundleGluingCalculusAdapterExact as Adapter

------------------------------------------------------------------------
-- RED/GREEN reference consumer: unlike the partial graph/RSA/wave adapters,
-- the existing council owner already supplies a full BundleSheaf instance,
-- compatibility witness, glue and exact restriction-back theorem.
------------------------------------------------------------------------

canonicalCouncilRestrictionViaGenericSurface :
  (point : Council.CouncilBasePoint) →
  Council.sectionAt Council.canonicalGlobalCouncilSection point
  ≡ Council.canonicalLocalCouncilFamily point
canonicalCouncilRestrictionViaGenericSurface =
  Adapter.canonicalCouncilRestrictionViaGenericSurface

canonicalCouncilUsesExistingBundleSheaf =
  Adapter.canonicalCouncilUsesExistingBundleSheaf
