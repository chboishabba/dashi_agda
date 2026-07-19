module DASHI.Core.NumberTheoreticInterconnectionAdapter where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ComparisonLawCore as Comparison
import DASHI.Core.FibreRestrictionCore as Restriction

------------------------------------------------------------------------
-- Number-theoretic instance grammar.
--
-- A residue/chart observation narrows a hidden factor or coordinate fibre but
-- does not recover the hidden object.  CRT compatibility, p-adic proximity,
-- and factor-chart evidence may refine the fibre; none promotes recovery by
-- itself.
------------------------------------------------------------------------

record ResidueProjectionSystem : Set₁ where
  constructor residueProjectionSystem
  field
    HiddenCarrier : Set
    ResidueChart  : Set
    Evidence      : Set
    project       : HiddenCarrier → ResidueChart
    Fibre         : ResidueChart → Set
    compatible    : ResidueChart → ResidueChart → Set
    restricts     : Evidence → ResidueChart → Set

open ResidueProjectionSystem public

residueComparisonCore :
  ResidueProjectionSystem → Comparison.ComparisonLawCore
residueComparisonCore system =
  Comparison.comparisonLawCore
    (HiddenCarrier system)
    (HiddenCarrier system)
    (ResidueChart system)
    (project system)
    (project system)
    (λ left right → compatible system left right)
    (compatible system)
    true

residueFibreRestrictionCore :
  ResidueProjectionSystem → Restriction.FibreRestrictionCore
residueFibreRestrictionCore system =
  Restriction.fibreRestrictionCore
    (HiddenCarrier system)
    (ResidueChart system)
    (Evidence system)
    (project system)
    (Fibre system)
    (restricts system)
    true
    false

residueEvidenceDoesNotRecoverCarrier :
  (system : ResidueProjectionSystem) →
  Restriction.doesNotRecoverCarrier
    (residueFibreRestrictionCore system) ≡ true
residueEvidenceDoesNotRecoverCarrier system = refl

residueEvidenceDoesNotPromoteTruth :
  (system : ResidueProjectionSystem) →
  Restriction.promotesTruth
    (residueFibreRestrictionCore system) ≡ false
residueEvidenceDoesNotPromoteTruth system = refl
