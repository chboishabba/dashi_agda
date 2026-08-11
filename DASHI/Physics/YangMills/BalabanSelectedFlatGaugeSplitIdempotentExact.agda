module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeSplitIdempotentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Expose the already-constructed flat based representative as the actual
-- split-idempotent projector carried by the selected 768-coordinate gauge
-- multiplier space.  The projector is based, idempotent, orbit-equivalent to
-- its input, and fixes exactly the based representatives.  The existing unit
-- constant witness proves that it is not the identity on the unreduced
-- carrier.
--
-- This is deliberately the flat constant-shift quotient.  It is not promoted
-- to a nonlinear selected-background gauge slice: the Round-42 holonomy
-- theorem proves that the physical stabilizer type changes with background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (0ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeBasedSectionExact as Based
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeSectionAsymmetryExact as Asymmetry

selectedBasedGaugeProjection : Based.GaugeMultiplier → Based.GaugeMultiplier
selectedBasedGaugeProjection = Based.basedRepresentative

selectedBasedGaugeProjectionBased : ∀ multiplier →
  Based.BasedGaugeMultiplier (selectedBasedGaugeProjection multiplier)
selectedBasedGaugeProjectionBased = Based.basedRepresentativeIsBased

selectedBasedGaugeProjectionIdempotent : ∀ multiplier coordinate site →
  selectedBasedGaugeProjection (selectedBasedGaugeProjection multiplier)
    (pair coordinate site)
  ≡ selectedBasedGaugeProjection multiplier (pair coordinate site)
selectedBasedGaugeProjectionIdempotent =
  Based.basedRepresentativeIdempotentPointwise

selectedBasedGaugeProjectionOrbitEquivalent : ∀ multiplier →
  Based.FlatConstantGaugeEquivalent
    multiplier (selectedBasedGaugeProjection multiplier)
selectedBasedGaugeProjectionOrbitEquivalent = Based.originalEquivalentToBased

selectedBasedGaugeProjectionFixesBased :
  ∀ multiplier →
  Based.BasedGaugeMultiplier multiplier →
  ∀ coordinate site →
  selectedBasedGaugeProjection multiplier (pair coordinate site)
  ≡ multiplier (pair coordinate site)
selectedBasedGaugeProjectionFixesBased multiplier based coordinate site
  rewrite based coordinate =
  ℚRing.solve-∀ (multiplier (pair coordinate site))

selectedBasedGaugeProjectionFixedImpliesBased :
  ∀ multiplier →
  (∀ coordinate site →
    selectedBasedGaugeProjection multiplier (pair coordinate site)
    ≡ multiplier (pair coordinate site)) →
  Based.BasedGaugeMultiplier multiplier
selectedBasedGaugeProjectionFixedImpliesBased multiplier fixed coordinate =
  trans
    (sym (fixed coordinate Based.baseSite))
    (Based.basedRepresentativeAtBase multiplier coordinate)

selectedBasedGaugeProjectionFixedIffBasedForward :
  ∀ multiplier →
  Based.BasedGaugeMultiplier multiplier →
  ∀ coordinate site →
  selectedBasedGaugeProjection multiplier (pair coordinate site)
  ≡ multiplier (pair coordinate site)
selectedBasedGaugeProjectionFixedIffBasedForward =
  selectedBasedGaugeProjectionFixesBased

selectedBasedGaugeProjectionFixedIffBasedBackward :
  ∀ multiplier →
  (∀ coordinate site →
    selectedBasedGaugeProjection multiplier (pair coordinate site)
    ≡ multiplier (pair coordinate site)) →
  Based.BasedGaugeMultiplier multiplier
selectedBasedGaugeProjectionFixedIffBasedBackward =
  selectedBasedGaugeProjectionFixedImpliesBased

selectedBasedGaugeProjectionNotIdentity :
  ¬ (∀ row →
    selectedBasedGaugeProjection Asymmetry.unitConstantMultiplier row
    ≡ Asymmetry.unitConstantMultiplier row)
selectedBasedGaugeProjectionNotIdentity =
  Asymmetry.basedSectionNotIdentityOnUnreducedCarrier

selectedFlatGaugeSplitIdempotentLevel : ProofLevel
selectedFlatGaugeSplitIdempotentLevel = machineChecked
