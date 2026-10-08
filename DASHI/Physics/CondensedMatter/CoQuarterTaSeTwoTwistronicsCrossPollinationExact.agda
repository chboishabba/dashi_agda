module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoTwistronicsCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Physics.CondensedMatter.FlatBandTwistronicsFe5GeTe2CrossPollinationExact as FlatTwist
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBlochRepresentationBoundaryExact as CoBloch

------------------------------------------------------------------------
-- STRUCTURAL CROSS-POLLINATION ONLY
--
-- Twistronics and the Co1/4TaSe2 altermagnet lane both require an observer to
-- retain a symmetry/registration coordinate that a coarser energy label can
-- erase.  The microscopic mechanisms are not identified: twist-angle moire
-- registration is not magnetic sublattice exchange, and the Co compound is not
-- being promoted to a twisted heterostructure.
------------------------------------------------------------------------

record RegistrationSymmetryCrossPollination : Set where
  constructor registration-symmetry-cross-pollination
  field
    relativeCoordinateCanAffectEffectiveObservable : Bool
    coarseEnergyCanLoseMechanismRelevantInformation : Bool
    twistronicsRegistrationEqualsMagneticSublatticeExchange : Bool
    magicAngleMechanismTransferredToCoQuarterTaSeTwo : Bool
    sameObjectAcrossMaterialsClaimed : Bool

canonicalRegistrationSymmetryCrossPollination :
  RegistrationSymmetryCrossPollination
canonicalRegistrationSymmetryCrossPollination =
  registration-symmetry-cross-pollination
    true true false false false

-- Consume the existing attributed twistronics source atlas rather than copying
-- its external claims into this material lane.
existingTwistronicsSourceAtlas = Twist.twistronicsSourceAtlas

-- Consume the existing mechanism-neutral theorem architecture only.
existingFlatBandCrossPollinationBoundary =
  FlatTwist.canonicalGrapheneFe5GeTe2CrossPollinationBoundary

-- The Co material-Hamiltonian leaf remains whatever the Co lane itself says;
-- cross-pollination cannot promote it.
existingCoMaterialHamiltonianStatus : CoBloch.MaterialHamiltonianStatus
existingCoMaterialHamiltonianStatus = CoBloch.canonicalMaterialHamiltonianStatus
