module DASHI.Geometry.TriadicExplodedTransformCrossPollination where

-- Cross-pollination layer for the exploded-transform formalism.
--
-- This module deliberately adapts the new geometry surface to canonical repo
-- carriers rather than introducing a second competing ontology:
--
-- * SSPTritCarrier supplies the canonical typed -1/0/+1 carrier;
-- * SSP369Ultrametric supplies the checked prefix metric;
-- * SSP369TreeAutomorphism supplies the existing tree-action discipline;
-- * W9MDLTerminationSeamRoute supplies the accepted MDL/Lyapunov seam.
--
-- What is proved here is exact carrier interoperability and the shape of the
-- metric/refinement receipts required of geometric consumers.  No general
-- affine-universality, continuum convergence, or codec-rate theorem is
-- promoted by this adapter.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Geometry.SSP369TreeAutomorphism as Tree
import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Geometry.TriadicExplodedTransformTower as Tower
import DASHI.Physics.Closure.W9MDLTerminationSeamRoute as W9

------------------------------------------------------------------------
-- Canonical trit-carrier interoperability.

fromSSPTrit : SSP.SSPTrit → Tower.Trit
fromSSPTrit SSP.sspNegOne = Tower.neg
fromSSPTrit SSP.sspZero = Tower.zeroT
fromSSPTrit SSP.sspPosOne = Tower.pos

toSSPTrit : Tower.Trit → SSP.SSPTrit
toSSPTrit Tower.neg = SSP.sspNegOne
toSSPTrit Tower.zeroT = SSP.sspZero
toSSPTrit Tower.pos = SSP.sspPosOne

from-to-SSPTrit : ∀ t → fromSSPTrit (toSSPTrit t) ≡ t
from-to-SSPTrit Tower.neg = refl
from-to-SSPTrit Tower.zeroT = refl
from-to-SSPTrit Tower.pos = refl

to-from-SSPTrit : ∀ t → toSSPTrit (fromSSPTrit t) ≡ t
to-from-SSPTrit SSP.sspNegOne = refl
to-from-SSPTrit SSP.sspZero = refl
to-from-SSPTrit SSP.sspPosOne = refl

ιSSP : SSP.SSPTrit → SSP.SSPTrit
ιSSP SSP.sspNegOne = SSP.sspPosOne
ιSSP SSP.sspZero = SSP.sspZero
ιSSP SSP.sspPosOne = SSP.sspNegOne

ιSSP-involutive : ∀ t → ιSSP (ιSSP t) ≡ t
ιSSP-involutive SSP.sspNegOne = refl
ιSSP-involutive SSP.sspZero = refl
ιSSP-involutive SSP.sspPosOne = refl

fromSSPTrit-commutes-with-involution :
  ∀ t → fromSSPTrit (ιSSP t) ≡ Tower.ιT (fromSSPTrit t)
fromSSPTrit-commutes-with-involution SSP.sspNegOne = refl
fromSSPTrit-commutes-with-involution SSP.sspZero = refl
fromSSPTrit-commutes-with-involution SSP.sspPosOne = refl

toSSPTrit-commutes-with-involution :
  ∀ t → toSSPTrit (Tower.ιT t) ≡ ιSSP (toSSPTrit t)
toSSPTrit-commutes-with-involution Tower.neg = refl
toSSPTrit-commutes-with-involution Tower.zeroT = refl
toSSPTrit-commutes-with-involution Tower.pos = refl

------------------------------------------------------------------------
-- Prefix-ultrametric geometric action gate.
--
-- Exploded transforms act executablely on a state field.  To claim that a
-- selected transform is a symmetry of the existing 369 address geometry, a
-- consumer must additionally provide the following preservation receipt.

record AddressIsometryReceipt (d : Nat) : Set where
  field
    addressWarp : U369.Address d → U369.Address d
    preservesDistance :
      (x y : U369.Address d) →
      U369.distance (addressWarp x) (addressWarp y)
      ≡ U369.distance x y

open AddressIsometryReceipt public

record PrefixRefinementReceipt (d : Nat) : Set where
  field
    fineWarp : U369.Address d → U369.Address d
    preservesAgreementDepth :
      (x y : U369.Address d) →
      U369.agreementDepth (fineWarp x) (fineWarp y)
      ≡ U369.agreementDepth x y

open PrefixRefinementReceipt public

agreement-preservation-implies-isometry :
  ∀ {d : Nat} →
  PrefixRefinementReceipt d →
  AddressIsometryReceipt d
agreement-preservation-implies-isometry r =
  record
    { addressWarp = fineWarp r
    ; preservesDistance = preserves
    }
  where
    preserves :
      ∀ x y →
      U369.distance (fineWarp r x) (fineWarp r y)
      ≡ U369.distance x y
    preserves x y rewrite preservesAgreementDepth r x y = refl

------------------------------------------------------------------------
-- Combined geometric/MDL consumer surface.

private
  variable
    ℓG ℓC : Level

record CrossPollinatedGeometricChart
  (G : Set ℓG)
  (C : Set ℓC)
  (d : Nat) : Set (lsuc (ℓG ⊔ ℓC)) where
  field
    control : Tower.GeometricControl G
    addressGeometry : AddressIsometryReceipt d

    -- A chart which claims coarse/fine compatibility must supply the actual
    -- scale map; this adapter does not manufacture one from metric data alone.
    FineSystem : Tower.ScaleSystem {ℓG} {ℓC} {ℓG}
    CoarseSystem : Tower.ScaleSystem {ℓG} {ℓC} {ℓG}
    scaleCompatibility : Tower.ScaleMap FineSystem CoarseSystem

    -- The repository's current accepted W9 route is retained as provenance.
    -- It is an MDL termination seam, not a proof that this geometric chart
    -- decreases the same functional.
    currentMDLRouteStatus : W9.W9MDLTerminationSeamRouteStatus
    currentMDLRouteStatusIsCanonical :
      currentMDLRouteStatus ≡ W9.currentW9MDLTerminationSeamStatus

------------------------------------------------------------------------
-- Live provenance witnesses.

canonicalSSPTritCarrierIsAvailable : SSP.SSPTritCarrierReceipt
canonicalSSPTritCarrierIsAvailable = SSP.canonicalSSPTritCarrierReceipt

currentW9MDLRouteIsAvailable : W9.W9MDLTerminationSeamRouteStatus
currentW9MDLRouteIsAvailable = W9.currentW9MDLTerminationSeamStatus

-- This typed reference ensures the existing tree-automorphism theorem remains
-- a live dependency of the cross-pollinated lane.  It records prefix
-- commutation for the canonical p7 action; it does not identify the distinct
-- address carriers without an explicit adapter.
p7TreePrefixCommutationIsAvailable =
  Tree.p7CanonicalThreeSixNinePrefixCommutes
