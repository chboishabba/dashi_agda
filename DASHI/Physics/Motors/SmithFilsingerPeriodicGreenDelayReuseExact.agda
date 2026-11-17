module DASHI.Physics.Motors.SmithFilsingerPeriodicGreenDelayReuseExact where

-- Direct reuse of an ACTUAL exact finite scalar Green convolution:
-- BalabanSide4ScalarGreenConvolutionExact.scalarGreen and its
-- siteGreenLaplacianIdentity are the original owners.
-- A separate Nat delay gates source history. The kernel is a PERIODIC
-- ELLIPTIC scalar inverse on a 4D side-four torus, NOT the 3D
-- soil/air/ionosphere Maxwell dyadic retarded Green operator.
--
-- This is a useful exact operator+time interface negative/positive
-- control, not same-original Sun/Earth harvesting evidence.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Rational.Base as ℚ

import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as G
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Sites
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Axis
import DASHI.Physics.Motors.SmithFilsingerCoerciveGreenRetardedWeldExact as Retarded

private
  Field : Set
  Field = Sums.SiteField Axis.side4

  Site : Set
  Site = Sites.PhysicalBlockL Axis.side4

zeroField : Field
zeroField site = ℚ.0ℚ

-- Apply the existing exact periodic Green only after the chosen delay.
-- Earlier times return an EXACT zero field.
periodicDelayedGreen : (Nat → Field) → Nat → Nat → Field
periodicDelayedGreen source zero t = G.scalarGreen (source t)
periodicDelayedGreen source (suc delay) zero = zeroField
periodicDelayedGreen source (suc delay) (suc t) =
  periodicDelayedGreen source delay t

periodicGreenBeforeLaunchIsZero :
  (source : Nat → Field)
  (delay t : Nat) →
  Retarded.StrictEarlier t delay →
  (site : Site) →
  periodicDelayedGreen source delay t site ≡ ℚ.0ℚ
periodicGreenBeforeLaunchIsZero source (suc delay) zero
  Retarded.firstEarlier site = refl
periodicGreenBeforeLaunchIsZero source (suc delay) (suc t)
  (Retarded.shiftEarlier earlier) site =
  periodicGreenBeforeLaunchIsZero source delay t earlier site

periodicGreenAtArrival :
  (source : Nat → Field) (delay : Nat) →
  periodicDelayedGreen source delay delay ≡ G.scalarGreen (source zero)
periodicGreenAtArrival source zero = refl
periodicGreenAtArrival source (suc delay) =
  periodicGreenAtArrival source delay

-- The actual original Green inverse theorem now transfers through
-- the delayed response. This is NOT a claim of an elliptic wave front:
-- time causality came from the explicitly staged delay, not G.
delayedPeriodicGreenSolvesMeanCorrectedLaplacian :
  (source : Nat → Field) (delay : Nat) (site : Site) →
  G.siteLocalLaplacian (periodicDelayedGreen source delay delay) site
    ≡ source zero site
        ℚ.- G.oneTwoFiftySix ℚ.* G.siteSum4 (source zero)
delayedPeriodicGreenSolvesMeanCorrectedLaplacian source delay site =
  trans
    (cong (λ field → G.siteLocalLaplacian field site)
      (periodicGreenAtArrival source delay))
    (G.siteGreenLaplacianIdentity (source zero) site)

-- Physical F02/F13 needs a hyperbolic anisotropic dyadic Green in real
-- 3D, causal finite support, source/return geometry, nonlinear medium,
-- material work, calibrated current/voltage and source backreaction.
