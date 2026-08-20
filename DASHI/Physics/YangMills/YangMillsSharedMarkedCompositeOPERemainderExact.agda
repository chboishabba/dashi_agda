module DASHI.Physics.YangMills.YangMillsSharedMarkedCompositeOPERemainderExact where

------------------------------------------------------------------------
-- ROUND83: SHARED MARKED COMPOSITE TAIL -> LITERAL DYADIC OPE REMAINDER TYPE
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Perturbative Field Theory",
-- Communications in Mathematical Physics 313 (2012), 257--290.
-- DOI: 10.1007/s00220-012-1457-4.
--
-- Stefan Hollands,
-- "The Operator Product Expansion for Perturbative Quantum Field Theory in
-- Curved Spacetime", Communications in Mathematical Physics 273 (2007), 1--36.
-- DOI: 10.1007/s00220-007-0230-6.
--
-- AUTHORITY BOUNDARY
--
-- These papers establish rigorous perturbative OPE remainder control, not the
-- nonperturbative four-dimensional Yang--Mills result.  The new physical input
-- remains the source-native marked composite estimate in the actual Balaban
-- continuum family.
--
-- DASHI CONTRIBUTION
--
-- Round83's shared marked shell already proves, uniformly in the terminal
-- finite cutoff count k,
--
--   compositeTail(n,k) <= C * (1/2) * 2^{-n}.
--
-- This file proves that this is EXACTLY the repository's existing
-- `DyadicOPERemainderMajorant`, with OPE coefficient C/2.  The tail is also
-- proved nonnegative from the nonnegative composite increments.  Hence no
-- second "OPE remainder decays" lemma remains after the physical composite
-- insertion has been identified with the shared marked activity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Cauchy
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

scaleIncrementTailNonnegative :
  (majorant : Cauchy.ScaleLocalIncrementMajorant) → ∀ start count →
  0ℚ ≤ Cauchy.scaleIncrementTail majorant start count
scaleIncrementTailNonnegative majorant start zero = ℚP.≤-refl
scaleIncrementTailNonnegative majorant start (suc count) =
  let
    summed = ℚP.+-mono-≤
      (Cauchy.incrementNonnegative majorant start)
      (scaleIncrementTailNonnegative majorant (suc start) count)
  in
  subst
    (λ lower →
      lower ≤ Cauchy.incrementMagnitude majorant start
        + Cauchy.scaleIncrementTail majorant (suc start) count)
    (ℚRing.solve [])
    summed

sharedCompositeAsDyadicOPERemainder :
  ∀ {Scale Volume Root}
    (shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root)
    (scale : Scale) (volume : Volume) (root : Root)
    -- `remaining depth` is the number of finite cutoff shells still present
    -- after the OPE is truncated at `depth`.  The theorem is uniform in it.
    (remaining : Nat → Nat) →
  Local.DyadicOPERemainderMajorant
sharedCompositeAsDyadicOPERemainder shared scale volume root remaining = record
  { Local.DyadicOPERemainderMajorant.coefficient =
      Shared.analyticConstant shared * Geo.half
  ; Local.DyadicOPERemainderMajorant.coefficientNonnegative =
      Weighted.productNonnegative
        (Shared.analyticConstant shared) Geo.half
        (Shared.analyticConstantNonnegative shared) Geo.halfNonnegative
  ; Local.DyadicOPERemainderMajorant.remainderMagnitude =
      λ depth → Shared.compositeInsertionTail
        shared scale volume root depth (remaining depth)
  ; Local.DyadicOPERemainderMajorant.remainderNonnegative =
      λ depth → scaleIncrementTailNonnegative
        (Shared.compositeScaleMajorant shared scale volume root)
        depth (remaining depth)
  ; Local.DyadicOPERemainderMajorant.remainderBelowDyadic =
      λ depth →
        subst
          (λ upper →
            Shared.compositeInsertionTail
              shared scale volume root depth (remaining depth)
            ≤ upper)
          (ℚRing.solve-∀
            (Shared.analyticConstant shared)
            Geo.half
            (Geo.halfPower depth))
          (Shared.compositeInsertionTailVanishingModulus
            shared scale volume root depth (remaining depth))
  }

sharedMarkedCompositeOPERemainderCompilerLevel : ProofLevel
sharedMarkedCompositeOPERemainderCompilerLevel = machineChecked

-- Remaining C1 physics after this bridge:
--   (1) construct/renormalize the actual gauge-invariant curvature-composite
--       insertion on the SAME continuum family;
--   (2) prove that its RG remainder is the shared composite tail above;
--   (3) identify the short-distance OPE coefficients with the asymptotically
--       free Yang--Mills coefficients.
-- The pure decay-to-zero theorem is no longer independent.
physicalSameFamilyCompositeOPEIdentificationLevel : ProofLevel
physicalSameFamilyCompositeOPEIdentificationLevel = conditional
