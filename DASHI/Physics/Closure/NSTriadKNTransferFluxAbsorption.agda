module DASHI.Physics.Closure.NSTriadKNTransferFluxAbsorption where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalEdgeTransferOperator as Edge
import DASHI.Physics.Closure.NSTriadKNWeightedEdgeYoungControl as Young
import DASHI.Physics.Closure.NSTriadKNWeightedFourierEnergyIdentity as Energy

------------------------------------------------------------------------
-- The decisive PDE gate after the exact bilinear identity.
--
-- This is intentionally a new controller: the first term comes from an
-- independently positive coercive edge weight W, while the second is the
-- exact dual transfer-flux norm.  It must not be identified with Lneg/Labs.
-- A state-independent W cannot generally make the flux term globally
-- absorbable by quadratic viscous dissipation: modal transfers are cubic in
-- u, so the dual squared norm is degree six while viscous dissipation is
-- degree two.  Any future inhabitant must make its normalisation or auxiliary
-- energy hierarchy explicit.
------------------------------------------------------------------------

record TransferFluxAbsorption
    (S : Scalar.ExactOrderedScalar) (W : Young.PositiveEdgeWeightAuthority S)
    (M : Nat) (T : Energy.ZeroSumTriadTransferField S)
    (triads : List Energy.ZeroSumTriad) : Set₁ where
  field
    baseDissipation : Scalar.Scalar S
    lowerOrder : Scalar.Scalar S
    absorptionFactor : Scalar.Scalar S
    strictSubcritical : Set

    transferFluxAbsorbed :
      Young._≤_ W
        (Energy.sumScalarList S
          (fluxTerms triads))
        (Scalar._+_ S
          (Scalar._*_ S absorptionFactor baseDissipation)
          lowerOrder)
  where
  fluxTerms : List Energy.ZeroSumTriad → List (Scalar.Scalar S)
  fluxTerms [] = []
  fluxTerms (σ ∷ σs) =
    Young.edgeTransferFluxDualNorm S W
      (Edge.modalTransferEdgeDifference S T σ) ∷ fluxTerms σs

open TransferFluxAbsorption public

-- No finite Fourier/viscous estimate currently inhabits this target.  The
-- diagnostic scripts rule out deriving it by replacing W with the old
-- one-output mMinus or mAbs coefficient, and also rule out an unnormalised
-- state-independent W against viscous dissipation alone.  The next proof must
-- choose a state-dependent/coercivity-normalised W or supply an additional
-- energy hierarchy, then prove this inequality with a strict factor.
transferFluxAbsorptionClosed : Bool
transferFluxAbsorptionClosed = false
