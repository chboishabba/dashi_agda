module DASHI.Mathematics.Symmetry.NoetherDiscreteVariationalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Emmy Noether,
-- "Invariante Variationsprobleme" (1918).
-- No DOI was assigned to the original publication.
-- M. A. Tavel translation, "Invariant Variation Problems":
-- DOI: 10.48550/arXiv.physics/0503066.
--
-- J. E. Marsden and M. West,
-- "Discrete mechanics and variational integrators",
-- Acta Numerica 10 (2001), 357--514.
-- DOI: 10.1017/S096249290100006X.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact algebraic core of one discrete Noether transport step.
-- Contracting the discrete Euler--Lagrange equation with an infinitesimal
-- symmetry gives
--
--   incomingMomentum + firstVariation = eulerResidual.
--
-- Invariance of the current discrete Lagrangian edge gives
--
--   firstVariation + outgoingMomentum = symmetryResidual.
--
-- Eliminating the shared first-variation term yields
--
--   outgoingMomentum - incomingMomentum
--     = symmetryResidual - eulerResidual.
--
-- In the exact on-shell invariant case both residuals vanish and momentum is
-- conserved.  The residual theorem is exported directly as the common
-- Noether dissipation/defect ledger used by the PDE bridge modules.
--
-- This module proves the displayed cancellation over exact rationals.  It does
-- not construct a configuration manifold, differentiable group action,
-- discrete Lagrangian, Euler--Lagrange derivative or momentum map.  Those data
-- must instantiate the typed step record separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Symmetry.NoetherDissipationDefectExact as N

discreteNoetherConservation :
  ∀ incomingMomentum firstVariation outgoingMomentum →
  incomingMomentum + firstVariation ≡ 0ℚ →
  firstVariation + outgoingMomentum ≡ 0ℚ →
  incomingMomentum ≡ outgoingMomentum
discreteNoetherConservation
    incomingMomentum firstVariation outgoingMomentum
    eulerLagrangeIdentity symmetryIdentity =
  trans
    (solve (incomingMomentum ∷ firstVariation ∷ []))
    (trans
      (cong (λ value → value + (- firstVariation))
        eulerLagrangeIdentity)
      (trans
        (cong (λ value → value + (- firstVariation))
          (sym symmetryIdentity))
        (solve (firstVariation ∷ outgoingMomentum ∷ []))))

discreteNoetherDefect :
  ∀ incomingMomentum firstVariation outgoingMomentum
    eulerResidual symmetryResidual →
  incomingMomentum + firstVariation ≡ eulerResidual →
  firstVariation + outgoingMomentum ≡ symmetryResidual →
  outgoingMomentum - incomingMomentum
  ≡ symmetryResidual - eulerResidual
discreteNoetherDefect
    incomingMomentum firstVariation outgoingMomentum
    eulerResidual symmetryResidual
    eulerLagrangeIdentity symmetryIdentity =
  trans
    (solve
      (incomingMomentum ∷ firstVariation ∷ outgoingMomentum ∷ []))
    (cong₂ _-_ symmetryIdentity eulerLagrangeIdentity)

record DiscreteVariationalNoetherStep : Set where
  constructor discreteNoetherStep
  field
    incomingMomentum : ℚ
    contractedFirstVariation : ℚ
    outgoingMomentum : ℚ
    eulerResidual : ℚ
    symmetryResidual : ℚ
    contractedEulerLagrangeIdentity :
      incomingMomentum + contractedFirstVariation ≡ eulerResidual
    contractedSymmetryIdentity :
      contractedFirstVariation + outgoingMomentum ≡ symmetryResidual

open DiscreteVariationalNoetherStep public

stepMomentumDefect : ∀ step →
  outgoingMomentum step - incomingMomentum step
  ≡ symmetryResidual step - eulerResidual step
stepMomentumDefect step =
  discreteNoetherDefect
    (incomingMomentum step)
    (contractedFirstVariation step)
    (outgoingMomentum step)
    (eulerResidual step)
    (symmetryResidual step)
    (contractedEulerLagrangeIdentity step)
    (contractedSymmetryIdentity step)

stepDefectLedger :
  DiscreteVariationalNoetherStep → N.DefectLedger
stepDefectLedger step =
  N.defectLedger
    (outgoingMomentum step - incomingMomentum step)
    0ℚ
    (symmetryResidual step - eulerResidual step)
    (trans
      (solve
        (outgoingMomentum step ∷ incomingMomentum step ∷ []))
      (stepMomentumDefect step))

exactStepConservesMomentum : ∀ step →
  eulerResidual step ≡ 0ℚ →
  symmetryResidual step ≡ 0ℚ →
  incomingMomentum step ≡ outgoingMomentum step
exactStepConservesMomentum step eulerZero symmetryZero =
  discreteNoetherConservation
    (incomingMomentum step)
    (contractedFirstVariation step)
    (outgoingMomentum step)
    (trans
      (contractedEulerLagrangeIdentity step)
      eulerZero)
    (trans
      (contractedSymmetryIdentity step)
      symmetryZero)

record DiscreteNoetherInstantiation : Set₁ where
  field
    Configuration : Set
    SymmetryGenerator : Set
    DiscreteLagrangianData : Set
    FirstSlotDerivativeData : Set
    SecondSlotDerivativeData : Set
    MomentumMapData : Set
    contractedStep :
      Configuration → Configuration → Configuration →
      SymmetryGenerator → DiscreteVariationalNoetherStep

-- DiscreteNoetherInstantiation names the geometric input required to obtain a
-- concrete step.  The exact cancellation theorem starts only after those data
-- produce the two displayed rational identities.
