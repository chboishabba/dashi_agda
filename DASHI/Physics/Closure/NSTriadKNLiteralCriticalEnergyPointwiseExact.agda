module DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyPointwiseExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S1a / LITERAL POINTWISE CRITICAL-ENERGY SPLIT
--
-- S0 now fixes one exact finite critical observable family on the live rational
-- Galerkin carrier.  Before asking for any derivative/FTC authority, isolate the
-- purely finite PDE algebra produced by the literal Round30 right-hand side.
--
-- For endpoint weight w(k), Round30 gives
--
--   u_t(k) = -nu |k|^2 u(k) + N_k(u).
--
-- Pairing with u(k), taking real part, and multiplying by 2 w(k) yields
--
--   2 w Re<u_t,u>
--     = 2 w Re<N(u),u> - 2 nu w |k|^2 |u|^2.
--
-- This file proves that identity modewise and after the literal finite mode
-- fold.  It uses no time-derivative semantics, FTC, integration linearity, or
-- estimate.  Those belong to S1b.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold

F : C3.RealField _
F = Rational.rationalRealField

modeCriticalDissipation :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Z3.FourierMode → ℚ
modeCriticalDissipation P mode =
  (Fold.dyadicCriticalWeight mode
    * C3.normSquared (R30.physicalInverseSquare P) mode)
  * L2.complex3NormSquared (Audit.velocityAt (R30.finiteSystem P) mode)

modeCriticalProduction :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Z3.FourierMode → ℚ
modeCriticalProduction P mode =
  Fold.two * Fold.dyadicCriticalWeight mode
    * Fold.realHermitianPairing
        (Audit.projectedNonlinearity (R30.finiteSystem P) mode)
        (Audit.velocityAt (R30.finiteSystem P) mode)

modeLiteralEnergyTangent :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  Z3.FourierMode → ℚ
modeLiteralEnergyTangent P mode =
  Fold.two * Fold.dyadicCriticalWeight mode
    * Fold.realHermitianPairing
        (R30.literalViscousQuadraticCoefficient P mode)
        (Audit.velocityAt (R30.finiteSystem P) mode)

literalModeCriticalEnergySplit :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (mode : Z3.FourierMode) →
  modeLiteralEnergyTangent P mode
  ≡ modeCriticalProduction P mode
      - (Fold.two * R30.viscosity P) * modeCriticalDissipation P mode
literalModeCriticalEnergySplit P mode
  with Audit.velocityAt (R30.finiteSystem P) mode
     | Audit.projectedNonlinearity (R30.finiteSystem P) mode
... | C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi)
    | C3.complex3
      (C3.complex nx nxi) (C3.complex ny nyi) (C3.complex nz nzi) =
  let
    w = Fold.dyadicCriticalWeight mode
    nu = R30.viscosity P
    k2 = C3.normSquared (R30.physicalInverseSquare P) mode
  in
  solve
    ( w ∷ nu ∷ k2
    ∷ ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi
    ∷ nx ∷ nxi ∷ ny ∷ nyi ∷ nz ∷ nzi ∷ [] )

finiteLiteralEnergyTangent :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  List Z3.FourierMode → ℚ
finiteLiteralEnergyTangent P [] = 0ℚ
finiteLiteralEnergyTangent P (mode ∷ rest) =
  modeLiteralEnergyTangent P mode + finiteLiteralEnergyTangent P rest

finiteCriticalProduction :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  List Z3.FourierMode → ℚ
finiteCriticalProduction P modes =
  Fold.two *
    Fold.weightedProjectedNonlinearProduction (R30.finiteSystem P) modes

finiteCriticalDissipation :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  List Z3.FourierMode → ℚ
finiteCriticalDissipation P modes =
  Fold.criticalViscousMass (R30.finiteSystem P) modes

literalFiniteCriticalEnergySplit :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  (modes : List Z3.FourierMode) →
  finiteLiteralEnergyTangent P modes
  ≡ finiteCriticalProduction P modes
      - (Fold.two * R30.viscosity P) * finiteCriticalDissipation P modes
literalFiniteCriticalEnergySplit P [] = solve []
literalFiniteCriticalEnergySplit P (mode ∷ rest)
  rewrite literalModeCriticalEnergySplit P mode
        | literalFiniteCriticalEnergySplit P rest =
  solve
    ( Fold.dyadicCriticalWeight mode
    ∷ Fold.realHermitianPairing
        (Audit.projectedNonlinearity (R30.finiteSystem P) mode)
        (Audit.velocityAt (R30.finiteSystem P) mode)
    ∷ modeCriticalDissipation P mode
    ∷ Fold.weightedProjectedNonlinearProduction (R30.finiteSystem P) rest
    ∷ Fold.criticalViscousMass (R30.finiteSystem P) rest
    ∷ R30.viscosity P
    ∷ [] )

literalLiveModeListCriticalEnergySplit :
  (P : R30.PhysicalFiniteComplex3GalerkinSystem F) →
  finiteLiteralEnergyTangent P (Audit.modes (R30.finiteSystem P))
  ≡ Fold.criticalProductionRate (R30.finiteSystem P)
      - (Fold.two * R30.viscosity P)
          * Fold.criticalDissipationRate (R30.finiteSystem P)
literalLiveModeListCriticalEnergySplit P =
  literalFiniteCriticalEnergySplit P (Audit.modes (R30.finiteSystem P))

literalModeCriticalEnergySplitClosed : Bool
literalModeCriticalEnergySplitClosed = true

literalFiniteCriticalEnergySplitClosed : Bool
literalFiniteCriticalEnergySplitClosed = true

pointwiseSplitUsesLiteralProjectedNonlinearity : Bool
pointwiseSplitUsesLiteralProjectedNonlinearity = true

pointwiseSplitIntroducesCalculusAuthority : Bool
pointwiseSplitIntroducesCalculusAuthority = false

integratedCriticalEnergyIdentityClosed : Bool
integratedCriticalEnergyIdentityClosed = false

literalModeCriticalEnergySplitClosedIsTrue :
  literalModeCriticalEnergySplitClosed ≡ true
literalModeCriticalEnergySplitClosedIsTrue = refl

literalFiniteCriticalEnergySplitClosedIsTrue :
  literalFiniteCriticalEnergySplitClosed ≡ true
literalFiniteCriticalEnergySplitClosedIsTrue = refl

pointwiseSplitUsesLiteralProjectedNonlinearityIsTrue :
  pointwiseSplitUsesLiteralProjectedNonlinearity ≡ true
pointwiseSplitUsesLiteralProjectedNonlinearityIsTrue = refl

pointwiseSplitIntroducesCalculusAuthorityIsFalse :
  pointwiseSplitIntroducesCalculusAuthority ≡ false
pointwiseSplitIntroducesCalculusAuthorityIsFalse = refl

integratedCriticalEnergyIdentityClosedIsFalse :
  integratedCriticalEnergyIdentityClosed ≡ false
integratedCriticalEnergyIdentityClosedIsFalse = refl
