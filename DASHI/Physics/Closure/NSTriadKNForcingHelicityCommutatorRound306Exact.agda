module DASHI.Physics.Closure.NSTriadKNForcingHelicityCommutatorRound306Exact where

------------------------------------------------------------------------
-- ROUND306 / THE R230 NONLINEAR FORCING IS A HELICITY COMMUTATOR
--
-- R305 proves that heat/resolvent damping alone does not improve the critical
-- shoulder exponents.  The next forward structure must therefore come from
-- the signed forcing itself.
--
-- R230's authoritative cell is
--
--   G_p+ x u_q- - G_p- x u_q+.
--
-- R223 already proves the generic algebra
--
--   (H a) x b - a x (H b)
--     = 2 (a+ x b- - a- x b+).
--
-- This file welds those two objects exactly.  No scalar multiplier-difference
-- theorem from R120 is imported: R230 is a helicity commutator, not generically
-- a (mu_q-mu_p) commutator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuadraticKernelRound223Exact as R223
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230

forcingMixedDifference :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
forcingMixedDifference {E = E} {I = I} S velocity forcing tau =
  R223.mixedHelicityDifference
    (Helical.helicalProjectorPlus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorPlus E I S
      (Physical.q tau) (velocity (Physical.q tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.q tau) (velocity (Physical.q tau)))

r230CellIsMixedDifference :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  R230.forcingCommutatorCell S velocity forcing tau
  ≡ forcingMixedDifference S velocity forcing tau
r230CellIsMixedDifference S velocity forcing tau = refl

doubleR230Cell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
doubleR230Cell S velocity forcing tau =
  C3.complex3Add
    (R230.forcingCommutatorCell S velocity forcing tau)
    (R230.forcingCommutatorCell S velocity forcing tau)

helicityCommutatorCell :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
helicityCommutatorCell {E = E} {I = I} S velocity forcing tau =
  R223.helicitySlotDifference
    (Helical.helicalProjectorPlus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.p tau) (forcing (Physical.p tau)))
    (Helical.helicalProjectorPlus E I S
      (Physical.q tau) (velocity (Physical.q tau)))
    (Helical.helicalProjectorMinus E I S
      (Physical.q tau) (velocity (Physical.q tau)))

doubleR230CellIsHelicityCommutator :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity forcing : Z3.FourierMode → C3.Complex3 F)
    (tau : Physical.PhysicalTriadIncidence) →
  doubleR230Cell S velocity forcing tau
  ≡ helicityCommutatorCell S velocity forcing tau
doubleR230CellIsHelicityCommutator {F = F} S velocity forcing tau =
  let
    pPlus = Helical.helicalProjectorPlus _ _ S
      (Physical.p tau) (forcing (Physical.p tau))
    pMinus = Helical.helicalProjectorMinus _ _ S
      (Physical.p tau) (forcing (Physical.p tau))
    qPlus = Helical.helicalProjectorPlus _ _ S
      (Physical.q tau) (velocity (Physical.q tau))
    qMinus = Helical.helicalProjectorMinus _ _ S
      (Physical.q tau) (velocity (Physical.q tau))
  in
  Field.symmetryAdapter
    (R223.helicitySlotDifferenceIsDoubleMixedHelicity
      pPlus pMinus qPlus qMinus)
  where
  -- Tiny orientation adapter: R223 states H-slot = double-mixed; R306 needs
  -- double-mixed = H-slot.  Kept local so no new algebraic authority appears.
  module Dummy where

round306R230CellIsLiteralMixedHelicityDifference : Bool
round306R230CellIsLiteralMixedHelicityDifference = true

round306R230CellHasExactHelicityCommutatorForm : Bool
round306R230CellHasExactHelicityCommutatorForm = true

round306R120ScalarMultiplierDifferenceImported : Bool
round306R120ScalarMultiplierDifferenceImported = false

round306PhysicalNSHelicityCommutatorEstimateClosed : Bool
round306PhysicalNSHelicityCommutatorEstimateClosed = false

round306PackageAClosed : Bool
round306PackageAClosed = false

round306ClayPromotion : Bool
round306ClayPromotion = false
