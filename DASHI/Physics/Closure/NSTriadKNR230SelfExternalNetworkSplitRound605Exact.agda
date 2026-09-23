{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact where

------------------------------------------------------------------------
-- ROUND605 / R230 MIXED-HELICITY FORCING = SELF + EXTERNAL NETWORK
--
-- R604 isolates the remaining proposed exact A3/Cauchy consumer bridge as
--
--   rateTotal * ForcingFull = 4 * A3.
--
-- R599's cyclic audit shows that full projected Galerkin forcing is not a
-- closed three-leg system: selected-triad self forcing is energy conservative,
-- while the external network must be retained.
--
-- This owner pushes that SAME physical self/external split through the actual
-- R230 mixed-helicity product-rule forcing, before any scalar estimate:
--
--   R230FullCell(tau) = R230SelfCell(tau) + R230ExternalCell(tau),
--
-- and then over the literal fixed-output fibre.
--
-- The proof uses only:
--   * R95 full = self + external on the literal p/q modal forcing slots;
--   * linearity of P^+ and P^- (R82 Leray additivity + R157 curl additivity);
--   * bilinearity of the vector cross product (R94);
--   * finite fold additivity already used by R230.
--
-- No cyclic-energy identification, estimate, norm, or sign claim is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact as R157
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as R82
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNHelicalDampedProjectorLinearityRound381Exact as R381

F : C3.RealField _
F = Rational.rationalRealField

module FixedSystem
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocityAt system
  fullForcing = Audit.projectedNonlinearity system
  cutoff = Audit.cutoff system

  ----------------------------------------------------------------------
  -- Helical projector additivity, assembled only from existing linear maps.
  ----------------------------------------------------------------------

  plusProjectorAdd :
    (mode : Z3.FourierMode) (left right : C3.Complex3 F) →
    Helical.helicalProjectorPlus E I S mode
      (C3.complex3Add left right)
    ≡
    C3.complex3Add
      (Helical.helicalProjectorPlus E I S mode left)
      (Helical.helicalProjectorPlus E I S mode right)
  plusProjectorAdd mode left right =
    let
      h = C3.realEmbed F (Helical.half S)
      lL = C3.lerayProject3 E I mode left
      lR = C3.lerayProject3 E I mode right
      cL = R142.normalizedCurl E S mode left
      cR = R142.normalizedCurl E S mode right
    in
    trans
      (cong
        (C3.complex3Scale h)
        (cong₂ C3.complex3Add
          (R82.lerayProjectAdd E I mode left right)
          (R157.normalizedCurlAdd E S mode left right)))
      (trans
        (cong
          (C3.complex3Scale h)
          (R230.complex3Shuffle lL lR cL cR))
        (R157.complex3ScaleAdd h
          (C3.complex3Add lL cL)
          (C3.complex3Add lR cR)))

  minusProjectorAdd :
    (mode : Z3.FourierMode) (left right : C3.Complex3 F) →
    Helical.helicalProjectorMinus E I S mode
      (C3.complex3Add left right)
    ≡
    C3.complex3Add
      (Helical.helicalProjectorMinus E I S mode left)
      (Helical.helicalProjectorMinus E I S mode right)
  minusProjectorAdd mode left right =
    let
      h = C3.realEmbed F (Helical.half S)
      one = C3.complexOne F
      lL = C3.lerayProject3 E I mode left
      lR = C3.lerayProject3 E I mode right
      cL = R142.normalizedCurl E S mode left
      cR = R142.normalizedCurl E S mode right

      insertOnes :
        C3.complex3Subtract
          (C3.complex3Add lL lR)
          (C3.complex3Add cL cR)
        ≡
        C3.complex3Subtract
          (C3.complex3Add (C3.complex3Scale one lL) lR)
          (C3.complex3Add (C3.complex3Scale one cL) cR)
      insertOnes =
        cong₂ C3.complex3Subtract
          (cong₂ C3.complex3Add (sym (R106.complex3ScaleOne lL)) refl)
          (cong₂ C3.complex3Add (sym (R106.complex3ScaleOne cL)) refl)
    in
    trans
      (cong
        (C3.complex3Scale h)
        (cong₂ C3.complex3Subtract
          (R82.lerayProjectAdd E I mode left right)
          (R157.normalizedCurlAdd E S mode left right)))
      (trans
        (cong (C3.complex3Scale h) insertOnes)
        (trans
          (R381.minusRegroup
            h one lL cL lR cR)
          (cong₂ C3.complex3Add
            (R106.complex3ScaleOne
              (C3.complex3Scale h (C3.complex3Subtract lL cL)))
            refl)))

  ----------------------------------------------------------------------
  -- Literal R230 full/self/external cells on one physical incidence.
  ----------------------------------------------------------------------

  fullProductRuleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  fullProductRuleCell =
    R230.productRuleForcingCell S velocity fullForcing

  selfProductRuleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfProductRuleCell tau =
    C3.complex3Add
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau) (R95.selfForcingP system tau))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau) (velocity (Physical.q tau))))
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau) (velocity (Physical.p tau)))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau) (R95.selfForcingQ system tau)))

  externalProductRuleCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalProductRuleCell tau =
    C3.complex3Add
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau) (R95.externalForcingP system tau))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau) (velocity (Physical.q tau))))
      (Cross.complex3Cross
        (Helical.helicalProjectorPlus E I S
          (Physical.p tau) (velocity (Physical.p tau)))
        (Helical.helicalProjectorMinus E I S
          (Physical.q tau) (R95.externalForcingQ system tau)))

  fullProductRuleCellSplitsSelfExternal :
    (tau : Physical.PhysicalTriadIncidence) →
    fullProductRuleCell tau
    ≡ C3.complex3Add
        (selfProductRuleCell tau)
        (externalProductRuleCell tau)
  fullProductRuleCellSplitsSelfExternal tau
    rewrite R95.fullPIsSelfPlusExternal system tau
          | R95.fullQIsSelfPlusExternal system tau =
    let
      p = Physical.p tau
      q = Physical.q tau

      selfP =
        Helical.helicalProjectorPlus E I S p
          (R95.selfForcingP system tau)
      extP =
        Helical.helicalProjectorPlus E I S p
          (R95.externalForcingP system tau)
      velQ =
        Helical.helicalProjectorMinus E I S q (velocity q)

      velP =
        Helical.helicalProjectorPlus E I S p (velocity p)
      selfQ =
        Helical.helicalProjectorMinus E I S q
          (R95.selfForcingQ system tau)
      extQ =
        Helical.helicalProjectorMinus E I S q
          (R95.externalForcingQ system tau)

      first :
        Cross.complex3Cross
          (Helical.helicalProjectorPlus E I S p
            (C3.complex3Add
              (R95.selfForcingP system tau)
              (R95.externalForcingP system tau)))
          velQ
        ≡ C3.complex3Add
            (Cross.complex3Cross selfP velQ)
            (Cross.complex3Cross extP velQ)
      first =
        trans
          (cong
            (λ projected → Cross.complex3Cross projected velQ)
            (plusProjectorAdd p
              (R95.selfForcingP system tau)
              (R95.externalForcingP system tau)))
          (R94.crossAddLeft selfP extP velQ)

      second :
        Cross.complex3Cross velP
          (Helical.helicalProjectorMinus E I S q
            (C3.complex3Add
              (R95.selfForcingQ system tau)
              (R95.externalForcingQ system tau)))
        ≡ C3.complex3Add
            (Cross.complex3Cross velP selfQ)
            (Cross.complex3Cross velP extQ)
      second =
        trans
          (cong
            (Cross.complex3Cross velP)
            (minusProjectorAdd q
              (R95.selfForcingQ system tau)
              (R95.externalForcingQ system tau)))
          (R94.crossAddRight velP selfQ extQ)
    in
    trans
      (cong₂ C3.complex3Add first second)
      (R230.complex3Shuffle
        (Cross.complex3Cross selfP velQ)
        (Cross.complex3Cross extP velQ)
        (Cross.complex3Cross velP selfQ)
        (Cross.complex3Cross velP extQ))

  ----------------------------------------------------------------------
  -- Finite fixed-output lift.
  ----------------------------------------------------------------------

  foldCongruent :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldCongruent left right pointwise [] = refl
  foldCongruent left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldCongruent left right pointwise rest)

  fixedOutputFullProductRuleSplitsSelfExternal :
    (output : Z3.FourierMode) →
    let fibre = Output.physicalOutputFiber cutoff output
    in
    R224.foldVector fullProductRuleCell fibre
    ≡
    C3.complex3Add
      (R224.foldVector selfProductRuleCell fibre)
      (R224.foldVector externalProductRuleCell fibre)
  fixedOutputFullProductRuleSplitsSelfExternal output =
    let fibre = Output.physicalOutputFiber cutoff output
        summed = λ tau →
          C3.complex3Add
            (selfProductRuleCell tau)
            (externalProductRuleCell tau)
    in
    trans
      (foldCongruent
        fullProductRuleCell summed
        fullProductRuleCellSplitsSelfExternal
        fibre)
      (R230.foldAdd selfProductRuleCell externalProductRuleCell fibre)

  fixedOutputFullCommutatorIsSelfPlusExternal :
    (output : Z3.FourierMode) →
    let fibre = Output.physicalOutputFiber cutoff output
    in
    R224.foldVector
      (R230.forcingCommutatorCell S velocity fullForcing) fibre
    ≡
    C3.complex3Add
      (R224.foldVector selfProductRuleCell fibre)
      (R224.foldVector externalProductRuleCell fibre)
  fixedOutputFullCommutatorIsSelfPlusExternal output =
    trans
      (sym
        (R230.fixedOutputProductRuleForcingIsMixedCommutator
          S velocity fullForcing cutoff output))
      (fixedOutputFullProductRuleSplitsSelfExternal output)

------------------------------------------------------------------------
-- Status / source-facing interpretation.
------------------------------------------------------------------------

round605HelicalProjectorAdditivityClosed : Bool
round605HelicalProjectorAdditivityClosed = true

round605R230CellSelfExternalSplitClosed : Bool
round605R230CellSelfExternalSplitClosed = true

round605R230FixedOutputSelfExternalSplitClosed : Bool
round605R230FixedOutputSelfExternalSplitClosed = true

round605R230FullCommutatorSelfExternalSplitClosed : Bool
round605R230FullCommutatorSelfExternalSplitClosed = true

round605IntroducesEstimate : Bool
round605IntroducesEstimate = false

round605SelfPartCancelsByCyclicEnergyConservation : Bool
round605SelfPartCancelsByCyclicEnergyConservation = false

round605ExternalNetworkPartPaid : Bool
round605ExternalNetworkPartPaid = false

round605R230CellSelfExternalSplitClosedIsTrue :
  round605R230CellSelfExternalSplitClosed ≡ true
round605R230CellSelfExternalSplitClosedIsTrue = refl

round605R230FixedOutputSelfExternalSplitClosedIsTrue :
  round605R230FixedOutputSelfExternalSplitClosed ≡ true
round605R230FixedOutputSelfExternalSplitClosedIsTrue = refl

round605R230FullCommutatorSelfExternalSplitClosedIsTrue :
  round605R230FullCommutatorSelfExternalSplitClosed ≡ true
round605R230FullCommutatorSelfExternalSplitClosedIsTrue = refl

round605IntroducesEstimateIsFalse :
  round605IntroducesEstimate ≡ false
round605IntroducesEstimateIsFalse = refl

round605SelfPartCancelsByCyclicEnergyConservationIsFalse :
  round605SelfPartCancelsByCyclicEnergyConservation ≡ false
round605SelfPartCancelsByCyclicEnergyConservationIsFalse = refl

round605ExternalNetworkPartPaidIsFalse :
  round605ExternalNetworkPartPaid ≡ false
round605ExternalNetworkPartPaidIsFalse = refl
