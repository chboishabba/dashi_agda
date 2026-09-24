module DASHI.Physics.Closure.NSTriadKNR573HelicitySplitLowOutputPaymentExact where

------------------------------------------------------------------------
-- PERIODIC B / CURRENT R573 HOMO-HETERO SPLIT PAID BY R574/R575 GEOMETRY
--
-- The live R573 split keeps
--
--   H_homo   = M++ + M--
--   H_hetero = M+- + M-+
--
-- separate.  R574 already proves a low-output squared bound for every M_st,
-- and R575 proves that the SUM of all four component majorants collapses
-- exactly to raw modal mass with no helicity-count factor.
--
-- Reuse the existing three-vector Cauchy theorem with a literal zero third
-- vector.  Each two-channel vector therefore costs only the fixed constant 3:
--
--   ||H_homo||^2   <= 3 (||M++||^2 + ||M--||^2)
--   ||H_hetero||^2 <= 3 (||M+-||^2 + ||M-+||^2).
--
-- Adding the two inequalities and invoking R575 yields
--
--   ||H_homo||^2 + ||H_hetero||^2
--     <= 27 |p|^2 ||u_a||^2 ||u_b||^2.
--
-- This theorem is valid for every nonzero inner output.  It has NO midpoint
-- hypothesis and NO HH hypothesis.  Thus both the odd-midpoint homochiral
-- branch and heterochiral non-HH branch already possess a pointwise physical
-- low-output currency; their remaining wall is variable inner-fibre / outer
-- spectator aggregation, not new local geometry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNFourHelicityComponentMassCollapseRound575Exact as R575
import DASHI.Physics.Closure.NSTriadKNR573HomochiralHeterochiralSplitExact as Split573

F : C3.RealField _
F = Rational.rationalRealField

twentySeven : ℚ
twentySeven = R178.three * R178.nine

module Payment
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse
  module Split = Split573.Split W S L H system velocityTransverse
  module Collapse = R575.PhysicalCollapse
    E I O system S L velocityTransverse

  componentMass :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign → Helical.HelicitySign → ℚ
  componentMass tau signP signQ =
    L2.complex3NormSquared
      (C.multiplierDifferenceVector tau signP signQ)

  homochiralComponentMass :
    Physical.PhysicalTriadIncidence → ℚ
  homochiralComponentMass tau =
    componentMass tau Helical.plus Helical.plus
    + componentMass tau Helical.minus Helical.minus

  heterochiralComponentMass :
    Physical.PhysicalTriadIncidence → ℚ
  heterochiralComponentMass tau =
    componentMass tau Helical.plus Helical.minus
    + componentMass tau Helical.minus Helical.plus

  splitComponentMassIsFourComponentMass :
    (tau : Physical.PhysicalTriadIncidence) →
    homochiralComponentMass tau + heterochiralComponentMass tau
    ≡
      componentMass tau Helical.plus Helical.plus
      + componentMass tau Helical.plus Helical.minus
      + componentMass tau Helical.minus Helical.plus
      + componentMass tau Helical.minus Helical.minus
  splitComponentMassIsFourComponentMass tau = solve
    ( componentMass tau Helical.plus Helical.plus
    ∷ componentMass tau Helical.plus Helical.minus
    ∷ componentMass tau Helical.minus Helical.plus
    ∷ componentMass tau Helical.minus Helical.minus
    ∷ [])

  homochiralInnerNormBound :
    (tau : Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (Split.homochiralInner tau)
    ≤ R178.three * homochiralComponentMass tau
  homochiralInnerNormBound tau =
    let
      a = C.multiplierDifferenceVector tau Helical.plus Helical.plus
      b = C.multiplierDifferenceVector tau Helical.minus Helical.minus
      base = R178.threeVectorSumNormSquaredBound a b (C3.complex3Zero F)
      target :
        R178.three *
          (L2.complex3NormSquared a
           + L2.complex3NormSquared b
           + L2.complex3NormSquared (C3.complex3Zero F))
        ≡ R178.three * homochiralComponentMass tau
      target = solve
        (L2.complex3NormSquared a ∷ L2.complex3NormSquared b ∷ [])
      lowerMeaning :
        C3.complex3Add (C3.complex3Add a b) (C3.complex3Zero F)
        ≡ Split.homochiralInner tau
      lowerMeaning = Field.complex3AddZeroRight (C3.complex3Add a b)
    in
    subst
      (λ lower →
        L2.complex3NormSquared lower
        ≤ R178.three * homochiralComponentMass tau)
      lowerMeaning
      (subst
        (λ upper →
          L2.complex3NormSquared
            (C3.complex3Add (C3.complex3Add a b) (C3.complex3Zero F))
          ≤ upper)
        target
        base)

  heterochiralInnerNormBound :
    (tau : Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (Split.heterochiralInner tau)
    ≤ R178.three * heterochiralComponentMass tau
  heterochiralInnerNormBound tau =
    let
      a = C.multiplierDifferenceVector tau Helical.plus Helical.minus
      b = C.multiplierDifferenceVector tau Helical.minus Helical.plus
      base = R178.threeVectorSumNormSquaredBound a b (C3.complex3Zero F)
      target :
        R178.three *
          (L2.complex3NormSquared a
           + L2.complex3NormSquared b
           + L2.complex3NormSquared (C3.complex3Zero F))
        ≡ R178.three * heterochiralComponentMass tau
      target = solve
        (L2.complex3NormSquared a ∷ L2.complex3NormSquared b ∷ [])
      lowerMeaning :
        C3.complex3Add (C3.complex3Add a b) (C3.complex3Zero F)
        ≡ Split.heterochiralInner tau
      lowerMeaning = Field.complex3AddZeroRight (C3.complex3Add a b)
    in
    subst
      (λ lower →
        L2.complex3NormSquared lower
        ≤ R178.three * heterochiralComponentMass tau)
      lowerMeaning
      (subst
        (λ upper →
          L2.complex3NormSquared
            (C3.complex3Add (C3.complex3Add a b) (C3.complex3Zero F))
          ≤ upper)
        target
        base)

  homoPlusHeteroLowOutputBound :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    L2.complex3NormSquared (Split.homochiralInner tau)
      + L2.complex3NormSquared (Split.heterochiralInner tau)
    ≤
    twentySeven * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
  homoPlusHeteroLowOutputBound tau outputNonzero =
    let
      local :
        L2.complex3NormSquared (Split.homochiralInner tau)
          + L2.complex3NormSquared (Split.heterochiralInner tau)
        ≤ R178.three *
            (homochiralComponentMass tau + heterochiralComponentMass tau)
      local =
        subst
          (λ upper →
            L2.complex3NormSquared (Split.homochiralInner tau)
              + L2.complex3NormSquared (Split.heterochiralInner tau)
            ≤ upper)
          (solve
            ( homochiralComponentMass tau
            ∷ heterochiralComponentMass tau
            ∷ []))
          (ℚP.+-mono-≤
            (homochiralInnerNormBound tau)
            (heterochiralInnerNormBound tau))

      fourBound = Collapse.sumFourComponentCellBounds tau outputNonzero

      splitBound :
        homochiralComponentMass tau + heterochiralComponentMass tau
        ≤
        R178.nine * C3.normSquared I (Physical.k tau)
          * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
          * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
      splitBound =
        subst
          (λ lower →
            lower
            ≤ R178.nine * C3.normSquared I (Physical.k tau)
              * L2.complex3NormSquared
                  (Audit.velocity system (Physical.p tau))
              * L2.complex3NormSquared
                  (Audit.velocity system (Physical.q tau)))
          (sym (splitComponentMassIsFourComponentMass tau))
          fourBound

      scaled :
        R178.three *
          (homochiralComponentMass tau + heterochiralComponentMass tau)
        ≤
        R178.three *
          (R178.nine * C3.normSquared I (Physical.k tau)
            * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
            * L2.complex3NormSquared (Audit.velocity system (Physical.q tau)))
      scaled =
        let instance threeNNI = nonNegative R178.threeNN
        in ℚP.*-monoˡ-≤-nonNeg R178.three splitBound

      normalized :
        R178.three *
          (R178.nine * C3.normSquared I (Physical.k tau)
            * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
            * L2.complex3NormSquared (Audit.velocity system (Physical.q tau)))
        ≡
        twentySeven * C3.normSquared I (Physical.k tau)
          * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
          * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
      normalized = solve
        ( C3.normSquared I (Physical.k tau)
        ∷ L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
        ∷ L2.complex3NormSquared (Audit.velocity system (Physical.q tau))
        ∷ [])
    in
    trans local
      (subst
        (λ upper →
          R178.three *
            (homochiralComponentMass tau + heterochiralComponentMass tau)
          ≤ upper)
        normalized scaled)

r573HomochiralPointwiseLowOutputPaymentClosed : Bool
r573HomochiralPointwiseLowOutputPaymentClosed = true

r573HeterochiralPointwiseLowOutputPaymentClosed : Bool
r573HeterochiralPointwiseLowOutputPaymentClosed = true

r573HeterochiralPaymentRequiresHH : Bool
r573HeterochiralPaymentRequiresHH = false

r573HomochiralPaymentRequiresMidpoint : Bool
r573HomochiralPaymentRequiresMidpoint = false

r573SplitLowOutputPaymentIntroducesVariableCardinality : Bool
r573SplitLowOutputPaymentIntroducesVariableCardinality = false

r573RemainingWallIsInnerFibreOuterSpectatorAggregation : Bool
r573RemainingWallIsInnerFibreOuterSpectatorAggregation = true

clayPromotion : Bool
clayPromotion = false

r573HeterochiralPaymentRequiresHHIsFalse :
  r573HeterochiralPaymentRequiresHH ≡ false
r573HeterochiralPaymentRequiresHHIsFalse = refl

r573HomochiralPaymentRequiresMidpointIsFalse :
  r573HomochiralPaymentRequiresMidpoint ≡ false
r573HomochiralPaymentRequiresMidpointIsFalse = refl
