module DASHI.Physics.Closure.NSTriadKNPhysicalSelfFourHelicityEDPaymentExact where

------------------------------------------------------------------------
-- FOUR HELICITY SELF-PHASE CHANNELS -> ONE MODAL ED PAIR KERNEL
--
-- The per-component theorem already gives, for every signs s,t,
--
--   N_{s,t}(p,q) <= D_p^s E_q^t + E_p^s D_q^t.
--
-- Summing all four sign pairs does NOT cost a factor four.  Orthogonality of
-- the +/- helical projectors gives exact Pythagoras on each input mode:
--
--   E_p^+ + E_p^- = E_p,
--   D_p^+ + D_p^- = D_p,
--
-- and similarly for q.  Hence the complete four-sign self contribution obeys
--
--   sum_{s,t} N_{s,t}(p,q) <= D_p E_q + E_p D_q.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNMHDRadiusReciprocalToNormalizedDirectionRound464Exact as R464
import DASHI.Physics.Closure.NSTriadKNPhysicalHHAndNestedRadiusCompilerRound468Exact as R468
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475
import DASHI.Physics.Closure.NSTriadKNPhysicalSelfHelicityComponentEDPaymentExact as Component

F : C3.RealField _
F = Rational.rationalRealField

module FourHelicityED
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws
      F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S)
    (O : Leray.RationalInverseNormOrder
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (radiusCalibration :
      R464.PhysicalSquareAndMHDCalibration
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        S)
    (orientation : R468.PhysicalRadiusOrientation S) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system

  module C = Component.PhysicalComponentED
    physicalSystem S L O unitGap radiusCalibration orientation

  modalEnergy : Z3.FourierMode → ℚ
  modalEnergy mode =
    L2.complex3NormSquared (velocity mode)

  modalDissipation : Z3.FourierMode → ℚ
  modalDissipation mode =
    C3.normSquared I mode * modalEnergy mode

  componentEnergySplit :
    (mode : Z3.FourierMode) →
    Helical.Transverse E mode (velocity mode) →
    C.componentEnergy Helical.plus mode
      + C.componentEnergy Helical.minus mode
    ≡ modalEnergy mode
  componentEnergySplit mode transverse =
    sym (R475.l2NormHelicalSplit E I S L mode (velocity mode) transverse)

  componentDissipationSplit :
    (mode : Z3.FourierMode) →
    Helical.Transverse E mode (velocity mode) →
    C.componentDissipation Helical.plus mode
      + C.componentDissipation Helical.minus mode
    ≡ modalDissipation mode
  componentDissipationSplit mode transverse =
    let
      p2 = C3.normSquared I mode
      ep = C.componentEnergy Helical.plus mode
      em = C.componentEnergy Helical.minus mode
      split = componentEnergySplit mode transverse
    in
    trans
      (solve (p2 ∷ ep ∷ em ∷ []))
      (cong (p2 *_) split)

  fourSignSelfPhase :
    (tau : Physical.PhysicalTriadIncidence) →
    Z3.NonZeroMode (Physical.k tau) →
    ℚ
  fourSignSelfPhase tau outputNonzero =
    C.selfPhaseReal tau outputNonzero Helical.plus Helical.plus
    + C.selfPhaseReal tau outputNonzero Helical.plus Helical.minus
    + C.selfPhaseReal tau outputNonzero Helical.minus Helical.plus
    + C.selfPhaseReal tau outputNonzero Helical.minus Helical.minus

  fourSignSelfPhaseBelowModalED :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
    (pMember : Physical.p tau Cube.∈ Audit.modes system) →
    (qMember : Physical.q tau Cube.∈ Audit.modes system) →
    fourSignSelfPhase tau outputNonzero
    ≤
    modalDissipation (Physical.p tau) * modalEnergy (Physical.q tau)
      + modalEnergy (Physical.p tau) * modalDissipation (Physical.q tau)
  fourSignSelfPhaseBelowModalED tau outputNonzero pMember qMember =
    let
      p = Physical.p tau
      q = Physical.q tau

      bPP = C.selfPhaseComponentBelowED
        tau outputNonzero Helical.plus Helical.plus pMember qMember
      bPM = C.selfPhaseComponentBelowED
        tau outputNonzero Helical.plus Helical.minus pMember qMember
      bMP = C.selfPhaseComponentBelowED
        tau outputNonzero Helical.minus Helical.plus pMember qMember
      bMM = C.selfPhaseComponentBelowED
        tau outputNonzero Helical.minus Helical.minus pMember qMember

      summed :
        fourSignSelfPhase tau outputNonzero
        ≤
        (C.componentDissipation Helical.plus p
            * C.componentEnergy Helical.plus q
          + C.componentEnergy Helical.plus p
            * C.componentDissipation Helical.plus q)
        +
        (C.componentDissipation Helical.plus p
            * C.componentEnergy Helical.minus q
          + C.componentEnergy Helical.plus p
            * C.componentDissipation Helical.minus q)
        +
        (C.componentDissipation Helical.minus p
            * C.componentEnergy Helical.plus q
          + C.componentEnergy Helical.minus p
            * C.componentDissipation Helical.plus q)
        +
        (C.componentDissipation Helical.minus p
            * C.componentEnergy Helical.minus q
          + C.componentEnergy Helical.minus p
            * C.componentDissipation Helical.minus q)
      summed =
        ℚP.+-mono-≤
          (ℚP.+-mono-≤
            (ℚP.+-mono-≤ bPP bPM)
            bMP)
          bMM

      pTransverse =
        Field30.retainedVelocityTransverse physicalSystem p pMember
      qTransverse =
        Field30.retainedVelocityTransverse physicalSystem q qMember

      eP = componentEnergySplit p pTransverse
      eQ = componentEnergySplit q qTransverse
      dP = componentDissipationSplit p pTransverse
      dQ = componentDissipationSplit q qTransverse

      endpoint :
        (C.componentDissipation Helical.plus p
            * C.componentEnergy Helical.plus q
          + C.componentEnergy Helical.plus p
            * C.componentDissipation Helical.plus q)
        +
        (C.componentDissipation Helical.plus p
            * C.componentEnergy Helical.minus q
          + C.componentEnergy Helical.plus p
            * C.componentDissipation Helical.minus q)
        +
        (C.componentDissipation Helical.minus p
            * C.componentEnergy Helical.plus q
          + C.componentEnergy Helical.minus p
            * C.componentDissipation Helical.plus q)
        +
        (C.componentDissipation Helical.minus p
            * C.componentEnergy Helical.minus q
          + C.componentEnergy Helical.minus p
            * C.componentDissipation Helical.minus q)
        ≡
        modalDissipation p * modalEnergy q
          + modalEnergy p * modalDissipation q
      endpoint
        rewrite sym eP | sym eQ | sym dP | sym dQ =
        solve
          ( C.componentEnergy Helical.plus p
          ∷ C.componentEnergy Helical.minus p
          ∷ C.componentEnergy Helical.plus q
          ∷ C.componentEnergy Helical.minus q
          ∷ C.componentDissipation Helical.plus p
          ∷ C.componentDissipation Helical.minus p
          ∷ C.componentDissipation Helical.plus q
          ∷ C.componentDissipation Helical.minus q
          ∷ [])
    in
    subst
      (fourSignSelfPhase tau outputNonzero ≤_)
      endpoint
      summed
