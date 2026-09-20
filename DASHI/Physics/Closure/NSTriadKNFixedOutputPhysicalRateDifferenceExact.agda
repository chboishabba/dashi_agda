module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact where

------------------------------------------------------------------------
-- S2b2d1b2 / PHYSICAL FIXED-OUTPUT RATE DIFFERENCE IS CENTERED RADIAL
--
-- For the literal physical viscous rate
--
--   rho(m) = nu |m|^2,
--   r_tau  = rho(p_tau) + rho(q_tau),
--
-- two incidences alpha,beta on one output k satisfy
--
--   2 (r_alpha - r_beta)
--     = nu ( |p_alpha-q_alpha|^2 - |p_beta-q_beta|^2 ).
--
-- This is the live rational-carrier counterpart of the integer
-- parallelogram/R128 geometry.  The common output square cancels exactly.
--
-- No division by two, square roots, shell localization, positivity,
-- cardinality factor, norm estimate, or spacetime estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNLiteralMixedCellGramPairClosedRound382Exact as R382

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

differenceMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
differenceMode p q = Z3.addMode p (Z3.negateMode q)

parallelogram :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (p q : Z3.FourierMode) →
  C3.normSquared I (differenceMode p q)
    + C3.normSquared I (Z3.addMode p q)
  ≡
  two * (C3.normSquared I p + C3.normSquared I q)
parallelogram E I
    (Z3.mode px py pz) (Z3.mode qx qy qz) =
  let
    ax = C3.embedInteger E px
    ay = C3.embedInteger E py
    az = C3.embedInteger E pz
    bx = C3.embedInteger E qx
    by = C3.embedInteger E qy
    bz = C3.embedInteger E qz
  in
  trans
    (cong
      (λ d2 →
        d2
        + C3.normSquared I
            (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz)))
      (C3.normSquaredMeaning I
        (differenceMode (Z3.mode px py pz) (Z3.mode qx qy qz))))
    (let
      endpoint :
        ((ax - bx) * (ax - bx)
          + (ay - by) * (ay - by))
          + (az - bz) * (az - bz)
          + C3.normSquared I
              (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        ≡
        two *
          (C3.normSquared I (Z3.mode px py pz)
            + C3.normSquared I (Z3.mode qx qy qz))
      endpoint
        rewrite C3.normSquaredMeaning I (Z3.mode px py pz)
              | C3.normSquaredMeaning I (Z3.mode qx qy qz)
              | C3.normSquaredMeaning I
                  (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
              | C3.embedAdd E px qx
              | C3.embedAdd E py qy
              | C3.embedAdd E pz qz =
        solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

      differenceMeaning :
        C3.normSquared I
          (differenceMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        ≡
        ((ax - bx) * (ax - bx)
          + (ay - by) * (ay - by))
          + (az - bz) * (az - bz)
      differenceMeaning
        rewrite C3.normSquaredMeaning I
          (differenceMode (Z3.mode px py pz) (Z3.mode qx qy qz))
              | C3.embedAdd E px (- qx)
              | C3.embedAdd E py (- qy)
              | C3.embedAdd E pz (- qz)
              | C3.embedNegate E qx
              | C3.embedNegate E qy
              | C3.embedNegate E qz =
        solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])
    in
    subst
      (λ d2 →
        d2
          + C3.normSquared I
              (Z3.addMode (Z3.mode px py pz) (Z3.mode qx qy qz))
        ≡
        two *
          (C3.normSquared I (Z3.mode px py pz)
            + C3.normSquared I (Z3.mode qx qy qz)))
      (sym differenceMeaning)
      endpoint)

resonantParallelogram :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  C3.normSquared I
      (differenceMode (Physical.p tau) (Physical.q tau))
    + C3.normSquared I (Physical.k tau)
  ≡
  two *
    (C3.normSquared I (Physical.p tau)
      + C3.normSquared I (Physical.q tau))
resonantParallelogram E I tau =
  subst
    (λ selectedOutput →
      C3.normSquared I
          (differenceMode (Physical.p tau) (Physical.q tau))
        + C3.normSquared I selectedOutput
      ≡
      two *
        (C3.normSquared I (Physical.p tau)
          + C3.normSquared I (Physical.q tau)))
    (Physical.resonance tau)
    (parallelogram E I (Physical.p tau) (Physical.q tau))

physicalCellRate :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  Physical.PhysicalTriadIncidence → ℚ
physicalCellRate physicalSystem tau =
  R94.physicalDecayRate physicalSystem (Physical.p tau)
  + R94.physicalDecayRate physicalSystem (Physical.q tau)

physicalCellRateIsLiteralPairRate :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (tau : Physical.PhysicalTriadIncidence) →
  physicalCellRate physicalSystem tau
  ≡
  let module P = R382.ClosedLiteralPair physicalSystem S
  in P.cellRate tau
physicalCellRateIsLiteralPairRate physicalSystem S tau = refl

fixedOutputPhysicalRateDifference :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem
    dAlpha = differenceMode (Physical.p alpha) (Physical.q alpha)
    dBeta = differenceMode (Physical.p beta) (Physical.q beta)
  in
  two *
    (physicalCellRate physicalSystem alpha
      - physicalCellRate physicalSystem beta)
  ≡
  nu * (C3.normSquared I dAlpha - C3.normSquared I dBeta)
fixedOutputPhysicalRateDifference physicalSystem alpha beta sameOutput =
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    nu = Field30.viscosity physicalSystem

    pa = C3.normSquared I (Physical.p alpha)
    qa = C3.normSquared I (Physical.q alpha)
    pb = C3.normSquared I (Physical.p beta)
    qb = C3.normSquared I (Physical.q beta)
    ka = C3.normSquared I (Physical.k alpha)
    kb = C3.normSquared I (Physical.k beta)
    da = C3.normSquared I
      (differenceMode (Physical.p alpha) (Physical.q alpha))
    db = C3.normSquared I
      (differenceMode (Physical.p beta) (Physical.q beta))

    paraA : da + ka ≡ two * (pa + qa)
    paraA = resonantParallelogram E I alpha

    paraB : db + kb ≡ two * (pb + qb)
    paraB = resonantParallelogram E I beta

    sameK : ka ≡ kb
    sameK = cong (C3.normSquared I) sameOutput

    decayPAlpha :
      R94.physicalDecayRate physicalSystem (Physical.p alpha)
      ≡ nu * pa
    decayPAlpha = refl

    decayQAlpha :
      R94.physicalDecayRate physicalSystem (Physical.q alpha)
      ≡ nu * qa
    decayQAlpha = refl

    decayPBeta :
      R94.physicalDecayRate physicalSystem (Physical.p beta)
      ≡ nu * pb
    decayPBeta = refl

    decayQBeta :
      R94.physicalDecayRate physicalSystem (Physical.q beta)
      ≡ nu * qb
    decayQBeta = refl
  in
  rewrite decayPAlpha | decayQAlpha | decayPBeta | decayQBeta
        | sym paraA | sym paraB | sameK =
    solve (nu ∷ da ∷ db ∷ kb ∷ [])

fixedOutputPhysicalRateDifferenceFactored : Bool
fixedOutputPhysicalRateDifferenceFactored = true

fixedOutputPhysicalRateDifferenceUsesCommonOutputCancellation : Bool
fixedOutputPhysicalRateDifferenceUsesCommonOutputCancellation = true

fixedOutputPhysicalRateDifferenceIntroducesDivision : Bool
fixedOutputPhysicalRateDifferenceIntroducesDivision = false

quantitativeRateWeightedCovariancePaidHere : Bool
quantitativeRateWeightedCovariancePaidHere = false

clayPromotion : Bool
clayPromotion = false

fixedOutputPhysicalRateDifferenceFactoredIsTrue :
  fixedOutputPhysicalRateDifferenceFactored ≡ true
fixedOutputPhysicalRateDifferenceFactoredIsTrue = refl

fixedOutputPhysicalRateDifferenceIntroducesDivisionIsFalse :
  fixedOutputPhysicalRateDifferenceIntroducesDivision ≡ false
fixedOutputPhysicalRateDifferenceIntroducesDivisionIsFalse = refl
