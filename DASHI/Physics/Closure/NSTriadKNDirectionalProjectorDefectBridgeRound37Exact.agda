module DASHI.Physics.Closure.NSTriadKNDirectionalProjectorDefectBridgeRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Connect the new line/stabilizer geometry directly to the repository's
-- existing HH-good/HH-bad directional defect.  The older exact defect is
--
--   Theta(xi,eta) = 1 - (xi dot eta)^2
--                  = |xi cross eta|^2.
--
-- Round 37's rank-one line projector satisfies exactly
--
--   ||Pi_xi - Pi_eta||_F^2 = 2 Theta(xi,eta).
--
-- Hence the proposed stabilizer mismatch is not a competing notion of
-- coherence: it is exactly twice the already-formalized Luo/Constantin--
-- Fefferman defect, while additionally making the xi ~ -xi quotient explicit.
-- Since 0 <= Theta <= 1, the projector defect lies in [0,2].  This gives a
-- concrete bridge for A3/A4 rather than introducing another abstract smallness
-- parameter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Defect
import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Projector

toDefectVec : V.Vector3 → Defect.Vec3
toDefectVec (V.v3 vx vy vz) = Defect.vec3 vx vy vz

defectNormMeaning : ∀ vector →
  Defect.normSquared (toDefectVec vector) ≡ V.normSquared vector
defectNormMeaning (V.v3 vx vy vz) = refl

defectDotMeaning : ∀ left right →
  Defect.dot (toDefectVec left) (toDefectVec right) ≡ V.dot left right
defectDotMeaning (V.v3 ax ay az) (V.v3 bx by bz) = refl

toExistingDirectionalPair :
  Projector.UnitDirection → Projector.UnitDirection → Defect.UnitDirectionPair
toExistingDirectionalPair left right =
  Defect.unit-direction-pair
    (toDefectVec (Projector.vector left))
    (toDefectVec (Projector.vector right))
    (trans
      (defectNormMeaning (Projector.vector left))
      (Projector.unitNorm left))
    (trans
      (defectNormMeaning (Projector.vector right))
      (Projector.unitNorm right))

existingDirectionalDefectMeaning : ∀ left right →
  Defect.directionalDefect (toExistingDirectionalPair left right)
  ≡
  1ℚ -
    (Projector.directionPairing left right
      * Projector.directionPairing left right)
existingDirectionalDefectMeaning left right =
  cong
    (λ pairing → 1ℚ - (pairing * pairing))
    (defectDotMeaning
      (Projector.vector left)
      (Projector.vector right))
  where
  open import Data.Rational.Base using (_-_)

projectorDefectIsTwiceExistingDirectionalDefect : ∀ left right →
  Projector.unitProjectorDefectSquared left right
  ≡ Projector.two
      * Defect.directionalDefect (toExistingDirectionalPair left right)
projectorDefectIsTwiceExistingDirectionalDefect left right =
  trans
    (Projector.unitProjectorDefectExact left right)
    (cong
      (Projector.two *_)
      (sym (existingDirectionalDefectMeaning left right)))

projectorTwoNonnegative : 0ℚ ≤ Projector.two
projectorTwoNonnegative =
  toWitness {a? = 0ℚ ≤? Projector.two} _

projectorDefectNonnegative : ∀ left right →
  0ℚ ≤ Projector.unitProjectorDefectSquared left right
projectorDefectNonnegative left right =
  subst
    (0ℚ ≤_)
    (sym (projectorDefectIsTwiceExistingDirectionalDefect left right))
    productNN
  where
  theta = Defect.directionalDefect (toExistingDirectionalPair left right)
  productNN : 0ℚ ≤ Projector.two * theta
  productNN =
    let
      instance
        twoNN = nonNegative projectorTwoNonnegative
        thetaNN = nonNegative
          (Defect.directionalDefectNonnegative
            (toExistingDirectionalPair left right))
        productNonnegative =
          ℚP.nonNeg*nonNeg⇒nonNeg Projector.two theta
    in
    ℚP.nonNegative⁻¹ (Projector.two * theta)

projectorDefectAtMostTwo : ∀ left right →
  Projector.unitProjectorDefectSquared left right ≤ Projector.two
projectorDefectAtMostTwo left right =
  let
    pair = toExistingDirectionalPair left right
    instance
      twoNN = nonNegative projectorTwoNonnegative
    scaled :
      Projector.two * Defect.directionalDefect pair
      ≤ Projector.two * 1ℚ
    scaled =
      ℚP.*-monoˡ-≤-nonNeg
        Projector.two
        (Defect.directionalDefectAtMostOne pair)
    rightMeaning : Projector.two * 1ℚ ≡ Projector.two
    rightMeaning = solve []
  in
  subst
    (λ lower → lower ≤ Projector.two)
    (sym (projectorDefectIsTwiceExistingDirectionalDefect left right))
    (subst
      (λ upper →
        Projector.two * Defect.directionalDefect pair ≤ upper)
      rightMeaning
      scaled)

directionalProjectorDefectBridgeClosed : Bool
directionalProjectorDefectBridgeClosed = true

directionalProjectorDefectBridgeClosedIsTrue :
  directionalProjectorDefectBridgeClosed ≡ true
directionalProjectorDefectBridgeClosedIsTrue = refl
