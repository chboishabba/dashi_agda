module DASHI.Physics.YangMills.BalabanP33WilsonBackgroundTrivializationBridgeExact where

------------------------------------------------------------------------
-- ROW A1: CMP99 LEFT-BACKGROUND / DASHI RIGHT-BACKGROUND TRIVIALIZATION
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- SOURCE / REPOSITORY CONVENTION
--
-- CMP99 expands a background link in the form
--
--       exp(s Y_L) U,
--
-- while DASHI's existing physical Wilson Hessian uses right-exponential link
-- jets.  On a unit quaternion U the two tangent coordinates are related by
--
--       Y_R = U^-1 Y_L U.
--
-- This file proves the finite rational quaternion cancellation directly.  In
-- particular
--
--       U Y_R = Y_L U,
--       Y_R U^-1 = U^-1 Y_L,
--
-- and transports the st and stt atoms for both positive and inverse plaquette
-- occurrences.  No abstract Ad-matrix identification is needed for this seam.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonBackgroundQuadraticJetExact as Mixed

------------------------------------------------------------------------
-- Small exact quaternion ring lemmas not previously named by the Wilson lane.
------------------------------------------------------------------------

oneMultiplyLeft : ∀ value → Jet.oneQ Jet.*q value ≡ value
oneMultiplyLeft (Jet.quat a0 a1 a2 a3) =
  Jet.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)

multiplyOneRight : ∀ value → value Jet.*q Jet.oneQ ≡ value
multiplyOneRight (Jet.quat a0 a1 a2 a3) =
  Jet.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)

negMultiplyLeft : ∀ left right →
  Jet.negQ left Jet.*q right ≡ Jet.negQ (left Jet.*q right)
negMultiplyLeft
    (Jet.quat a0 a1 a2 a3) (Jet.quat b0 b1 b2 b3) =
  Jet.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)

multiplyNegRight : ∀ left right →
  left Jet.*q Jet.negQ right ≡ Jet.negQ (left Jet.*q right)
multiplyNegRight
    (Jet.quat a0 a1 a2 a3) (Jet.quat b0 b1 b2 b3) =
  Jet.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)
    (ℚRing.solve-∀ a0 a1 a2 a3 b0 b1 b2 b3)

mixedFactorJetExt :
  ∀ {left right : Mixed.QuaternionBackgroundQuadraticFactorJet} →
  Mixed.factorValue left ≡ Mixed.factorValue right →
  Mixed.factorBackground left ≡ Mixed.factorBackground right →
  Mixed.factorFluctuation left ≡ Mixed.factorFluctuation right →
  Mixed.factorFluctuationSecond left ≡ Mixed.factorFluctuationSecond right →
  Mixed.factorBackgroundFluctuation left ≡ Mixed.factorBackgroundFluctuation right →
  Mixed.factorBackgroundFluctuationSecond left
    ≡ Mixed.factorBackgroundFluctuationSecond right →
  left ≡ right
mixedFactorJetExt
  {Mixed.mixedFactorJet value background fluctuation fluctuationSecond
    backgroundFluctuation backgroundFluctuationSecond}
  {Mixed.mixedFactorJet .value .background .fluctuation .fluctuationSecond
    .backgroundFluctuation .backgroundFluctuationSecond}
  refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- Algebraic left/right tangent conversion for a unit link.
------------------------------------------------------------------------

record UnitQuaternionPair : Set where
  field
    value inverse : Jet.RationalQuaternion
    valueInverse : value Jet.*q inverse ≡ Jet.oneQ
    inverseValue : inverse Jet.*q value ≡ Jet.oneQ

open UnitQuaternionPair public

rightTrivializedBackground :
  UnitQuaternionPair → Jet.RationalQuaternion → Jet.RationalQuaternion
rightTrivializedBackground unit leftBackground =
  (inverse unit Jet.*q leftBackground) Jet.*q value unit

positiveBackgroundCancellation :
  ∀ unit leftBackground →
  value unit Jet.*q rightTrivializedBackground unit leftBackground
  ≡ leftBackground Jet.*q value unit
positiveBackgroundCancellation unit leftBackground =
  let
    u = value unit
    uInv = inverse unit
    y = leftBackground
  in
  trans
    (sym (Jet.quaternionMultiplyAssociative u (uInv Jet.*q y) u))
    (trans
      (cong (_Jet.*q u)
        (sym (Jet.quaternionMultiplyAssociative u uInv y)))
      (trans
        (cong (λ selected → (selected Jet.*q y) Jet.*q u)
          (valueInverse unit))
        (cong (_Jet.*q u) (oneMultiplyLeft y))))

inverseBackgroundCancellation :
  ∀ unit leftBackground →
  rightTrivializedBackground unit leftBackground Jet.*q inverse unit
  ≡ inverse unit Jet.*q leftBackground
inverseBackgroundCancellation unit leftBackground =
  let
    u = value unit
    uInv = inverse unit
    y = leftBackground
  in
  trans
    (Jet.quaternionMultiplyAssociative (uInv Jet.*q y) u uInv)
    (trans
      (cong ((uInv Jet.*q y) Jet.*q_)
        (valueInverse unit))
      (multiplyOneRight (uInv Jet.*q y)))

------------------------------------------------------------------------
-- Mixed s t^2 factor jets in the two conventions.
------------------------------------------------------------------------

positiveRightTrivializedJet :
  UnitQuaternionPair → Jet.RationalQuaternion → Jet.RationalQuaternion →
  Mixed.QuaternionBackgroundQuadraticFactorJet
positiveRightTrivializedJet unit leftBackground fluctuation =
  let
    u = value unit
    yR = rightTrivializedBackground unit leftBackground
    x = fluctuation
  in
  Mixed.mixedFactorJet
    u
    (u Jet.*q yR)
    (u Jet.*q x)
    (u Jet.*q (x Jet.*q x))
    (u Jet.*q (yR Jet.*q x))
    (u Jet.*q (yR Jet.*q (x Jet.*q x)))

positiveCMP99LeftJet :
  UnitQuaternionPair → Jet.RationalQuaternion → Jet.RationalQuaternion →
  Mixed.QuaternionBackgroundQuadraticFactorJet
positiveCMP99LeftJet unit leftBackground fluctuation =
  let
    u = value unit
    y = leftBackground
    x = fluctuation
  in
  Mixed.mixedFactorJet
    u
    (y Jet.*q u)
    (u Jet.*q x)
    (u Jet.*q (x Jet.*q x))
    ((y Jet.*q u) Jet.*q x)
    ((y Jet.*q u) Jet.*q (x Jet.*q x))

positiveTrivializationMixedJetExact :
  ∀ unit leftBackground fluctuation →
  positiveRightTrivializedJet unit leftBackground fluctuation
  ≡ positiveCMP99LeftJet unit leftBackground fluctuation
positiveTrivializationMixedJetExact unit y x =
  let
    u = value unit
    yR = rightTrivializedBackground unit y
    background = positiveBackgroundCancellation unit y
    mixed = trans
      (sym (Jet.quaternionMultiplyAssociative u yR x))
      (cong (_Jet.*q x) background)
    mixedSecond = trans
      (sym (Jet.quaternionMultiplyAssociative u yR (x Jet.*q x)))
      (cong (_Jet.*q (x Jet.*q x)) background)
  in
  mixedFactorJetExt refl background refl refl mixed mixedSecond

inverseRightTrivializedJet :
  UnitQuaternionPair → Jet.RationalQuaternion → Jet.RationalQuaternion →
  Mixed.QuaternionBackgroundQuadraticFactorJet
inverseRightTrivializedJet unit leftBackground fluctuation =
  let
    uInv = inverse unit
    yR = rightTrivializedBackground unit leftBackground
    x = fluctuation
  in
  Mixed.mixedFactorJet
    uInv
    (Jet.negQ yR Jet.*q uInv)
    (Jet.negQ x Jet.*q uInv)
    ((x Jet.*q x) Jet.*q uInv)
    ((x Jet.*q yR) Jet.*q uInv)
    (Jet.negQ ((x Jet.*q x) Jet.*q yR) Jet.*q uInv)

inverseCMP99LeftJet :
  UnitQuaternionPair → Jet.RationalQuaternion → Jet.RationalQuaternion →
  Mixed.QuaternionBackgroundQuadraticFactorJet
inverseCMP99LeftJet unit leftBackground fluctuation =
  let
    uInv = inverse unit
    y = leftBackground
    x = fluctuation
  in
  Mixed.mixedFactorJet
    uInv
    (uInv Jet.*q Jet.negQ y)
    (Jet.negQ x Jet.*q uInv)
    ((x Jet.*q x) Jet.*q uInv)
    (x Jet.*q (uInv Jet.*q y))
    (Jet.negQ ((x Jet.*q x) Jet.*q (uInv Jet.*q y)))

inverseBackgroundNegCancellation :
  ∀ unit leftBackground →
  Jet.negQ (rightTrivializedBackground unit leftBackground)
    Jet.*q inverse unit
  ≡ inverse unit Jet.*q Jet.negQ leftBackground
inverseBackgroundNegCancellation unit y =
  trans
    (negMultiplyLeft (rightTrivializedBackground unit y) (inverse unit))
    (trans
      (cong Jet.negQ (inverseBackgroundCancellation unit y))
      (sym (multiplyNegRight (inverse unit) y)))

inverseMixedCancellation :
  ∀ unit leftBackground fluctuation →
  (fluctuation Jet.*q rightTrivializedBackground unit leftBackground)
    Jet.*q inverse unit
  ≡ fluctuation Jet.*q (inverse unit Jet.*q leftBackground)
inverseMixedCancellation unit y x =
  trans
    (Jet.quaternionMultiplyAssociative x
      (rightTrivializedBackground unit y) (inverse unit))
    (cong (x Jet.*q_) (inverseBackgroundCancellation unit y))

inverseMixedSecondCancellation :
  ∀ unit leftBackground fluctuation →
  Jet.negQ
      (((fluctuation Jet.*q fluctuation)
        Jet.*q rightTrivializedBackground unit leftBackground))
    Jet.*q inverse unit
  ≡ Jet.negQ
      ((fluctuation Jet.*q fluctuation)
        Jet.*q (inverse unit Jet.*q leftBackground))
inverseMixedSecondCancellation unit y x =
  trans
    (negMultiplyLeft
      ((x Jet.*q x) Jet.*q rightTrivializedBackground unit y)
      (inverse unit))
    (cong Jet.negQ
      (inverseMixedCancellation unit y (x Jet.*q x)))

inverseTrivializationMixedJetExact :
  ∀ unit leftBackground fluctuation →
  inverseRightTrivializedJet unit leftBackground fluctuation
  ≡ inverseCMP99LeftJet unit leftBackground fluctuation
inverseTrivializationMixedJetExact unit y x =
  mixedFactorJetExt
    refl
    (inverseBackgroundNegCancellation unit y)
    refl
    refl
    (inverseMixedCancellation unit y x)
    (inverseMixedSecondCancellation unit y x)

------------------------------------------------------------------------
-- Proof levels
------------------------------------------------------------------------

wilsonBackgroundLeftRightTrivializationLevel : ProofLevel
wilsonBackgroundLeftRightTrivializationLevel = machineChecked

wilsonBackgroundMixedJetTrivializationLevel : ProofLevel
wilsonBackgroundMixedJetTrivializationLevel = machineChecked
