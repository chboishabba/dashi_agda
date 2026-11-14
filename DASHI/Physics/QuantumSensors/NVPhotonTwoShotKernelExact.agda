module DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact where

-- Two Bernoulli trials conditional on a declared i.i.d. model.
-- Product probabilities are model assumptions, NOT deduced from
-- single-shot photon response or experimental independence.
-- The underlying one-shot normalized likelihood is imported from MCG.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (trans)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon

data PhotonBit : Set where
  click dark : PhotonBit

record IndependentTwoShot : Set₁ where
  field
    single : Photon.BinaryPhotonLikelihood
open IndependentTwoShot public

weight : Photon.BinaryPhotonLikelihood → PhotonBit → ℚ
weight p click = Photon.photon p
weight p dark = Photon.noPhoton p

joint : IndependentTwoShot → PhotonBit → PhotonBit → ℚ
joint t x y = weight (single t) x * weight (single t) y

-- Product mass normalisation follows from existing one-shot normalisation.
-- The first equality is a finite polynomial identity; the second uses
-- the source likelihood's normalization witness.
jointSquare : (t : IndependentTwoShot) →
  joint t click click +
  (joint t click dark + joint t dark click) + joint t dark dark ≡
  (Photon.photon (single t) + Photon.noPhoton (single t)) *
  (Photon.photon (single t) + Photon.noPhoton (single t))
jointSquare t =
  solve (Photon.photon (single t) ∷
         Photon.noPhoton (single t) ∷ [])

jointNormalized : (t : IndependentTwoShot) →
  joint t click click +
  (joint t click dark + joint t dark click) + joint t dark dark ≡ 1ℚ
jointNormalized t =
  trans (jointSquare t)
    (trans (cong (λ z → z * z) (Photon.normalized (single t))) refl)

-- A threshold rule retains the ambiguous 1-click outcomes as ties.
data TwoShotOutcome : Set where
  bothClick tie bothDark : TwoShotOutcome

classify : PhotonBit → PhotonBit → TwoShotOutcome
classify click click = bothClick
classify click dark = tie
classify dark click = tie
classify dark dark = bothDark

bothClickWeight : IndependentTwoShot → ℚ
bothClickWeight t = joint t click click

bothDarkWeight : IndependentTwoShot → ℚ
bothDarkWeight t = joint t dark dark

tieWeight : IndependentTwoShot → ℚ
tieWeight t = joint t click dark + joint t dark click

partition : (t : IndependentTwoShot) →
  bothClickWeight t + tieWeight t + bothDarkWeight t ≡ 1ℚ
partition t = jointNormalized t

-- The model is useful to an experimental consumer only if the joint
-- probabilities have a separately justified physical independence receipt.
