module DASHI.Physics.QuantumSensors.NVPhotonHistoryNormalizationExact where

-- Full binary-prefix-tree probability normalization for arbitrary depth.
-- This is a formal recursion over the source-owned normalized Bernoulli
-- kernel. Conditional i.i.d. is a model assumption, not a device claim.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)
import DASHI.Physics.QuantumSensors.NVPhotonBinaryLikelihoodExact as Photon
import DASHI.Physics.QuantumSensors.NVPhotonTwoShotKernelExact as Two
import DASHI.Physics.QuantumSensors.NVPhotonHistoryLikelihoodExact as Hist

-- Sum across the two possible next observations, recursively across
-- the complete binary history tree. No unproved list equivalence is used.
treeMass : Photon.BinaryPhotonLikelihood → Nat → ℚ
treeMass p zero = 1ℚ
treeMass p (suc n) =
  Two.weight p Two.click * treeMass p n +
  Two.weight p Two.dark * treeMass p n

treeStepIdentity : (a b : ℚ) →
  a * 1ℚ + b * 1ℚ ≡ a + b
treeStepIdentity a b = solve (a ∷ b ∷ [])

treeMassOne :
  (p : Photon.BinaryPhotonLikelihood) → treeMass p (suc zero) ≡ 1ℚ
treeMassOne p =
  trans (treeStepIdentity (Photon.photon p) (Photon.noPhoton p))
        (Photon.normalized p)

-- The inductive step is exactly the Bernoulli normalization contract.
treeMassNormalized :
  (p : Photon.BinaryPhotonLikelihood) (n : Nat) →
  treeMass p n ≡ 1ℚ
treeMassNormalized p zero = refl
treeMassNormalized p (suc n)
  rewrite treeMassNormalized p n =
  trans (treeStepIdentity (Photon.photon p) (Photon.noPhoton p))
        (Photon.normalized p)

-- Actual finite histories remain available as the physical observation
-- carrier, including the empty history; the tree recursion enumerates
-- the two successor choices at each step.
History : Set
History = Hist.History

singletonHistory : History
singletonHistory = Two.click ∷ []

-- Algebraic tree normalization does not imply conditional independence
-- of observed physical measurements. It also does not prove that a
-- finite decision rule has low error or that a detector is calibrated.
