module DASHI.Culture.GoodmanSonicWarfareRationalInverseExact where

------------------------------------------------------------------------
-- RATIONAL INVERSE / CALIBRATED RECOVERY / PERTURBATION
--
-- Prior mathematical source: Jacques Hadamard's inverse-problem criteria
-- (1902/1923). Prior code/proof owner: Data.Rational.Tactic.RingSolver
-- in agda-stdlib. Prior DASHI proof owner:
-- DASHI.Core.RobustExperimentInferenceFrontierExact.
--
-- Steve Goodman (2009) owns the cultural/philosophical source synthesis,
-- NOT these elementary rational matrix identities or the underlying
-- rational arithmetic. This is a new DASHI finite-formalisation adapter.
--
-- A declared inverse coefficient r is mandatory. r*q=1 is an explicit
-- assumption that must be independently supported for physical sensors.
-- No field solution, real-world calibration, uniform conditioning,
-- human/clinical outcome, or Monster representation is established.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import Data.Rational.Properties as QProperties

forwardTriangular : ℚ → (ℚ × ℚ) → (ℚ × ℚ)
forwardTriangular q (x , y) =
  x , (x + q * y)

recoverTriangular : ℚ → (ℚ × ℚ) → (ℚ × ℚ)
recoverTriangular r (a , b) =
  a , r * (b - a)

-- Exact polynomial cancellation; owner is the original rational ring
-- solver, not a newly postulated arithmetic identity.
ringCancellation :
  ∀ (q r x y : ℚ) →
  r * ((x + q * y) - x) ≡ (r * q) * y
ringCancellation q r x y =
  solve (q ∷ r ∷ x ∷ y ∷ [])

-- Assumption r*q=1 remains explicit, not automatic or empirical.
calibratedInverseRoundtrip :
  ∀ (q r x y : ℚ) →
  r * q ≡ 1ℚ →
  recoverTriangular r (forwardTriangular q (x , y))
    ≡ (x , y)
calibratedInverseRoundtrip q r x y paid =
  cong (λ second → x , second)
    (trans
      (ringCancellation q r x y)
      (trans
        (cong (λ factor → factor * y) paid)
        (QProperties.*-identityˡ y)))

-- For a perturbation δ in the second observed coordinate, the hidden
-- second coordinate is shifted by r*δ. No bound on |r| is inferred.
ringPerturbation :
  ∀ (q r x y delta : ℚ) →
  r * (((x + q * y) + delta) - x)
    ≡ ((r * q) * y) + r * delta
ringPerturbation q r x y delta =
  solve (q ∷ r ∷ x ∷ y ∷ delta ∷ [])

calibratedPerturbation :
  ∀ (q r x y delta : ℚ) →
  r * q ≡ 1ℚ →
  r * (((x + q * y) + delta) - x)
    ≡ y + r * delta
calibratedPerturbation q r x y delta paid =
  trans
    (ringPerturbation q r x y delta)
    (trans
      (cong (λ factor → factor * y + r * delta) paid)
      (cong
        (λ value → value + r * delta)
        (QProperties.*-identityˡ y)))

------------------------------------------------------------------------
-- Stop: the quantitative family A_n = [[1,0],[1,1/n]], and
-- condition_infinity(A_n)=2(n+1), are verified by a separate exact-
-- rational Python regression for selected positive n. They are NOT
-- implied by the ring identities alone and have NOT been kernel-checked
-- for all positive n.
------------------------------------------------------------------------
