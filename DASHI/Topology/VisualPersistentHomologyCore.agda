module DASHI.Topology.VisualPersistentHomologyCore where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Division-free finite surface for persistent homology of 2D images.
--
-- The intended executable refinement is a filtration of finite cubical
-- complexes.  This core records the exact typed output needed downstream:
-- persistence intervals, H0/H1 integrated Betti areas, the paired BW/WB
-- Alexander-duality residual, and rational target comparison without using
-- floating-point division.

infixl 6 _+ℕ_ _∸ℕ_
infixl 7 _*ℕ_

_+ℕ_ : Nat → Nat → Nat
zero +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

_*ℕ_ : Nat → Nat → Nat
zero *ℕ n = zero
suc m *ℕ n = n +ℕ (m *ℕ n)

_∸ℕ_ : Nat → Nat → Nat
m ∸ℕ zero = m
zero ∸ℕ suc n = zero
suc m ∸ℕ suc n = m ∸ℕ n

absDiffℕ : Nat → Nat → Nat
absDiffℕ m n = (m ∸ℕ n) +ℕ (n ∸ℕ m)

data FiltrationDirection : Set where
  blackToWhite : FiltrationDirection
  whiteToBlack : FiltrationDirection

oppositeFiltration : FiltrationDirection → FiltrationDirection
oppositeFiltration blackToWhite = whiteToBlack
oppositeFiltration whiteToBlack = blackToWhite

oppositeFiltrationInvolutive :
  (direction : FiltrationDirection) →
  oppositeFiltration (oppositeFiltration direction) ≡ direction
oppositeFiltrationInvolutive blackToWhite = refl
oppositeFiltrationInvolutive whiteToBlack = refl

data HomologyDimension : Set where
  H0 : HomologyDimension
  H1 : HomologyDimension

record PersistentCycle : Set where
  constructor mkPersistentCycle
  field
    cycleLabel : String
    cycleFiltration : FiltrationDirection
    cycleDimension : HomologyDimension
    birthStep : Nat
    deathStep : Nat
    lifetime : Nat
    lifetimeMatches : lifetime ≡ deathStep ∸ℕ birthStep
    perimeter : Nat
    touchesImageFrame : Bool

open PersistentCycle public

record ImagePersistenceSignature : Set where
  constructor mkImagePersistenceSignature
  field
    imageLabel : String
    cycles : List PersistentCycle
    bwH0IntegratedBettiArea : Nat
    bwH1IntegratedBettiArea : Nat
    wbH0IntegratedBettiArea : Nat
    wbH1IntegratedBettiArea : Nat

open ImagePersistenceSignature public

data AlexanderDualityLane : Set where
  bwH0AgainstWbH1 : AlexanderDualityLane
  wbH0AgainstBwH1 : AlexanderDualityLane

primaryArea :
  ImagePersistenceSignature →
  AlexanderDualityLane →
  Nat
primaryArea signature bwH0AgainstWbH1 =
  bwH0IntegratedBettiArea signature
primaryArea signature wbH0AgainstBwH1 =
  wbH0IntegratedBettiArea signature

dualArea :
  ImagePersistenceSignature →
  AlexanderDualityLane →
  Nat
dualArea signature bwH0AgainstWbH1 =
  wbH1IntegratedBettiArea signature
dualArea signature wbH0AgainstBwH1 =
  bwH1IntegratedBettiArea signature

record NormalizedAlexanderResidual : Set where
  constructor mkNormalizedAlexanderResidual
  field
    leftArea : Nat
    rightArea : Nat
    residualNumerator : Nat
    residualDenominator : Nat
    numeratorMatches :
      residualNumerator ≡
      (suc (suc zero)) *ℕ absDiffℕ leftArea rightArea
    denominatorMatches :
      residualDenominator ≡ leftArea +ℕ rightArea

open NormalizedAlexanderResidual public

alexanderResidual :
  (signature : ImagePersistenceSignature) →
  (lane : AlexanderDualityLane) →
  NormalizedAlexanderResidual
alexanderResidual signature lane =
  mkNormalizedAlexanderResidual
    (primaryArea signature lane)
    (dualArea signature lane)
    ((suc (suc zero)) *ℕ
      absDiffℕ
        (primaryArea signature lane)
        (dualArea signature lane))
    (primaryArea signature lane +ℕ dualArea signature lane)
    refl
    refl

record RationalTarget : Set where
  constructor mkRationalTarget
  field
    targetNumerator : Nat
    targetDenominator : Nat

open RationalTarget public

scaledTargetResidual :
  NormalizedAlexanderResidual →
  RationalTarget →
  Nat
scaledTargetResidual residual target =
  absDiffℕ
    (targetDenominator target *ℕ residualNumerator residual)
    (targetNumerator target *ℕ residualDenominator residual)

------------------------------------------------------------------------
-- A finite regression witness only.  It proves that the division-free target
-- socket recognizes 2/5 exactly; it is not an artwork or empirical claim.

twoFifthsTarget : RationalTarget
twoFifthsTarget =
  mkRationalTarget (suc (suc zero))
    (suc (suc (suc (suc (suc zero)))))

toyTwoFifthsSignature : ImagePersistenceSignature
toyTwoFifthsSignature =
  mkImagePersistenceSignature
    "toy-two-fifths-regression"
    []
    (suc (suc (suc zero)))
    (suc (suc (suc (suc zero))))
    (suc (suc (suc (suc zero))))
    (suc (suc zero))

toyBwResidualIsExactlyTwoFifths :
  scaledTargetResidual
    (alexanderResidual toyTwoFifthsSignature bwH0AgainstWbH1)
    twoFifthsTarget
  ≡ zero
toyBwResidualIsExactlyTwoFifths = refl
