module DASHI.Foundations.SurrealCompactificationRationalBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationIntake as Intake

------------------------------------------------------------------------
-- Internal symbolic rational carrier.
--
-- This is deliberately not Data.Rational and it does not promote a QQ or
-- No carrier.  It is only the finite balanced-ternary approximant shape
-- needed to bridge finite trit towers to a rational-looking symbolic term.

mapVec :
  {A B : Set} →
  {length : Nat} →
  (A → B) →
  SC.Vec A length →
  SC.Vec B length
mapVec f SC.[] =
  SC.[]
mapVec f (x SC.∷ xs) =
  f x SC.∷ mapVec f xs

embedTritVec :
  {depth : Nat} →
  SC.Vec Trit depth →
  SC.Vec Intake.BalancedTernaryDigit depth
embedTritVec =
  mapVec Intake.balancedTernaryEmbedDigit

data SymbolicDenominator : Set where
  threePower :
    Nat →
    SymbolicDenominator

record SymbolicRationalApproximation : Set where
  constructor symbolicRationalApproximation
  field
    scaleDepth :
      Nat

    balancedDigits :
      SC.Vec Intake.BalancedTernaryDigit scaleDepth

    denominator :
      SymbolicDenominator

    denominatorIsThreePowerOfDepth :
      denominator ≡ threePower scaleDepth

    qqCarrierPromoted :
      Bool

    qqCarrierPromotedIsFalse :
      qqCarrierPromoted ≡ false

    noCarrierPromoted :
      Bool

    noCarrierPromotedIsFalse :
      noCarrierPromoted ≡ false

open SymbolicRationalApproximation public

symbolicZero :
  SymbolicRationalApproximation
symbolicZero =
  symbolicRationalApproximation
    zero
    SC.[]
    (threePower zero)
    refl
    false
    refl
    false
    refl

towerToSymbolicRational :
  {depth : Nat} →
  SC.FiniteTritTower depth →
  SymbolicRationalApproximation
towerToSymbolicRational {depth} tower =
  symbolicRationalApproximation
    depth
    (embedTritVec (SC.towerToVec tower))
    (threePower depth)
    refl
    false
    refl
    false
    refl

towerToSymbolicRational-depth :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  scaleDepth (towerToSymbolicRational tower) ≡ depth
towerToSymbolicRational-depth tower =
  refl

towerToSymbolicRational-denominator :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  denominator (towerToSymbolicRational tower) ≡ threePower depth
towerToSymbolicRational-denominator tower =
  refl

towerToSymbolicRational-digits :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  balancedDigits (towerToSymbolicRational tower)
  ≡
  embedTritVec (SC.towerToVec tower)
towerToSymbolicRational-digits tower =
  refl

emptyTowerToSymbolicZero :
  towerToSymbolicRational SC.emptyTower ≡ symbolicZero
emptyTowerToSymbolicZero =
  refl

oneStepNegativeDigit :
  balancedDigits (towerToSymbolicRational SC.oneStepNegative)
  ≡
  Intake.minusOneDigit SC.∷ SC.[]
oneStepNegativeDigit =
  refl

oneStepZeroDigit :
  balancedDigits (towerToSymbolicRational SC.oneStepZero)
  ≡
  Intake.zeroDigit SC.∷ SC.[]
oneStepZeroDigit =
  refl

oneStepPositiveDigit :
  balancedDigits (towerToSymbolicRational SC.oneStepPositive)
  ≡
  Intake.plusOneDigit SC.∷ SC.[]
oneStepPositiveDigit =
  refl

------------------------------------------------------------------------
-- Bridge surface.

record FiniteTritTowerSymbolicRationalBridge : Set₁ where
  field
    intakeContract :
      Intake.SurrealCompactificationIntakeContract

    intakeContractIsCanonical :
      intakeContract ≡ Intake.canonicalSurrealCompactificationIntakeContract

    sourceCarrier :
      Nat →
      Set

    sourceCarrierIsFiniteTritTower :
      sourceCarrier ≡ SC.FiniteTritTower

    symbolicCarrier :
      Set

    symbolicCarrierIsInternal :
      symbolicCarrier ≡ SymbolicRationalApproximation

    digitEmbedding :
      Trit →
      Intake.BalancedTernaryDigit

    digitEmbeddingIsCanonical :
      digitEmbedding ≡ Intake.balancedTernaryEmbedDigit

    bridgeFiniteTower :
      {depth : Nat} →
      SC.FiniteTritTower depth →
      SymbolicRationalApproximation

    bridgeFiniteTowerIsInternal :
      {depth : Nat} →
      (tower : SC.FiniteTritTower depth) →
      bridgeFiniteTower tower ≡ towerToSymbolicRational tower

    truncationSurface :
      SC.InternalBoundedTruncationSurface

    truncationSurfaceIsInternal :
      truncationSurface ≡ SC.canonicalInternalBoundedTruncationSurface

    noQQCarrierBridgeIntake :
      Intake.NoQQCarrierBridgeIntake

    noQQCarrierBridgeIntakeIsCanonical :
      noQQCarrierBridgeIntake ≡ Intake.canonicalNoQQCarrierBridgeIntake

    noPromotionFlags :
      Intake.NoPromotionFlags

    noPromotionFlagsAreCanonical :
      noPromotionFlags ≡ Intake.canonicalNoPromotionFlags

open FiniteTritTowerSymbolicRationalBridge public

canonicalFiniteTritTowerSymbolicRationalBridge :
  FiniteTritTowerSymbolicRationalBridge
canonicalFiniteTritTowerSymbolicRationalBridge =
  record
    { intakeContract =
        Intake.canonicalSurrealCompactificationIntakeContract
    ; intakeContractIsCanonical =
        refl
    ; sourceCarrier =
        SC.FiniteTritTower
    ; sourceCarrierIsFiniteTritTower =
        refl
    ; symbolicCarrier =
        SymbolicRationalApproximation
    ; symbolicCarrierIsInternal =
        refl
    ; digitEmbedding =
        Intake.balancedTernaryEmbedDigit
    ; digitEmbeddingIsCanonical =
        refl
    ; bridgeFiniteTower =
        towerToSymbolicRational
    ; bridgeFiniteTowerIsInternal =
        λ tower → refl
    ; truncationSurface =
        SC.canonicalInternalBoundedTruncationSurface
    ; truncationSurfaceIsInternal =
        refl
    ; noQQCarrierBridgeIntake =
        Intake.canonicalNoQQCarrierBridgeIntake
    ; noQQCarrierBridgeIntakeIsCanonical =
        refl
    ; noPromotionFlags =
        Intake.canonicalNoPromotionFlags
    ; noPromotionFlagsAreCanonical =
        refl
    }

canonicalBridgeDoesNotPromoteQQ :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  qqCarrierPromoted
    (bridgeFiniteTower canonicalFiniteTritTowerSymbolicRationalBridge tower)
  ≡
  false
canonicalBridgeDoesNotPromoteQQ tower =
  refl

canonicalBridgeDoesNotPromoteNo :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  noCarrierPromoted
    (bridgeFiniteTower canonicalFiniteTritTowerSymbolicRationalBridge tower)
  ≡
  false
canonicalBridgeDoesNotPromoteNo tower =
  refl

canonicalBridgeDepth :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  scaleDepth
    (bridgeFiniteTower canonicalFiniteTritTowerSymbolicRationalBridge tower)
  ≡
  depth
canonicalBridgeDepth tower =
  refl

canonicalBridgeDigits :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  balancedDigits
    (bridgeFiniteTower canonicalFiniteTritTowerSymbolicRationalBridge tower)
  ≡
  embedTritVec (SC.towerToVec tower)
canonicalBridgeDigits tower =
  refl

canonicalBridgeTruncateDepth :
  {target source : Nat} →
  (target≤source : target SC.≤ source) →
  (tower : SC.FiniteTritTower source) →
  scaleDepth
    (bridgeFiniteTower canonicalFiniteTritTowerSymbolicRationalBridge
      (SC.truncateTower target≤source tower))
  ≡
  target
canonicalBridgeTruncateDepth target≤source tower =
  refl
