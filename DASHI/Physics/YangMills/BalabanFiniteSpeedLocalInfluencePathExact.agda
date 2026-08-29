module DASHI.Physics.YangMills.BalabanFiniteSpeedLocalInfluencePathExact where

------------------------------------------------------------------------
-- ROUND70: FINITE-SPEED CORE FROM LOCAL GENERATOR SUPPORT
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Ali Naddaf and Thomas Spencer,
-- "On Homogenization and Scaling Limit of Some Gradient Perturbations of a
-- Massless Free Field", Communications in Mathematical Physics 183 (1997),
-- 55--84. DOI: 10.1007/s002200050020.
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- DASHI CONTRIBUTION
--
-- Isolate and PROVE the algebraic/combinatorial heart of finite-speed local
-- derivative propagation.  Let A be a finite influence generator whose matrix
-- entries vanish unless the two sites are equal or adjacent.  Define A^n by
-- literal finite matrix multiplication.  Then
--
--   no local walk of n steps from x to y  ==>  (A^n)_{xy} = 0.
--
-- Thus every Dyson/matrix-exponential term below graph distance vanishes
-- EXACTLY before any analytic tail estimate.  The remaining continuum-time
-- estimate is only the tail of the source semigroup expansion plus a row-mass
-- majorant; locality itself is no longer an assumed finite-speed receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ using (_<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

record FiniteLocalInfluence (Site : Set) : Set₁ where
  field
    sites : List Site
    Adjacent : Site → Site → Set
    adjacentDec : ∀ x y → Dec (Adjacent x y)
    equalityDec : ∀ x y → Dec (x ≡ y)

    generator : Site → Site → ℚ

    -- Diagonal terms are allowed: they do not propagate support.  Every truly
    -- off-local entry vanishes exactly.
    generatorOutsideLocalStepZero : ∀ x y →
      (((x ≡ y) ⊎ Adjacent x y) → ⊥) →
      generator x y ≡ 0ℚ

open FiniteLocalInfluence public

LocalStep : ∀ {Site} → FiniteLocalInfluence Site → Site → Site → Set
LocalStep dataSet x y = (x ≡ y) ⊎ Adjacent dataSet x y

localStepDec :
  ∀ {Site} (dataSet : FiniteLocalInfluence Site) x y →
  Dec (LocalStep dataSet x y)
localStepDec dataSet x y with equalityDec dataSet x y
... | yes equal = yes (inj₁ equal)
... | no notEqual with adjacentDec dataSet x y
...   | yes adjacent = yes (inj₂ adjacent)
...   | no notAdjacent = no λ
        { (inj₁ equal) → notEqual equal
        ; (inj₂ adjacent) → notAdjacent adjacent
        }

data LocalWalk {Site : Set}
    (dataSet : FiniteLocalInfluence Site) :
    Nat → Site → Site → Set where
  walk0 : ∀ {x} → LocalWalk dataSet zero x x
  walkStep : ∀ {n x middle y} →
    LocalStep dataSet x middle →
    LocalWalk dataSet n middle y →
    LocalWalk dataSet (suc n) x y

NoLocalWalk :
  ∀ {Site} → FiniteLocalInfluence Site → Nat → Site → Site → Set
NoLocalWalk dataSet n x y = LocalWalk dataSet n x y → ⊥

Matrix : Set → Set
Matrix Site = Site → Site → ℚ

identityMatrix :
  ∀ {Site} → FiniteLocalInfluence Site → Matrix Site
identityMatrix dataSet x y with equalityDec dataSet x y
... | yes _ = 1ℚ
... | no _ = 0ℚ

matrixCompose :
  ∀ {Site} → FiniteLocalInfluence Site → Matrix Site → Matrix Site → Matrix Site
matrixCompose dataSet left right x y =
  Sums.sumRational (sites dataSet) (λ middle → left x middle * right middle y)

influencePower :
  ∀ {Site} → FiniteLocalInfluence Site → Nat → Matrix Site
influencePower dataSet zero = identityMatrix dataSet
influencePower dataSet (suc n) =
  matrixCompose dataSet (generator dataSet) (influencePower dataSet n)

sumZero : ∀ {A : Set} (values : List A) →
  Sums.sumRational values (λ _ → 0ℚ) ≡ 0ℚ
sumZero [] = refl
sumZero (_ ∷ values) rewrite sumZero values = refl

powerVanishesWithoutWalk :
  ∀ {Site} (dataSet : FiniteLocalInfluence Site) n {x y} →
  NoLocalWalk dataSet n x y →
  influencePower dataSet n x y ≡ 0ℚ
powerVanishesWithoutWalk dataSet zero {x} {y} noWalk
  with equalityDec dataSet x y
... | yes refl = ⊥-elim (noWalk walk0)
... | no _ = refl
powerVanishesWithoutWalk dataSet (suc n) {x} {y} noWalk =
  trans
    (Sums.sumRationalCong
      (sites dataSet)
      (λ middle →
        generator dataSet x middle * influencePower dataSet n middle y)
      (λ _ → 0ℚ)
      pointwiseZero)
    (sumZero (sites dataSet))
  where
  pointwiseZero : ∀ middle →
    generator dataSet x middle * influencePower dataSet n middle y ≡ 0ℚ
  pointwiseZero middle with localStepDec dataSet x middle
  ... | yes local =
    let
      tailNoWalk : NoLocalWalk dataSet n middle y
      tailNoWalk tail = noWalk (walkStep local tail)
      tailZero = powerVanishesWithoutWalk dataSet n tailNoWalk
    in
    trans
      (cong (generator dataSet x middle *_) tailZero)
      (ℚP.*-zeroʳ (generator dataSet x middle))
  ... | no notLocal =
    trans
      (cong (_* influencePower dataSet n middle y)
        (generatorOutsideLocalStepZero dataSet x middle notLocal))
      (ℚP.*-zeroˡ (influencePower dataSet n middle y))

------------------------------------------------------------------------
-- A graph-distance consumer only needs to prove that orders below distance
-- admit no local walk.  The matrix-power cancellation then follows for free.
------------------------------------------------------------------------

record DistanceLowerBound
    {Site : Set} (dataSet : FiniteLocalInfluence Site)
    (Distance : Site → Site → Nat) : Set₁ where
  field
    belowDistanceHasNoWalk : ∀ {x y n} →
      n ℕ.< Distance x y →
      NoLocalWalk dataSet n x y

open DistanceLowerBound public

belowDistanceInfluencePowerZero :
  ∀ {Site} {dataSet : FiniteLocalInfluence Site}
    {Distance : Site → Site → Nat} →
  DistanceLowerBound dataSet Distance →
  ∀ {x y n} →
  n ℕ.< Distance x y →
  influencePower dataSet n x y ≡ 0ℚ
belowDistanceInfluencePowerZero distanceProof below =
  powerVanishesWithoutWalk _ _
    (belowDistanceHasNoWalk distanceProof below)

finiteSpeedLocalityPowerCancellationLevel : ProofLevel
finiteSpeedLocalityPowerCancellationLevel = machineChecked

-- Physical L7 seam remaining after this theorem:
-- identify the Jacobian/derivative evolution generator of the SAME Balaban /
-- Polchinski effective dynamics with a finite local influence matrix, and bound
-- its local absolute row mass in the unified derivative/KP norm.  Low-order
-- propagation is then exact combinatorics, not additional analysis.
physicalYMLocalDerivativeGeneratorIdentificationLevel : ProofLevel
physicalYMLocalDerivativeGeneratorIdentificationLevel = conditional
