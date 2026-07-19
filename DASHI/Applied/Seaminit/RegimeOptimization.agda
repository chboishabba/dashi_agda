module DASHI.Applied.Seaminit.RegimeOptimization where

open import Agda.Builtin.Bool      using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List     using (List; []; _∷_)
open import Agda.Builtin.Nat      using (Nat)

open import DASHI.Applied.Seaminit.KernelCoupling

------------------------------------------------------------------------
-- Triadic support regime

data Regime : Set where
  avoid   : Regime
  neutral : Regime
  support : Regime

severity : Regime → Nat
severity avoid   = 2
severity neutral = 0
severity support = 1

joinRegime : Regime → Regime → Regime
joinRegime avoid   _       = avoid
joinRegime _       avoid   = avoid
joinRegime support _       = support
joinRegime _       support = support
joinRegime neutral neutral = neutral

joinRegime-idem : ∀ r → joinRegime r r ≡ r
joinRegime-idem avoid   = refl
joinRegime-idem neutral = refl
joinRegime-idem support = refl

joinRegime-comm : ∀ x y → joinRegime x y ≡ joinRegime y x
joinRegime-comm avoid avoid       = refl
joinRegime-comm avoid neutral     = refl
joinRegime-comm avoid support     = refl
joinRegime-comm neutral avoid     = refl
joinRegime-comm neutral neutral   = refl
joinRegime-comm neutral support   = refl
joinRegime-comm support avoid     = refl
joinRegime-comm support neutral   = refl
joinRegime-comm support support   = refl

joinRegime-assoc : ∀ x y z →
  joinRegime (joinRegime x y) z ≡ joinRegime x (joinRegime y z)
joinRegime-assoc avoid y z = refl
joinRegime-assoc neutral avoid z = refl
joinRegime-assoc neutral neutral avoid = refl
joinRegime-assoc neutral neutral neutral = refl
joinRegime-assoc neutral neutral support = refl
joinRegime-assoc neutral support avoid = refl
joinRegime-assoc neutral support neutral = refl
joinRegime-assoc neutral support support = refl
joinRegime-assoc support avoid z = refl
joinRegime-assoc support neutral avoid = refl
joinRegime-assoc support neutral neutral = refl
joinRegime-assoc support neutral support = refl
joinRegime-assoc support support avoid = refl
joinRegime-assoc support support neutral = refl
joinRegime-assoc support support support = refl

------------------------------------------------------------------------
-- Region aggregation and classification

record RegionClassifier (Vertex Field : Set) : Set₁ where
  field
    Region       : Set
    contains     : Region → Vertex → Bool
    aggregate    : Region → (Vertex → Field) → Field
    classify     : Field → Regime

  classifyField : Region → (Vertex → Field) → Regime
  classifyField r f = classify (aggregate r f)

------------------------------------------------------------------------
-- Robust optimisation over admissible ROM

record SupportObjective
  (Pose Fabric Design Vertex Field Score : Set) : Set₁ where
  field
    admissiblePose   : Pose → Bool
    admissibleFabric : Fabric → Bool
    admissibleDesign : Design → Bool

    riskField        : Pose → Fabric → Design → Vertex → Field
    supportField     : Pose → Fabric → Design → Vertex → Field
    score            : (Vertex → Field) → (Vertex → Field) → Score

  evaluate : Pose → Fabric → Design → Score
  evaluate q p d = score (riskField q p d) (supportField q p d)

record RobustOptimal
  (Pose Fabric Design Vertex Field Score : Set)
  (O : SupportObjective Pose Fabric Design Vertex Field Score)
  : Set₁ where

  private
    module O = SupportObjective O

  field
    noWorse : Score → Score → Set
    chosenFabric : Fabric
    chosenDesign : Design

    chosenFabricAdmissible : O.admissibleFabric chosenFabric ≡ true
    chosenDesignAdmissible : O.admissibleDesign chosenDesign ≡ true

    robust : ∀ q p d →
      O.admissiblePose q ≡ true →
      O.admissibleFabric p ≡ true →
      O.admissibleDesign d ≡ true →
      noWorse
        (O.evaluate q chosenFabric chosenDesign)
        (O.evaluate q p d)

------------------------------------------------------------------------
-- End-to-end promotion contract

record SeaminitSupportPromotion : Set₂ where
  field
    engine : SeaminitKernelEngine

  private
    module E = SeaminitKernelEngine engine

  field
    Design : Set
    Score  : Set

    classifier : RegionClassifier E.Vertex E.Field
    objective  : SupportObjective
      E.Pose E.Fabric Design E.Vertex E.Field Score
    optimum    : RobustOptimal
      E.Pose E.Fabric Design E.Vertex E.Field Score objective

    sharedBasisForAllFields : Bool
    sharedBasisForAllFields≡true : sharedBasisForAllFields ≡ true
    pathDependentROMAccounted : Bool
    pathDependentROMAccounted≡true : pathDependentROMAccounted ≡ true
    fabricInteractionAccounted : Bool
    fabricInteractionAccounted≡true : fabricInteractionAccounted ≡ true
