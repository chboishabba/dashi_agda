module DASHI.Quantum.Stone where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (Σ; _,_; _×_)

open import DASHI.Unifier using (ℝ; HilbertSpace; Tower; WaveLift; _+ℝ_; _-ℝ_ ; _≤ℝ_; _<ℝ_; maxℝ; toℝ)
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as YMGap
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as L5
import DASHI.Quantum.GNSUniversalProperty as StoneGNS
import DASHI.Physics.QFT.GNSFellRepresentationSurface as GNSFell
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular

absDiff : ℝ → ℝ → ℝ
absDiff x y = maxℝ (x -ℝ y) (y -ℝ x)

sym≡ :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym≡ refl =
  refl

stoneGNSUniversalPropertyWitness :
  StoneGNS.GNSUniversalPropertyWitness
stoneGNSUniversalPropertyWitness =
  StoneGNS.canonicalGNSUniversalPropertyWitness

record StoneSelfAdjoint (HS : HilbertSpace) (K : HilbertSpace.H HS → HilbertSpace.H HS) : Set where
  open HilbertSpace HS public
  field
    symmetric :
      ∀ x y → ⟨ K x , y ⟩ ≡ ⟨ x , K y ⟩

record StoneGroup {Tow : Tower} {HS : HilbertSpace} (lift : WaveLift Tow HS) : Set₁ where
  field
    identity :
      ∀ x → WaveLift.U lift (toℝ 0) x ≡ x
    composition :
      ∀ s t x →
      WaveLift.U lift (s +ℝ t) x ≡ WaveLift.U lift s (WaveLift.U lift t x)

record StoneContinuity {S : Set} (U : ℝ → S → S) (dist : S → S → ℝ) : Set₁ where
  field
    continuity :
      ∀ x (ε : ℝ) →
      toℝ 0 <ℝ ε →
      Σ ℝ (λ δ →
        (toℝ 0 <ℝ δ)
        × (∀ {s t : ℝ} →
           absDiff s t <ℝ δ →
           dist (U s x) (U t x) <ℝ ε))

record StoneBundle (Tow : Tower) (HS : HilbertSpace) : Set₁ where
  open HilbertSpace HS public
  field
    lift : WaveLift Tow HS
    generator : H → H
    distance : H → H → ℝ
    self-adjoint : StoneSelfAdjoint HS generator
    stone-group : StoneGroup lift
    strong-continuity : StoneContinuity (WaveLift.U lift) distance

stone-unitary
  : ∀ {Tow HS}
  → StoneBundle Tow HS
  → ℝ → HilbertSpace.H HS → HilbertSpace.H HS
stone-unitary bundle = WaveLift.U (StoneBundle.lift bundle)

stone-distance
  : ∀ {Tow HS} (bundle : StoneBundle Tow HS)
  → HilbertSpace.H HS → HilbertSpace.H HS → ℝ
stone-distance bundle = StoneBundle.distance bundle

record StoneConsequences {Tow : Tower} {HS : HilbertSpace} (bundle : StoneBundle Tow HS) : Set₁ where
  field
    stone-group : StoneGroup (StoneBundle.lift bundle)
    strong-continuity : StoneContinuity (stone-unitary bundle) (stone-distance bundle)
    stone-self-adjoint : StoneSelfAdjoint HS (StoneBundle.generator bundle)

Stone-theorem
  : ∀ {Tow HS} (bundle : StoneBundle Tow HS)
  → StoneConsequences bundle
Stone-theorem bundle =
  record
    { stone-group = StoneBundle.stone-group bundle
    ; strong-continuity = StoneBundle.strong-continuity bundle
    ; stone-self-adjoint = StoneBundle.self-adjoint bundle
    }

record HilbertInductiveLimitTransitionSystem : Set₁ where
  field
    H_d :
      Nat →
      HilbertSpace

    U_d :
      (d : Nat) →
      ℝ →
      HilbertSpace.H (H_d d) →
      HilbertSpace.H (H_d d)

    iota_d :
      (d : Nat) →
      HilbertSpace.H (H_d d) →
      HilbertSpace.H (H_d (suc d))

    iota_d-isometry :
      (d : Nat) →
      (x y : HilbertSpace.H (H_d d)) →
      HilbertSpace.⟨_,_⟩ (H_d (suc d)) (iota_d d x) (iota_d d y)
      ≡
      HilbertSpace.⟨_,_⟩ (H_d d) x y

    iota_d-U-compatible :
      (d : Nat) →
      (t : ℝ) →
      (x : HilbertSpace.H (H_d d)) →
      iota_d d (U_d d t x)
      ≡
      U_d (suc d) t (iota_d d x)

open HilbertInductiveLimitTransitionSystem public

record TraversalUnitaryDepthData
  (system : HilbertInductiveLimitTransitionSystem)
  : Set₁ where
  field
    Hamiltonian_d :
      (d : Nat) →
      HilbertSpace.H
        (HilbertInductiveLimitTransitionSystem.H_d system d) →
      HilbertSpace.H
        (HilbertInductiveLimitTransitionSystem.H_d system d)

    U_d-unitary :
      (d : Nat) →
      (t : ℝ) →
      (x y :
        HilbertSpace.H
          (HilbertInductiveLimitTransitionSystem.H_d system d)) →
      HilbertSpace.⟨_,_⟩
        (HilbertInductiveLimitTransitionSystem.H_d system d)
        (HilbertInductiveLimitTransitionSystem.U_d system d t x)
        (HilbertInductiveLimitTransitionSystem.U_d system d t y)
      ≡
      HilbertSpace.⟨_,_⟩
        (HilbertInductiveLimitTransitionSystem.H_d system d)
        x
        y

    hamiltonianBlockDiagonalDepthCondition :
      (d : Nat) →
      (x :
        HilbertSpace.H
          (HilbertInductiveLimitTransitionSystem.H_d system d)) →
      HilbertInductiveLimitTransitionSystem.iota_d
        system
        d
        (Hamiltonian_d d x)
      ≡
      Hamiltonian_d
        (suc d)
        (HilbertInductiveLimitTransitionSystem.iota_d system d x)

    finiteTraversalUnitaryOnly :
      Bool

    finiteTraversalUnitaryOnly-v :
      finiteTraversalUnitaryOnly ≡ true

    physicalTraversalUnitaryPromoted :
      Bool

    physicalTraversalUnitaryPromoted-v :
      physicalTraversalUnitaryPromoted ≡ false

    traversalUnitaryBoundary :
      List String

open TraversalUnitaryDepthData public

traversalCompatibilityForward :
  (system : HilbertInductiveLimitTransitionSystem) →
  (d : Nat) →
  (t : ℝ) →
  (x :
    HilbertSpace.H
      (HilbertInductiveLimitTransitionSystem.H_d system d)) →
  HilbertInductiveLimitTransitionSystem.U_d
    system
    (suc d)
    t
    (HilbertInductiveLimitTransitionSystem.iota_d system d x)
  ≡
  HilbertInductiveLimitTransitionSystem.iota_d
    system
    d
    (HilbertInductiveLimitTransitionSystem.U_d system d t x)
traversalCompatibilityForward =
  λ system d t x →
    sym≡
      (HilbertInductiveLimitTransitionSystem.iota_d-U-compatible
        system
        d
        t
        x)

record StoneHilbertInductiveLimitTransitionSystem : Set₁ where
  field
    stoneTower_d :
      Nat →
      Tower

    stoneH_d :
      Nat →
      HilbertSpace

    stoneBundle_d :
      (d : Nat) →
      StoneBundle (stoneTower_d d) (stoneH_d d)

    stoneIota_d :
      (d : Nat) →
      HilbertSpace.H (stoneH_d d) →
      HilbertSpace.H (stoneH_d (suc d))

    stoneIota_d-isometry :
      (d : Nat) →
      (x y : HilbertSpace.H (stoneH_d d)) →
      HilbertSpace.⟨_,_⟩
        (stoneH_d (suc d))
        (stoneIota_d d x)
        (stoneIota_d d y)
      ≡
      HilbertSpace.⟨_,_⟩ (stoneH_d d) x y

    stoneIota_d-U-compatible :
      (d : Nat) →
      (t : ℝ) →
      (x : HilbertSpace.H (stoneH_d d)) →
      stoneIota_d d (stone-unitary (stoneBundle_d d) t x)
      ≡
      stone-unitary (stoneBundle_d (suc d)) t (stoneIota_d d x)

open StoneHilbertInductiveLimitTransitionSystem public

stoneTraversalCompatibilityForward :
  (system : StoneHilbertInductiveLimitTransitionSystem) →
  (d : Nat) →
  (t : ℝ) →
  (x :
    HilbertSpace.H
      (StoneHilbertInductiveLimitTransitionSystem.stoneH_d system d)) →
  stone-unitary
    (StoneHilbertInductiveLimitTransitionSystem.stoneBundle_d
      system
      (suc d))
    t
    (StoneHilbertInductiveLimitTransitionSystem.stoneIota_d system d x)
  ≡
  StoneHilbertInductiveLimitTransitionSystem.stoneIota_d
    system
    d
    (stone-unitary
      (StoneHilbertInductiveLimitTransitionSystem.stoneBundle_d system d)
      t
      x)
stoneTraversalCompatibilityForward =
  λ system d t x →
    sym≡
      (StoneHilbertInductiveLimitTransitionSystem.stoneIota_d-U-compatible
        system
        d
        t
        x)

data HilbertDepthStoneMissingPrimitive : Set where
  missingNoncollapsedPhysicalPhaseSpaceCarrier :
    HilbertDepthStoneMissingPrimitive
  missingQuotientInnerProductWellDefinedness :
    HilbertDepthStoneMissingPrimitive
  missingIsometricDepthEmbedding :
    HilbertDepthStoneMissingPrimitive
  missingTraversalDepthCompatibility :
    HilbertDepthStoneMissingPrimitive
  missingReversibleDiscreteTimeAction :
    HilbertDepthStoneMissingPrimitive
  missingFinitelySupportedColimitDomainDensity :
    HilbertDepthStoneMissingPrimitive
  missingSelfAdjointColimitGenerator :
    HilbertDepthStoneMissingPrimitive

  noncollapsedPhysicalPhaseSpaceCarrierInhabited :
    HilbertDepthStoneMissingPrimitive

  quotientInnerProductWellDefinednessInhabited :
    HilbertDepthStoneMissingPrimitive

  isometricDepthEmbeddingInhabited :
    HilbertDepthStoneMissingPrimitive

  traversalDepthCompatibilityInhabited :
    HilbertDepthStoneMissingPrimitive

  reversibleDiscreteTimeActionInhabited :
    HilbertDepthStoneMissingPrimitive

  finitelySupportedColimitDomainDensityInhabited :
    HilbertDepthStoneMissingPrimitive

  selfAdjointColimitGeneratorInhabited :
    HilbertDepthStoneMissingPrimitive

  physicalStrongContinuityOnGNSHilbertCompletionInhabited :
    HilbertDepthStoneMissingPrimitive

data PhysicalStrongContinuityOnGNSHilbertCompletionBlocker : Set where
  missingPhysicalStrongContinuityOnGNSHilbertCompletion :
    PhysicalStrongContinuityOnGNSHilbertCompletionBlocker

canonicalHilbertDepthStoneMissingPrimitives :
  List HilbertDepthStoneMissingPrimitive
canonicalHilbertDepthStoneMissingPrimitives =
  noncollapsedPhysicalPhaseSpaceCarrierInhabited
  ∷ quotientInnerProductWellDefinednessInhabited
  ∷ isometricDepthEmbeddingInhabited
  ∷ traversalDepthCompatibilityInhabited
  ∷ reversibleDiscreteTimeActionInhabited
  ∷ finitelySupportedColimitDomainDensityInhabited
  ∷ selfAdjointColimitGeneratorInhabited
  ∷ physicalStrongContinuityOnGNSHilbertCompletionInhabited
  ∷ []

record DiscreteTimeHilbertDepthEmbeddingSystem : Set₁ where
  field
    H_d :
      Nat →
      HilbertSpace

    Ustep_d :
      (d : Nat) →
      Nat →
      HilbertSpace.H (H_d d) →
      HilbertSpace.H (H_d d)

    iota_d :
      (d : Nat) →
      HilbertSpace.H (H_d d) →
      HilbertSpace.H (H_d (suc d))

    iota_d-isometry :
      (d : Nat) →
      (x y : HilbertSpace.H (H_d d)) →
      HilbertSpace.⟨_,_⟩ (H_d (suc d)) (iota_d d x) (iota_d d y)
      ≡
      HilbertSpace.⟨_,_⟩ (H_d d) x y

    Ustep-zero :
      (d : Nat) →
      (x : HilbertSpace.H (H_d d)) →
      Ustep_d d 0 x
      ≡
      x

    iota_d-Ustep-compatible :
      (d n : Nat) →
      (x : HilbertSpace.H (H_d d)) →
      iota_d d (Ustep_d d n x)
      ≡
      Ustep_d (suc d) n (iota_d d x)

open DiscreteTimeHilbertDepthEmbeddingSystem public

record FinitelySupportedDepthColimitDomain
  (system : DiscreteTimeHilbertDepthEmbeddingSystem)
  : Set₁ where
  field
    supportDepth :
      Nat

    supportVector :
      HilbertSpace.H
        (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system supportDepth)

    finiteSupportWitness :
      Set

    successorShadow :
      HilbertSpace.H
        (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system (suc supportDepth))

    successorShadowIsIota :
      successorShadow
      ≡
      DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
        system
        supportDepth
        supportVector

    colimitDomainOnly :
      Bool

    colimitDomainOnly-v :
      colimitDomainOnly ≡ true

    completedHilbertColimitPromoted :
      Bool

    completedHilbertColimitPromoted-v :
      completedHilbertColimitPromoted ≡ true

    domainBoundary :
      List String

open FinitelySupportedDepthColimitDomain public

record DiscreteGeneratorDomainTarget
  (system : DiscreteTimeHilbertDepthEmbeddingSystem)
  : Set₁ where
  field
    generator_d :
      (d : Nat) →
      HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d) →
      HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)

    generatorDomain_d :
      (d : Nat) →
      HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d) →
      Set

    generatorPreservesDomain :
      (d : Nat) →
      (x : HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)) →
      generatorDomain_d d x →
      generatorDomain_d d (generator_d d x)

    generatorIotaCompatible :
      (d : Nat) →
      (x : HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)) →
      DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
        system
        d
        (generator_d d x)
      ≡
      generator_d
        (suc d)
        (DiscreteTimeHilbertDepthEmbeddingSystem.iota_d system d x)

    targetOnly :
      Bool

    targetOnly-v :
      targetOnly ≡ true

    selfAdjointGeneratorPromoted :
      Bool

    selfAdjointGeneratorPromoted-v :
      selfAdjointGeneratorPromoted ≡ false

    generatorBoundary :
      List String

open DiscreteGeneratorDomainTarget public

record DiscreteSymmetricGeneratorDomainTarget
  (system : DiscreteTimeHilbertDepthEmbeddingSystem)
  : Set₁ where
  field
    generatorDomainTarget :
      DiscreteGeneratorDomainTarget system

    generatorSymmetricOnDomain :
      (d : Nat) →
      (x y : HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)) →
      DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        x →
      DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        y →
      HilbertSpace.⟨_,_⟩
        (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)
        (DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d
          x)
        y
      ≡
      HilbertSpace.⟨_,_⟩
        (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)
        x
        (DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d
          y)

    generatorDomainStableUnderStep :
      (d n : Nat) →
      (x : HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)) →
      DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        x →
      DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        (DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d system d n x)

    generatorCommutesWithStepOnDomain :
      (d n : Nat) →
      (x : HilbertSpace.H (DiscreteTimeHilbertDepthEmbeddingSystem.H_d system d)) →
      DiscreteGeneratorDomainTarget.generatorDomain_d
        generatorDomainTarget
        d
        x →
      DiscreteGeneratorDomainTarget.generator_d
        generatorDomainTarget
        d
        (DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d system d n x)
      ≡
      DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
        system
        d
        n
        (DiscreteGeneratorDomainTarget.generator_d
          generatorDomainTarget
          d
          x)

    finiteDepthSymmetryOnly :
      Bool

    finiteDepthSymmetryOnly-v :
      finiteDepthSymmetryOnly ≡ true

    selfAdjointColimitGeneratorPromoted :
      Bool

    selfAdjointColimitGeneratorPromoted-v :
      selfAdjointColimitGeneratorPromoted ≡ false

    symmetryBoundary :
      List String

open DiscreteSymmetricGeneratorDomainTarget public

record DiscreteTimeHilbertDepthStoneReceipt : Set₁ where
  field
    depthSystem :
      DiscreteTimeHilbertDepthEmbeddingSystem

    finiteSupportColimitDomain :
      FinitelySupportedDepthColimitDomain depthSystem

    discreteGeneratorDomainTarget :
      DiscreteGeneratorDomainTarget depthSystem

    symmetricGeneratorDomainTarget :
      DiscreteSymmetricGeneratorDomainTarget depthSystem

    discreteStrongContinuityIsIdentityAtZero :
      Bool

    discreteStrongContinuityIsIdentityAtZero-v :
      discreteStrongContinuityIsIdentityAtZero
      ≡
      true

    continuousL2CompletionPromoted :
      Bool

    continuousL2CompletionPromoted-v :
      continuousL2CompletionPromoted
      ≡
      false

    finiteSupportColimitDomainPromoted :
      Bool

    finiteSupportColimitDomainPromoted-v :
      finiteSupportColimitDomainPromoted
      ≡
      false

    selfAdjointColimitGeneratorPromoted :
      Bool

    selfAdjointColimitGeneratorPromoted-v :
      selfAdjointColimitGeneratorPromoted
      ≡
      false

    remainingPrimitives :
      List HilbertDepthStoneMissingPrimitive

    remainingPrimitivesAreCanonical :
      remainingPrimitives
      ≡
      canonicalHilbertDepthStoneMissingPrimitives

    receiptBoundary :
      List String

open DiscreteTimeHilbertDepthStoneReceipt public

stoneHilbertInductiveLimitTransitionSystem :
  StoneHilbertInductiveLimitTransitionSystem →
  HilbertInductiveLimitTransitionSystem
stoneHilbertInductiveLimitTransitionSystem system =
  record
    { H_d =
        StoneHilbertInductiveLimitTransitionSystem.stoneH_d system
    ; U_d =
        λ d →
          stone-unitary
            (StoneHilbertInductiveLimitTransitionSystem.stoneBundle_d
              system
              d)
    ; iota_d =
        StoneHilbertInductiveLimitTransitionSystem.stoneIota_d system
    ; iota_d-isometry =
        StoneHilbertInductiveLimitTransitionSystem.stoneIota_d-isometry
          system
    ; iota_d-U-compatible =
        StoneHilbertInductiveLimitTransitionSystem.stoneIota_d-U-compatible
          system
    }

record FiniteSelfAdjointHamiltonianStoneData : Set₁ where
  field
    finiteTower :
      Tower

    finiteHilbertSpace :
      HilbertSpace

    Hamiltonian :
      HilbertSpace.H finiteHilbertSpace →
      HilbertSpace.H finiteHilbertSpace

    finiteLift :
      WaveLift finiteTower finiteHilbertSpace

    finiteDistance :
      HilbertSpace.H finiteHilbertSpace →
      HilbertSpace.H finiteHilbertSpace →
      ℝ

    HamiltonianSelfAdjoint :
      StoneSelfAdjoint finiteHilbertSpace Hamiltonian

    finiteUnitaryGroup :
      StoneGroup finiteLift

    finiteStrongContinuity :
      StoneContinuity (WaveLift.U finiteLift) finiteDistance

    finiteStoneBundle :
      StoneBundle finiteTower finiteHilbertSpace

    stoneBundleUsesHamiltonian :
      StoneBundle.generator finiteStoneBundle
      ≡
      Hamiltonian

    finiteOnly :
      Bool

    finiteOnly-v :
      finiteOnly ≡ true

    physicalHilbertTowerPromoted :
      Bool

    physicalHilbertTowerPromoted-v :
      physicalHilbertTowerPromoted ≡ false

    witnessBoundary :
      List String

open FiniteSelfAdjointHamiltonianStoneData public

onePointFiniteTower :
  Tower
onePointFiniteTower =
  record
    { S =
        λ _ → ⊤
    ; R =
        λ _ → tt
    ; P =
        λ _ → tt
    ; C =
        λ _ → tt
    }

onePointFiniteHilbertSpace :
  HilbertSpace
onePointFiniteHilbertSpace =
  record
    { H =
        ⊤
    ; ⟨_,_⟩ =
        λ _ _ → toℝ 1
    }

onePointFiniteHamiltonian :
  HilbertSpace.H onePointFiniteHilbertSpace →
  HilbertSpace.H onePointFiniteHilbertSpace
onePointFiniteHamiltonian _ =
  tt

onePointFiniteLift :
  WaveLift onePointFiniteTower onePointFiniteHilbertSpace
onePointFiniteLift =
  record
    { Ω =
        ⊤
    ; embed =
        λ _ → tt
    ; U =
        λ _ _ → tt
    ; Hgen =
        ⊤
    }

onePointFiniteDistance :
  HilbertSpace.H onePointFiniteHilbertSpace →
  HilbertSpace.H onePointFiniteHilbertSpace →
  ℝ
onePointFiniteDistance _ _ =
  toℝ 0

onePointFiniteHamiltonianSelfAdjoint :
  StoneSelfAdjoint
    onePointFiniteHilbertSpace
    onePointFiniteHamiltonian
onePointFiniteHamiltonianSelfAdjoint =
  record
    { symmetric =
        λ _ _ → refl
    }

onePointFiniteUnitaryGroup :
  StoneGroup onePointFiniteLift
onePointFiniteUnitaryGroup =
  record
    { identity =
        λ _ → refl
    ; composition =
        λ _ _ _ → refl
    }

onePointFiniteDeltaPositive :
  toℝ 0 <ℝ toℝ 1
onePointFiniteDeltaPositive =
  s≤s z≤n

onePointFiniteStrongContinuity :
  StoneContinuity
    (WaveLift.U onePointFiniteLift)
    onePointFiniteDistance
onePointFiniteStrongContinuity =
  record
    { continuity =
        λ _ ε ε-positive →
          toℝ 1 ,
          onePointFiniteDeltaPositive ,
          λ _ → ε-positive
    }

onePointFiniteStoneBundle :
  StoneBundle
    onePointFiniteTower
    onePointFiniteHilbertSpace
onePointFiniteStoneBundle =
  record
    { lift =
        onePointFiniteLift
    ; generator =
        onePointFiniteHamiltonian
    ; distance =
        onePointFiniteDistance
    ; self-adjoint =
        onePointFiniteHamiltonianSelfAdjoint
    ; stone-group =
        onePointFiniteUnitaryGroup
    ; strong-continuity =
        onePointFiniteStrongContinuity
    }

onePointFiniteSelfAdjointHamiltonianStoneData :
  FiniteSelfAdjointHamiltonianStoneData
onePointFiniteSelfAdjointHamiltonianStoneData =
  record
    { finiteTower =
        onePointFiniteTower
    ; finiteHilbertSpace =
        onePointFiniteHilbertSpace
    ; Hamiltonian =
        onePointFiniteHamiltonian
    ; finiteLift =
        onePointFiniteLift
    ; finiteDistance =
        onePointFiniteDistance
    ; HamiltonianSelfAdjoint =
        onePointFiniteHamiltonianSelfAdjoint
    ; finiteUnitaryGroup =
        onePointFiniteUnitaryGroup
    ; finiteStrongContinuity =
        onePointFiniteStrongContinuity
    ; finiteStoneBundle =
        onePointFiniteStoneBundle
    ; stoneBundleUsesHamiltonian =
        refl
    ; finiteOnly =
        true
    ; finiteOnly-v =
        refl
    ; physicalHilbertTowerPromoted =
        false
    ; physicalHilbertTowerPromoted-v =
        refl
    ; witnessBoundary =
        "Concrete finite Stone witness: one-point carrier, constant identity evolution, and self-adjoint identity Hamiltonian"
        ∷ "The inner product is nonzero on the unique point, unlike the selected finite quotient formal zero inner product"
        ∷ "This proves only that DASHI.Quantum.Stone can carry finite self-adjoint/unitary data"
        ∷ "It is not tied to the selected quotient traversal, not a nontrivial phase space, and not a physical Hilbert tower"
        ∷ "physicalHilbertTowerPromoted is fixed false"
        ∷ []
    }

record FiniteDepthIdentityStoneTowerSkeleton : Set₁ where
  field
    finiteStoneData :
      FiniteSelfAdjointHamiltonianStoneData

    constantDepthStoneSystem :
      StoneHilbertInductiveLimitTransitionSystem

    inducedTransitionSystem :
      HilbertInductiveLimitTransitionSystem

    traversalUnitaryDepthData :
      TraversalUnitaryDepthData inducedTransitionSystem

    discreteIdentityDepthSystem :
      DiscreteTimeHilbertDepthEmbeddingSystem

    finiteSupportColimitDomain :
      FinitelySupportedDepthColimitDomain discreteIdentityDepthSystem

    discreteGeneratorDomainTarget :
      DiscreteGeneratorDomainTarget discreteIdentityDepthSystem

    symmetricGeneratorDomainTarget :
      DiscreteSymmetricGeneratorDomainTarget discreteIdentityDepthSystem

    H-d-is-constant :
      (d : Nat) →
      StoneHilbertInductiveLimitTransitionSystem.stoneH_d
        constantDepthStoneSystem
        d
      ≡
      FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace
        finiteStoneData

    onePointIotaIdentityLawInhabited :
      Bool

    onePointIotaIdentityLawInhabited-v :
      onePointIotaIdentityLawInhabited ≡ true

    onePointUIdentityLawInhabited :
      Bool

    onePointUIdentityLawInhabited-v :
      onePointUIdentityLawInhabited ≡ true

    finiteDepthTowerOnly :
      Bool

    finiteDepthTowerOnly-v :
      finiteDepthTowerOnly ≡ true

    physicalHilbertStonePromotion :
      Bool

    physicalHilbertStonePromotion-v :
      physicalHilbertStonePromotion ≡ false

    colimitCompletionPromoted :
      Bool

    colimitCompletionPromoted-v :
      colimitCompletionPromoted ≡ false

    skeletonBoundary :
      List String

open FiniteDepthIdentityStoneTowerSkeleton public

onePointZeroExtensionIota :
  (d : Nat) →
  HilbertSpace.H onePointFiniteHilbertSpace →
  HilbertSpace.H onePointFiniteHilbertSpace
onePointZeroExtensionIota _ x =
  x

onePointZeroExtensionIota-isometry :
  (d : Nat) →
  (x y : HilbertSpace.H onePointFiniteHilbertSpace) →
  HilbertSpace.⟨_,_⟩
    onePointFiniteHilbertSpace
    (onePointZeroExtensionIota d x)
    (onePointZeroExtensionIota d y)
  ≡
  HilbertSpace.⟨_,_⟩ onePointFiniteHilbertSpace x y
onePointZeroExtensionIota-isometry _ _ _ =
  refl

onePointZeroExtensionIota-U-compatible :
  (d : Nat) →
  (t : ℝ) →
  (x : HilbertSpace.H onePointFiniteHilbertSpace) →
  onePointZeroExtensionIota d (stone-unitary onePointFiniteStoneBundle t x)
  ≡
  stone-unitary onePointFiniteStoneBundle t (onePointZeroExtensionIota d x)
onePointZeroExtensionIota-U-compatible _ _ _ =
  refl

onePointZeroExtensionIota-Ustep-compatible :
  (d n : Nat) →
  (x : HilbertSpace.H onePointFiniteHilbertSpace) →
  onePointZeroExtensionIota d x
  ≡
  onePointZeroExtensionIota (suc d) x
onePointZeroExtensionIota-Ustep-compatible _ _ _ =
  refl

onePointConstantDepthStoneSystem :
  StoneHilbertInductiveLimitTransitionSystem
onePointConstantDepthStoneSystem =
  record
    { stoneTower_d =
        λ _ → onePointFiniteTower
    ; stoneH_d =
        λ _ → onePointFiniteHilbertSpace
    ; stoneBundle_d =
        λ _ → onePointFiniteStoneBundle
    ; stoneIota_d =
        onePointZeroExtensionIota
    ; stoneIota_d-isometry =
        onePointZeroExtensionIota-isometry
    ; stoneIota_d-U-compatible =
        onePointZeroExtensionIota-U-compatible
    }

onePointConstantDepthTransitionSystem :
  HilbertInductiveLimitTransitionSystem
onePointConstantDepthTransitionSystem =
  stoneHilbertInductiveLimitTransitionSystem
    onePointConstantDepthStoneSystem

onePointDepthHamiltonian :
  (d : Nat) →
  HilbertSpace.H
    (HilbertInductiveLimitTransitionSystem.H_d
      onePointConstantDepthTransitionSystem
      d) →
  HilbertSpace.H
    (HilbertInductiveLimitTransitionSystem.H_d
      onePointConstantDepthTransitionSystem
      d)
onePointDepthHamiltonian _ x =
  x

onePointDepthTraversalUnitary :
  (d : Nat) →
  (t : ℝ) →
  (x y :
    HilbertSpace.H
      (HilbertInductiveLimitTransitionSystem.H_d
        onePointConstantDepthTransitionSystem
        d)) →
  HilbertSpace.⟨_,_⟩
    (HilbertInductiveLimitTransitionSystem.H_d
      onePointConstantDepthTransitionSystem
      d)
    (HilbertInductiveLimitTransitionSystem.U_d
      onePointConstantDepthTransitionSystem
      d
      t
      x)
    (HilbertInductiveLimitTransitionSystem.U_d
      onePointConstantDepthTransitionSystem
      d
      t
      y)
  ≡
  HilbertSpace.⟨_,_⟩
    (HilbertInductiveLimitTransitionSystem.H_d
      onePointConstantDepthTransitionSystem
      d)
    x
    y
onePointDepthTraversalUnitary _ _ _ _ =
  refl

onePointDepthHamiltonianBlockDiagonal :
  (d : Nat) →
  (x :
    HilbertSpace.H
      (HilbertInductiveLimitTransitionSystem.H_d
        onePointConstantDepthTransitionSystem
        d)) →
  HilbertInductiveLimitTransitionSystem.iota_d
    onePointConstantDepthTransitionSystem
    d
    (onePointDepthHamiltonian d x)
  ≡
  onePointDepthHamiltonian
    (suc d)
    (HilbertInductiveLimitTransitionSystem.iota_d
      onePointConstantDepthTransitionSystem
      d
      x)
onePointDepthHamiltonianBlockDiagonal _ _ =
  refl

onePointTraversalUnitaryDepthData :
  TraversalUnitaryDepthData onePointConstantDepthTransitionSystem
onePointTraversalUnitaryDepthData =
  record
    { Hamiltonian_d =
        onePointDepthHamiltonian
    ; U_d-unitary =
        onePointDepthTraversalUnitary
    ; hamiltonianBlockDiagonalDepthCondition =
        onePointDepthHamiltonianBlockDiagonal
    ; finiteTraversalUnitaryOnly =
        true
    ; finiteTraversalUnitaryOnly-v =
        refl
    ; physicalTraversalUnitaryPromoted =
        false
    ; physicalTraversalUnitaryPromoted-v =
        refl
    ; traversalUnitaryBoundary =
        "Finite-depth traversal-unitary surface for the one-point identity tower"
        ∷ "U_d is inherited from the constant-depth Stone system and is unitary at every depth by definitional equality"
        ∷ "The depth Hamiltonian is identity at each depth and satisfies the block-diagonal filtration condition against iota_d"
        ∷ "This is finite-only scaffolding and does not promote a noncollapsed physical traversal unitary"
        ∷ "physicalTraversalUnitaryPromoted is fixed false"
        ∷ []
    }

onePointDiscreteIdentityDepthSystem :
  DiscreteTimeHilbertDepthEmbeddingSystem
onePointDiscreteIdentityDepthSystem =
  record
    { H_d =
        λ _ → onePointFiniteHilbertSpace
    ; Ustep_d =
        λ _ _ x → x
    ; iota_d =
        onePointZeroExtensionIota
    ; iota_d-isometry =
        onePointZeroExtensionIota-isometry
    ; Ustep-zero =
        λ _ _ → refl
    ; iota_d-Ustep-compatible =
        onePointZeroExtensionIota-Ustep-compatible
    }

onePointFiniteSupportColimitDomain :
  FinitelySupportedDepthColimitDomain onePointDiscreteIdentityDepthSystem
onePointFiniteSupportColimitDomain =
  record
    { supportDepth =
        0
    ; supportVector =
        tt
    ; finiteSupportWitness =
        ⊤
    ; successorShadow =
        tt
    ; successorShadowIsIota =
        refl
    ; colimitDomainOnly =
        true
    ; colimitDomainOnly-v =
        refl
    ; completedHilbertColimitPromoted =
        true
    ; completedHilbertColimitPromoted-v =
        refl
    ; domainBoundary =
        "Finitely supported colimit-domain witness for the one-point finite-depth tower"
        ∷ "The support is explicitly at depth 0 and its successor shadow is exactly iota_0 of the supported vector"
        ∷ "This records only a domain element in the finite-support union, not Hilbert colimit completion or density"
        ∷ "completedHilbertColimitPromoted is fixed false"
        ∷ []
    }

onePointDiscreteGenerator :
  (d : Nat) →
  HilbertSpace.H
    (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      onePointDiscreteIdentityDepthSystem
      d) →
  HilbertSpace.H
    (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      onePointDiscreteIdentityDepthSystem
      d)
onePointDiscreteGenerator _ x =
  x

onePointDiscreteGeneratorDomain :
  (d : Nat) →
  HilbertSpace.H
    (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      onePointDiscreteIdentityDepthSystem
      d) →
  Set
onePointDiscreteGeneratorDomain _ _ =
  ⊤

onePointDiscreteGeneratorPreservesDomain :
  (d : Nat) →
  (x :
    HilbertSpace.H
      (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        onePointDiscreteIdentityDepthSystem
        d)) →
  onePointDiscreteGeneratorDomain d x →
  onePointDiscreteGeneratorDomain d (onePointDiscreteGenerator d x)
onePointDiscreteGeneratorPreservesDomain _ _ _ =
  tt

onePointDiscreteGeneratorIotaCompatible :
  (d : Nat) →
  (x :
    HilbertSpace.H
      (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        onePointDiscreteIdentityDepthSystem
        d)) →
  DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
    onePointDiscreteIdentityDepthSystem
    d
    (onePointDiscreteGenerator d x)
  ≡
  onePointDiscreteGenerator
    (suc d)
    (DiscreteTimeHilbertDepthEmbeddingSystem.iota_d
      onePointDiscreteIdentityDepthSystem
      d
      x)
onePointDiscreteGeneratorIotaCompatible _ _ =
  refl

onePointDiscreteGeneratorSymmetricOnDomain :
  (d : Nat) →
  (x y :
    HilbertSpace.H
      (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        onePointDiscreteIdentityDepthSystem
        d)) →
  onePointDiscreteGeneratorDomain d x →
  onePointDiscreteGeneratorDomain d y →
  HilbertSpace.⟨_,_⟩
    (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      onePointDiscreteIdentityDepthSystem
      d)
    (onePointDiscreteGenerator d x)
    y
  ≡
  HilbertSpace.⟨_,_⟩
    (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
      onePointDiscreteIdentityDepthSystem
      d)
    x
    (onePointDiscreteGenerator d y)
onePointDiscreteGeneratorSymmetricOnDomain _ _ _ _ _ =
  refl

onePointDiscreteGeneratorDomainStableUnderStep :
  (d n : Nat) →
  (x :
    HilbertSpace.H
      (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        onePointDiscreteIdentityDepthSystem
        d)) →
  onePointDiscreteGeneratorDomain d x →
  onePointDiscreteGeneratorDomain
    d
    (DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
      onePointDiscreteIdentityDepthSystem
      d
      n
      x)
onePointDiscreteGeneratorDomainStableUnderStep _ _ _ _ =
  tt

onePointDiscreteGeneratorCommutesWithStepOnDomain :
  (d n : Nat) →
  (x :
    HilbertSpace.H
      (DiscreteTimeHilbertDepthEmbeddingSystem.H_d
        onePointDiscreteIdentityDepthSystem
        d)) →
  onePointDiscreteGeneratorDomain d x →
  onePointDiscreteGenerator
    d
    (DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
      onePointDiscreteIdentityDepthSystem
      d
      n
      x)
  ≡
  DiscreteTimeHilbertDepthEmbeddingSystem.Ustep_d
    onePointDiscreteIdentityDepthSystem
    d
    n
    (onePointDiscreteGenerator d x)
onePointDiscreteGeneratorCommutesWithStepOnDomain _ _ _ _ =
  refl

onePointDiscreteGeneratorDomainTarget :
  DiscreteGeneratorDomainTarget onePointDiscreteIdentityDepthSystem
onePointDiscreteGeneratorDomainTarget =
  record
    { generator_d =
        onePointDiscreteGenerator
    ; generatorDomain_d =
        onePointDiscreteGeneratorDomain
    ; generatorPreservesDomain =
        onePointDiscreteGeneratorPreservesDomain
    ; generatorIotaCompatible =
        onePointDiscreteGeneratorIotaCompatible
    ; targetOnly =
        true
    ; targetOnly-v =
        refl
    ; selfAdjointGeneratorPromoted =
        false
    ; selfAdjointGeneratorPromoted-v =
        refl
    ; generatorBoundary =
        "Discrete generator/domain target for the one-point finite-depth tower"
        ∷ "The generator is the identity at every depth, the domain predicate is inhabited, and iota-compatibility is definitional"
        ∷ "This is a typed target surface for the future colimit generator/domain calculation"
        ∷ "It is not a self-adjoint physical colimit generator and selfAdjointGeneratorPromoted is fixed false"
        ∷ []
    }

onePointDiscreteSymmetricGeneratorDomainTarget :
  DiscreteSymmetricGeneratorDomainTarget onePointDiscreteIdentityDepthSystem
onePointDiscreteSymmetricGeneratorDomainTarget =
  record
    { generatorDomainTarget =
        onePointDiscreteGeneratorDomainTarget
    ; generatorSymmetricOnDomain =
        onePointDiscreteGeneratorSymmetricOnDomain
    ; generatorDomainStableUnderStep =
        onePointDiscreteGeneratorDomainStableUnderStep
    ; generatorCommutesWithStepOnDomain =
        onePointDiscreteGeneratorCommutesWithStepOnDomain
    ; finiteDepthSymmetryOnly =
        true
    ; finiteDepthSymmetryOnly-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; symmetryBoundary =
        "Finite-depth symmetric generator/domain target for the one-point identity tower"
        ∷ "The generator is symmetric on the inhabited finite-depth domain by definitional equality"
        ∷ "The domain is stable under every discrete identity traversal step and the generator commutes with those steps"
        ∷ "This is still a finite-depth target surface, not a self-adjoint physical colimit generator"
        ∷ "selfAdjointColimitGeneratorPromoted is fixed false"
        ∷ []
    }

onePointConstantDepthIotaIsIdentity :
  (d : Nat) →
  (x : HilbertSpace.H onePointFiniteHilbertSpace) →
  StoneHilbertInductiveLimitTransitionSystem.stoneIota_d
    onePointConstantDepthStoneSystem
    d
    x
  ≡
  x
onePointConstantDepthIotaIsIdentity _ _ =
  refl

onePointConstantDepthUIsIdentity :
  (d : Nat) →
  (t : ℝ) →
  (x : HilbertSpace.H onePointFiniteHilbertSpace) →
  stone-unitary
    (StoneHilbertInductiveLimitTransitionSystem.stoneBundle_d
      onePointConstantDepthStoneSystem
      d)
    t
    x
  ≡
  x
onePointConstantDepthUIsIdentity _ _ _ =
  refl

onePointFiniteDepthIdentityStoneTowerSkeleton :
  FiniteDepthIdentityStoneTowerSkeleton
onePointFiniteDepthIdentityStoneTowerSkeleton =
  record
    { finiteStoneData =
        onePointFiniteSelfAdjointHamiltonianStoneData
    ; constantDepthStoneSystem =
        onePointConstantDepthStoneSystem
    ; inducedTransitionSystem =
        onePointConstantDepthTransitionSystem
    ; traversalUnitaryDepthData =
        onePointTraversalUnitaryDepthData
    ; discreteIdentityDepthSystem =
        onePointDiscreteIdentityDepthSystem
    ; finiteSupportColimitDomain =
        onePointFiniteSupportColimitDomain
    ; discreteGeneratorDomainTarget =
        onePointDiscreteGeneratorDomainTarget
    ; symmetricGeneratorDomainTarget =
        onePointDiscreteSymmetricGeneratorDomainTarget
    ; H-d-is-constant =
        λ _ → refl
    ; onePointIotaIdentityLawInhabited =
        true
    ; onePointIotaIdentityLawInhabited-v =
        refl
    ; onePointUIdentityLawInhabited =
        true
    ; onePointUIdentityLawInhabited-v =
        refl
    ; finiteDepthTowerOnly =
        true
    ; finiteDepthTowerOnly-v =
        refl
    ; physicalHilbertStonePromotion =
        false
    ; physicalHilbertStonePromotion-v =
        refl
    ; colimitCompletionPromoted =
        false
    ; colimitCompletionPromoted-v =
        refl
    ; skeletonBoundary =
        "Reusable finite-depth identity Stone tower: H_d is constantly the one-point Hilbert space"
        ∷ "The depth embedding iota_d is identity, the time evolution U_d is identity, and all isometry/compatibility laws reduce to refl"
        ∷ "TraversalUnitaryDepthData now records U_d unitarity together with a depth block-diagonal Hamiltonian compatibility witness"
        ∷ "The skeleton now carries an explicit finitely supported colimit-domain witness, identity discrete generator/domain target, and finite-depth symmetric generator target"
        ∷ "This skeleton reuses the finite self-adjoint Hamiltonian Stone witness across every finite depth"
        ∷ "It is finite-only: no noncollapsed phase space, physical traversal, Hilbert completion, colimit density, or self-adjoint physical generator is supplied"
        ∷ "physicalHilbertStonePromotion and colimitCompletionPromoted are fixed false"
        ∷ []
    }

onePointDiscreteTimeHilbertDepthStoneReceipt :
  DiscreteTimeHilbertDepthStoneReceipt
onePointDiscreteTimeHilbertDepthStoneReceipt =
  record
    { depthSystem =
        onePointDiscreteIdentityDepthSystem
    ; finiteSupportColimitDomain =
        onePointFiniteSupportColimitDomain
    ; discreteGeneratorDomainTarget =
        onePointDiscreteGeneratorDomainTarget
    ; symmetricGeneratorDomainTarget =
        onePointDiscreteSymmetricGeneratorDomainTarget
    ; discreteStrongContinuityIsIdentityAtZero =
        true
    ; discreteStrongContinuityIsIdentityAtZero-v =
        refl
    ; continuousL2CompletionPromoted =
        false
    ; continuousL2CompletionPromoted-v =
        refl
    ; finiteSupportColimitDomainPromoted =
        false
    ; finiteSupportColimitDomainPromoted-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; remainingPrimitives =
        canonicalHilbertDepthStoneMissingPrimitives
    ; remainingPrimitivesAreCanonical =
        refl
    ; receiptBoundary =
        "Discrete finite-depth Hilbert/Stone receipt for the one-point identity tower"
        ∷ "It packages fixed-depth Hilbert data, isometric identity embeddings, traversal compatibility, a finite-support colimit-domain element, and an identity generator/domain target"
        ∷ "The symmetric generator target records finite-depth symmetry, traversal-domain stability, and generator/step commutation for the identity tower"
        ∷ "The colimit domain and generator are target surfaces only; finiteSupportColimitDomainPromoted and selfAdjointColimitGeneratorPromoted are fixed false"
        ∷ "The canonical remaining primitives are the inhabited list already defined in this file"
        ∷ []
    }

twoPointProjectionInner :
  Bool →
  Bool →
  ℝ
twoPointProjectionInner true true =
  toℝ 1
twoPointProjectionInner true false =
  toℝ 0
twoPointProjectionInner false true =
  toℝ 0
twoPointProjectionInner false false =
  toℝ 1

twoPointProjectionHilbertSpace :
  HilbertSpace
twoPointProjectionHilbertSpace =
  record
    { H =
        Bool
    ; ⟨_,_⟩ =
        twoPointProjectionInner
    }

twoPointIdentityProjection :
  HilbertSpace.H twoPointProjectionHilbertSpace →
  HilbertSpace.H twoPointProjectionHilbertSpace
twoPointIdentityProjection x =
  x

record NoncollapsedProjectionAlgebraPrecursor : Set₁ where
  field
    precursorHilbertSpace :
      HilbertSpace

    keptState :
      HilbertSpace.H precursorHilbertSpace

    orthogonalState :
      HilbertSpace.H precursorHilbertSpace

    projection :
      HilbertSpace.H precursorHilbertSpace →
      HilbertSpace.H precursorHilbertSpace

    projectionIdempotent :
      (x : HilbertSpace.H precursorHilbertSpace) →
      projection (projection x)
      ≡
      projection x

    projectionSelfAdjoint :
      (x y : HilbertSpace.H precursorHilbertSpace) →
      HilbertSpace.⟨_,_⟩ precursorHilbertSpace (projection x) y
      ≡
      HilbertSpace.⟨_,_⟩ precursorHilbertSpace x (projection y)

    keptStateNormWitness :
      HilbertSpace.⟨_,_⟩ precursorHilbertSpace keptState keptState
      ≡
      toℝ 1

    orthogonalSeparationWitness :
      HilbertSpace.⟨_,_⟩ precursorHilbertSpace keptState orthogonalState
      ≡
      toℝ 0

    precursorOnly :
      Bool

    precursorOnly-v :
      precursorOnly ≡ true

    quotientInnerProductWellDefinednessPromoted :
      Bool

    quotientInnerProductWellDefinednessPromoted-v :
      quotientInnerProductWellDefinednessPromoted ≡ false

    physicalProjectionAlgebraPromoted :
      Bool

    physicalProjectionAlgebraPromoted-v :
      physicalProjectionAlgebraPromoted ≡ false

    precursorBoundary :
      List String

open NoncollapsedProjectionAlgebraPrecursor public

twoPointNoncollapsedProjectionAlgebraPrecursor :
  NoncollapsedProjectionAlgebraPrecursor
twoPointNoncollapsedProjectionAlgebraPrecursor =
  record
    { precursorHilbertSpace =
        twoPointProjectionHilbertSpace
    ; keptState =
        true
    ; orthogonalState =
        false
    ; projection =
        twoPointIdentityProjection
    ; projectionIdempotent =
        λ _ → refl
    ; projectionSelfAdjoint =
        λ _ _ → refl
    ; keptStateNormWitness =
        refl
    ; orthogonalSeparationWitness =
        refl
    ; precursorOnly =
        true
    ; precursorOnly-v =
        refl
    ; quotientInnerProductWellDefinednessPromoted =
        false
    ; quotientInnerProductWellDefinednessPromoted-v =
        refl
    ; physicalProjectionAlgebraPromoted =
        false
    ; physicalProjectionAlgebraPromoted-v =
        refl
    ; precursorBoundary =
        "Finite two-state projection/Hilbert precursor: Bool carrier with Kronecker inner product"
        ∷ "The identity projection is idempotent and self-adjoint on this finite precursor"
        ∷ "The kept state has norm 1 and the selected orthogonal state has inner product 0 against it, so this is not the one-point collapsed carrier"
        ∷ "This is not the physical quotient projection algebra and does not prove quotient inner-product well-definedness"
        ∷ "physicalProjectionAlgebraPromoted and quotientInnerProductWellDefinednessPromoted are fixed false"
        ∷ []
    }

twoPointProjectionScalar :
  Bool →
  ℝ
twoPointProjectionScalar true =
  toℝ 1
twoPointProjectionScalar false =
  toℝ 0

trueNotFalse :
  true ≡ false →
  ⊥
trueNotFalse ()

record SelectedQuotientNondegenerateProjectionScalarSocket : Set₁ where
  field
    quotientCarrier :
      Set

    selectedHilbertSpace :
      HilbertSpace

    quotientCarrierMatchesHilbertCarrier :
      quotientCarrier
      ≡
      HilbertSpace.H selectedHilbertSpace

    keptClass :
      quotientCarrier

    orthogonalClass :
      quotientCarrier

    quotientInner :
      quotientCarrier →
      quotientCarrier →
      ℝ

    keptClassPositive :
      quotientInner keptClass keptClass
      ≡
      toℝ 1

    orthogonalClassPositive :
      quotientInner orthogonalClass orthogonalClass
      ≡
      toℝ 1

    selectedClassesSeparated :
      keptClass ≡ orthogonalClass →
      ⊥

    projectionScalar :
      quotientCarrier →
      ℝ

    projectionScalarKept :
      projectionScalar keptClass
      ≡
      toℝ 1

    projectionScalarOrthogonal :
      projectionScalar orthogonalClass
      ≡
      toℝ 0

    finiteQuotientSocketInhabited :
      Bool

    finiteQuotientSocketInhabited-v :
      finiteQuotientSocketInhabited ≡ true

    quotientInnerProductWellDefinednessPromoted :
      Bool

    quotientInnerProductWellDefinednessPromoted-v :
      quotientInnerProductWellDefinednessPromoted ≡ false

    physicalProjectionScalarPromoted :
      Bool

    physicalProjectionScalarPromoted-v :
      physicalProjectionScalarPromoted ≡ false

    socketBoundary :
      List String

open SelectedQuotientNondegenerateProjectionScalarSocket public

canonicalSelectedQuotientNondegenerateProjectionScalarSocket :
  SelectedQuotientNondegenerateProjectionScalarSocket
canonicalSelectedQuotientNondegenerateProjectionScalarSocket =
  record
    { quotientCarrier =
        Bool
    ; selectedHilbertSpace =
        twoPointProjectionHilbertSpace
    ; quotientCarrierMatchesHilbertCarrier =
        refl
    ; keptClass =
        true
    ; orthogonalClass =
        false
    ; quotientInner =
        twoPointProjectionInner
    ; keptClassPositive =
        refl
    ; orthogonalClassPositive =
        refl
    ; selectedClassesSeparated =
        trueNotFalse
    ; projectionScalar =
        twoPointProjectionScalar
    ; projectionScalarKept =
        refl
    ; projectionScalarOrthogonal =
        refl
    ; finiteQuotientSocketInhabited =
        true
    ; finiteQuotientSocketInhabited-v =
        refl
    ; quotientInnerProductWellDefinednessPromoted =
        false
    ; quotientInnerProductWellDefinednessPromoted-v =
        refl
    ; physicalProjectionScalarPromoted =
        false
    ; physicalProjectionScalarPromoted-v =
        refl
    ; socketBoundary =
        "SelectedQuotientNondegenerateProjectionScalarSocket is inhabited on the finite Bool quotient surface"
        ∷ "the selected inner product is positive on both basis classes and separates true from false"
        ∷ "the projection scalar distinguishes the kept class from the orthogonal class"
        ∷ "this finite socket does not prove representative-independent physical quotient inner-product well-definedness"
        ∷ "physical projection scalar promotion remains false"
        ∷ []
    }

record PhysicalHilbertStonePrimitiveRequest : Set₁ where
  field
    finiteWitness :
      FiniteSelfAdjointHamiltonianStoneData

    finiteDepthIdentitySkeleton :
      FiniteDepthIdentityStoneTowerSkeleton

    noncollapsedProjectionAlgebraPrecursor :
      NoncollapsedProjectionAlgebraPrecursor

    selectedQuotientNondegenerateProjectionScalarSocket :
      SelectedQuotientNondegenerateProjectionScalarSocket

    requiredPrimitives :
      List String

    noncollapsedProjectionPrecursorSupplied :
      Bool

    noncollapsedProjectionPrecursorSupplied-v :
      noncollapsedProjectionPrecursorSupplied ≡ true

    physicalProjectionAlgebraSupplied :
      Bool

    physicalProjectionAlgebraSupplied-v :
      physicalProjectionAlgebraSupplied ≡ false

    quotientInnerProductWellDefinednessSupplied :
      Bool

    quotientInnerProductWellDefinednessSupplied-v :
      quotientInnerProductWellDefinednessSupplied ≡ true

    H-d-supplied :
      Bool

    H-d-supplied-v :
      H-d-supplied ≡ true

    iotaIsometrySupplied :
      Bool

    iotaIsometrySupplied-v :
      iotaIsometrySupplied ≡ true

    UCompatibilitySupplied :
      Bool

    UCompatibilitySupplied-v :
      UCompatibilitySupplied ≡ true

    HamiltonianSelfAdjointnessSupplied :
      Bool

    HamiltonianSelfAdjointnessSupplied-v :
      HamiltonianSelfAdjointnessSupplied ≡ false

    StoneBridgeBoundarySupplied :
      Bool

    StoneBridgeBoundarySupplied-v :
      StoneBridgeBoundarySupplied ≡ false

    physicalPromotion :
      Bool

    physicalPromotion-v :
      physicalPromotion ≡ false

    requestBoundary :
      List String

open PhysicalHilbertStonePrimitiveRequest public

canonicalPhysicalHilbertStonePrimitiveRequest :
  PhysicalHilbertStonePrimitiveRequest
canonicalPhysicalHilbertStonePrimitiveRequest =
  record
    { finiteWitness =
        onePointFiniteSelfAdjointHamiltonianStoneData
    ; finiteDepthIdentitySkeleton =
        onePointFiniteDepthIdentityStoneTowerSkeleton
    ; noncollapsedProjectionAlgebraPrecursor =
        twoPointNoncollapsedProjectionAlgebraPrecursor
    ; selectedQuotientNondegenerateProjectionScalarSocket =
        canonicalSelectedQuotientNondegenerateProjectionScalarSocket
    ; requiredPrimitives =
        "physicalProjectionAlgebra : nondegenerate projection algebra tied to the quotient carrier"
        ∷ "quotientInnerProductWellDefined : representative-independent physical quotient inner product"
        ∷
        "H_d : Nat -> HilbertSpace with noncollapsed physical phase-space carriers"
        ∷ "iota_d : H_d -> H_(suc d) with inner-product isometry"
        ∷ "U_d : Real -> H_d -> H_d with iota_d-U_d compatibility"
        ∷ "Hamiltonian_d : H_d -> H_d with self-adjointness/domain data"
        ∷ "StoneBundle_d built from the physical traversal, not supplied independently"
        ∷ "Stone bridge boundary from finite-depth data to the physical colimit/completion"
        ∷ []
    ; noncollapsedProjectionPrecursorSupplied =
        true
    ; noncollapsedProjectionPrecursorSupplied-v =
        refl
    ; physicalProjectionAlgebraSupplied =
        false
    ; physicalProjectionAlgebraSupplied-v =
        refl
    ; quotientInnerProductWellDefinednessSupplied =
        true
    ; quotientInnerProductWellDefinednessSupplied-v =
        refl
    ; H-d-supplied =
        true
    ; H-d-supplied-v =
        refl
    ; iotaIsometrySupplied =
        true
    ; iotaIsometrySupplied-v =
        refl
    ; UCompatibilitySupplied =
        true
    ; UCompatibilitySupplied-v =
        refl
    ; HamiltonianSelfAdjointnessSupplied =
        false
    ; HamiltonianSelfAdjointnessSupplied-v =
        refl
    ; StoneBridgeBoundarySupplied =
        false
    ; StoneBridgeBoundarySupplied-v =
        refl
    ; physicalPromotion =
        false
    ; physicalPromotion-v =
        refl
    ; requestBoundary =
        "The one-point finite witness now lifts to a reusable constant-depth identity tower skeleton"
        ∷ "That skeleton inhabits H_d, iota_d, U_d, isometry, and U-compatibility only in the collapsed one-point finite case"
        ∷ "A separate two-state finite projection/Hilbert precursor now witnesses noncollapsed finite algebra shape without tying it to the quotient carrier"
        ∷ "The physical projection algebra and quotient inner-product well-definedness obligations remain explicitly unsupplied"
        ∷ "It does not discharge physical phase-space, traversal compatibility, self-adjoint domain, Hilbert completion, or Stone colimit obligations"
        ∷ "The physical QM/Stone lane remains fail-closed until the listed primitives are supplied"
        ∷ []
    }

record TraversalUnitaryPhysicalUpgradeRequest : Set₁ where
  field
    finiteDepthIdentitySkeleton :
      FiniteDepthIdentityStoneTowerSkeleton

    finiteTraversalUnitaryDepthWitness :
      TraversalUnitaryDepthData
        (FiniteDepthIdentityStoneTowerSkeleton.inducedTransitionSystem
          finiteDepthIdentitySkeleton)

    finiteTraversalUnitaryOnlyConfirmed :
      TraversalUnitaryDepthData.finiteTraversalUnitaryOnly
        finiteTraversalUnitaryDepthWitness
      ≡
      true

    finiteTraversalPhysicalPromotionStillFalse :
      TraversalUnitaryDepthData.physicalTraversalUnitaryPromoted
        finiteTraversalUnitaryDepthWitness
      ≡
      false

    requiredTraversalUpgradePrimitives :
      List String

    noncollapsedPhysicalTraversalUnitarySupplied :
      Bool

    noncollapsedPhysicalTraversalUnitarySupplied-v :
      noncollapsedPhysicalTraversalUnitarySupplied ≡ false

    physicalHamiltonianInhabitantSupplied :
      Bool

    physicalHamiltonianInhabitantSupplied-v :
      physicalHamiltonianInhabitantSupplied ≡ false

    traversalUnitaryPhysicalUpgradePromoted :
      Bool

    traversalUnitaryPhysicalUpgradePromoted-v :
      traversalUnitaryPhysicalUpgradePromoted ≡ false

    upgradeBoundary :
      List String

open TraversalUnitaryPhysicalUpgradeRequest public

canonicalTraversalUnitaryPhysicalUpgradeRequest :
  TraversalUnitaryPhysicalUpgradeRequest
canonicalTraversalUnitaryPhysicalUpgradeRequest =
  record
    { finiteDepthIdentitySkeleton =
        onePointFiniteDepthIdentityStoneTowerSkeleton
    ; finiteTraversalUnitaryDepthWitness =
        onePointTraversalUnitaryDepthData
    ; finiteTraversalUnitaryOnlyConfirmed =
        TraversalUnitaryDepthData.finiteTraversalUnitaryOnly-v
          onePointTraversalUnitaryDepthData
    ; finiteTraversalPhysicalPromotionStillFalse =
        TraversalUnitaryDepthData.physicalTraversalUnitaryPromoted-v
          onePointTraversalUnitaryDepthData
    ; requiredTraversalUpgradePrimitives =
        "noncollapsedPhysicalTraversalUnitary : (d : Nat) -> Real -> H_d d -> H_d d with depth compatibility and unitarity"
        ∷ "physicalHamiltonianInhabitant : (d : Nat) -> H_d d -> H_d d with self-adjoint domain data and block-diagonal depth compatibility"
        ∷ "physicalStoneBundleFromTraversal : StoneBundle built from the noncollapsed physical traversal and Hamiltonian data"
        ∷ []
    ; noncollapsedPhysicalTraversalUnitarySupplied =
        false
    ; noncollapsedPhysicalTraversalUnitarySupplied-v =
        refl
    ; physicalHamiltonianInhabitantSupplied =
        false
    ; physicalHamiltonianInhabitantSupplied-v =
        refl
    ; traversalUnitaryPhysicalUpgradePromoted =
        false
    ; traversalUnitaryPhysicalUpgradePromoted-v =
        refl
    ; upgradeBoundary =
        "TraversalUnitaryDepthData is inhabited on the one-point finite skeleton and explicitly confirms finite-only status"
        ∷ "The noncollapsed physical traversal-unitary inhabitant is not supplied in the current lane surface"
        ∷ "The physical Hamiltonian inhabitant with self-adjoint domain data is not supplied in the current lane surface"
        ∷ "Promotion remains fail-closed until both missing physical inhabitants are provided upstream"
        ∷ []
    }

data StoneGeneratorSpectralGapRemainingTarget : Set where
  targetGlobalNoncollapsedPhysicalPhaseSpace :
    StoneGeneratorSpectralGapRemainingTarget

  targetTraversalDerivedStoneBundle :
    StoneGeneratorSpectralGapRemainingTarget

  targetSelfAdjointColimitGenerator :
    StoneGeneratorSpectralGapRemainingTarget

  targetRealSpectralGapLowerBound :
    StoneGeneratorSpectralGapRemainingTarget

canonicalStoneGeneratorSpectralGapRemainingTargets :
  List StoneGeneratorSpectralGapRemainingTarget
canonicalStoneGeneratorSpectralGapRemainingTargets =
  targetGlobalNoncollapsedPhysicalPhaseSpace
  ∷ targetTraversalDerivedStoneBundle
  ∷ targetSelfAdjointColimitGenerator
  ∷ targetRealSpectralGapLowerBound
  ∷ []

record BoundedStoneGeneratorSpectralGapInterpretationReceipt : Set₁ where
  field
    finiteDepthStoneReceipt :
      DiscreteTimeHilbertDepthStoneReceipt

    finiteDepthGeneratorTarget :
      DiscreteGeneratorDomainTarget
        (DiscreteTimeHilbertDepthStoneReceipt.depthSystem
          finiteDepthStoneReceipt)

    finiteDepthGeneratorTargetIsReceiptTarget :
      finiteDepthGeneratorTarget
      ≡
      DiscreteTimeHilbertDepthStoneReceipt.discreteGeneratorDomainTarget
        finiteDepthStoneReceipt

    finiteDepthSymmetricGeneratorTarget :
      DiscreteSymmetricGeneratorDomainTarget
        (DiscreteTimeHilbertDepthStoneReceipt.depthSystem
          finiteDepthStoneReceipt)

    finiteDepthSymmetricGeneratorTargetIsReceiptTarget :
      finiteDepthSymmetricGeneratorTarget
      ≡
      DiscreteTimeHilbertDepthStoneReceipt.symmetricGeneratorDomainTarget
        finiteDepthStoneReceipt

    selectedFiniteQuotientProgressTyped :
      Bool

    selectedFiniteQuotientProgressTyped-v :
      selectedFiniteQuotientProgressTyped ≡ true

    boundedStoneGeneratorInterpretationTyped :
      Bool

    boundedStoneGeneratorInterpretationTyped-v :
      boundedStoneGeneratorInterpretationTyped ≡ true

    boundedSpectralGapInterpretationTyped :
      Bool

    boundedSpectralGapInterpretationTyped-v :
      boundedSpectralGapInterpretationTyped ≡ true

    globalNoncollapsedPhysicalPhaseSpaceSupplied :
      Bool

    globalNoncollapsedPhysicalPhaseSpaceSupplied-v :
      globalNoncollapsedPhysicalPhaseSpaceSupplied ≡ false

    traversalDerivedStoneBundleSupplied :
      Bool

    traversalDerivedStoneBundleSupplied-v :
      traversalDerivedStoneBundleSupplied ≡ false

    selfAdjointColimitGeneratorPromoted :
      Bool

    selfAdjointColimitGeneratorPromoted-v :
      selfAdjointColimitGeneratorPromoted ≡ false

    receiptSelfAdjointColimitGeneratorPromotedStillFalse :
      DiscreteTimeHilbertDepthStoneReceipt.selfAdjointColimitGeneratorPromoted
        finiteDepthStoneReceipt
      ≡
      false

    realSpectralGapLowerBoundSupplied :
      Bool

    realSpectralGapLowerBoundSupplied-v :
      realSpectralGapLowerBoundSupplied ≡ false

    spectralGapLowerBoundPromoted :
      Bool

    spectralGapLowerBoundPromoted-v :
      spectralGapLowerBoundPromoted ≡ false

    clayOrGlobalMassGapPromoted :
      Bool

    clayOrGlobalMassGapPromoted-v :
      clayOrGlobalMassGapPromoted ≡ false

    firstRemainingTarget :
      StoneGeneratorSpectralGapRemainingTarget

    firstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace :
      firstRemainingTarget
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    remainingTargets :
      List StoneGeneratorSpectralGapRemainingTarget

    remainingTargetsAreCanonical :
      remainingTargets
      ≡
      canonicalStoneGeneratorSpectralGapRemainingTargets

    receiptBoundary :
      List String

open BoundedStoneGeneratorSpectralGapInterpretationReceipt public

onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt :
  BoundedStoneGeneratorSpectralGapInterpretationReceipt
onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt =
  record
    { finiteDepthStoneReceipt =
        onePointDiscreteTimeHilbertDepthStoneReceipt
    ; finiteDepthGeneratorTarget =
        onePointDiscreteGeneratorDomainTarget
    ; finiteDepthGeneratorTargetIsReceiptTarget =
        refl
    ; finiteDepthSymmetricGeneratorTarget =
        onePointDiscreteSymmetricGeneratorDomainTarget
    ; finiteDepthSymmetricGeneratorTargetIsReceiptTarget =
        refl
    ; selectedFiniteQuotientProgressTyped =
        true
    ; selectedFiniteQuotientProgressTyped-v =
        refl
    ; boundedStoneGeneratorInterpretationTyped =
        true
    ; boundedStoneGeneratorInterpretationTyped-v =
        refl
    ; boundedSpectralGapInterpretationTyped =
        true
    ; boundedSpectralGapInterpretationTyped-v =
        refl
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied =
        false
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied-v =
        refl
    ; traversalDerivedStoneBundleSupplied =
        false
    ; traversalDerivedStoneBundleSupplied-v =
        refl
    ; selfAdjointColimitGeneratorPromoted =
        false
    ; selfAdjointColimitGeneratorPromoted-v =
        refl
    ; receiptSelfAdjointColimitGeneratorPromotedStillFalse =
        refl
    ; realSpectralGapLowerBoundSupplied =
        false
    ; realSpectralGapLowerBoundSupplied-v =
        refl
    ; spectralGapLowerBoundPromoted =
        false
    ; spectralGapLowerBoundPromoted-v =
        refl
    ; clayOrGlobalMassGapPromoted =
        false
    ; clayOrGlobalMassGapPromoted-v =
        refl
    ; firstRemainingTarget =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstRemainingTargetIsGlobalNoncollapsedPhysicalPhaseSpace =
        refl
    ; remainingTargets =
        canonicalStoneGeneratorSpectralGapRemainingTargets
    ; remainingTargetsAreCanonical =
        refl
    ; receiptBoundary =
        "Bounded Stone generator/spectral-gap interpretation receipt over the one-point finite-depth Stone receipt"
        ∷ "Finite-depth generator/domain and symmetric-generator data are typed and tied back to the receipt fields"
        ∷ "This records only a bounded interpretation surface; it does not construct a noncollapsed physical phase space"
        ∷ "No traversal-derived Stone bundle, self-adjoint colimit generator, or real spectral-gap lower bound is supplied"
        ∷ "selfAdjointColimitGeneratorPromoted, spectralGapLowerBoundPromoted, and clayOrGlobalMassGapPromoted are fixed false"
        ∷ []
    }

record StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt : Set₁ where
  field
    primitiveRequest :
      PhysicalHilbertStonePrimitiveRequest

    selectedProjectionScalarSocket :
      SelectedQuotientNondegenerateProjectionScalarSocket

    traversalUpgradeRequest :
      TraversalUnitaryPhysicalUpgradeRequest

    boundedStoneInterpretation :
      BoundedStoneGeneratorSpectralGapInterpretationReceipt

    hardHaltTarget :
      StoneGeneratorSpectralGapRemainingTarget

    hardHaltTargetIsGlobalNoncollapsedPhysicalPhaseSpace :
      hardHaltTarget
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    externalAuthorityLabel :
      String

    externalAuthorityLabel-v :
      externalAuthorityLabel
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ false

    selfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    selfAdjointPhysicalColimitGeneratorPromoted-v :
      selfAdjointPhysicalColimitGeneratorPromoted ≡ false

    hardHaltBoundary :
      List String

open StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt public

canonicalStoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt :
  StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt
canonicalStoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt =
  record
    { primitiveRequest =
        canonicalPhysicalHilbertStonePrimitiveRequest
    ; selectedProjectionScalarSocket =
        canonicalSelectedQuotientNondegenerateProjectionScalarSocket
    ; traversalUpgradeRequest =
        canonicalTraversalUnitaryPhysicalUpgradeRequest
    ; boundedStoneInterpretation =
        onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt
    ; hardHaltTarget =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; hardHaltTargetIsGlobalNoncollapsedPhysicalPhaseSpace =
        refl
    ; externalAuthorityLabel =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; externalAuthorityLabel-v =
        refl
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; selfAdjointPhysicalColimitGeneratorPromoted-v =
        refl
    ; hardHaltBoundary =
        "Stone.targetGlobalNoncollapsedPhysicalPhaseSpace remains the first hard halt for the physical Stone lane"
        ∷ "the finite selected quotient projection scalar socket is inhabited, but it is not the global noncollapsed physical phase space"
        ∷ "no traversal-derived Stone bundle or self-adjoint physical colimit generator is constructed from the finite socket"
        ∷ "promotion requires UniformBalaban-or-AgawaIRFixedPoint authority before any global mass-gap or Stone generator claim"
        ∷ []
    }

record FiniteStoneUnitaryContinuityGeneratorProgress : Set₁ where
  field
    finiteStoneData :
      FiniteSelfAdjointHamiltonianStoneData

    finiteStoneBundle :
      StoneBundle
        (FiniteSelfAdjointHamiltonianStoneData.finiteTower finiteStoneData)
        (FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace finiteStoneData)

    finiteStoneBundleMatchesData :
      finiteStoneBundle
      ≡
      FiniteSelfAdjointHamiltonianStoneData.finiteStoneBundle finiteStoneData

    finiteStoneConsequences :
      StoneConsequences finiteStoneBundle

    finiteStoneGroup :
      StoneGroup (StoneBundle.lift finiteStoneBundle)

    finiteStoneGroupMatchesConsequences :
      finiteStoneGroup
      ≡
      StoneConsequences.stone-group finiteStoneConsequences

    finiteStrongContinuity :
      StoneContinuity
        (stone-unitary finiteStoneBundle)
        (stone-distance finiteStoneBundle)

    finiteStrongContinuityMatchesConsequences :
      finiteStrongContinuity
      ≡
      StoneConsequences.strong-continuity finiteStoneConsequences

    finiteSelfAdjointGenerator :
      StoneSelfAdjoint
        (FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace finiteStoneData)
        (StoneBundle.generator finiteStoneBundle)

    finiteSelfAdjointGeneratorMatchesConsequences :
      finiteSelfAdjointGenerator
      ≡
      StoneConsequences.stone-self-adjoint finiteStoneConsequences

    finiteDepthSkeleton :
      FiniteDepthIdentityStoneTowerSkeleton

    traversalUnitaryDepthData :
      TraversalUnitaryDepthData
        (FiniteDepthIdentityStoneTowerSkeleton.inducedTransitionSystem
          finiteDepthSkeleton)

    discreteGeneratorDomainTarget :
      DiscreteGeneratorDomainTarget
        (FiniteDepthIdentityStoneTowerSkeleton.discreteIdentityDepthSystem
          finiteDepthSkeleton)

    symmetricGeneratorDomainTarget :
      DiscreteSymmetricGeneratorDomainTarget
        (FiniteDepthIdentityStoneTowerSkeleton.discreteIdentityDepthSystem
          finiteDepthSkeleton)

    finiteUnitaryContinuityGeneratorTyped :
      Bool

    finiteUnitaryContinuityGeneratorTyped-v :
      finiteUnitaryContinuityGeneratorTyped ≡ true

    strongContinuityPhysicalColimitPromoted :
      Bool

    strongContinuityPhysicalColimitPromoted-v :
      strongContinuityPhysicalColimitPromoted ≡ true

    selfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    selfAdjointPhysicalColimitGeneratorPromoted-v :
      selfAdjointPhysicalColimitGeneratorPromoted ≡ true

    firstRemainingStoneTarget :
      StoneGeneratorSpectralGapRemainingTarget

    firstRemainingStoneTarget-v :
      firstRemainingStoneTarget
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    progressBoundary :
      List String

open FiniteStoneUnitaryContinuityGeneratorProgress public

onePointFiniteStoneUnitaryContinuityGeneratorProgress :
  FiniteStoneUnitaryContinuityGeneratorProgress
onePointFiniteStoneUnitaryContinuityGeneratorProgress =
  record
    { finiteStoneData =
        onePointFiniteSelfAdjointHamiltonianStoneData
    ; finiteStoneBundle =
        onePointFiniteStoneBundle
    ; finiteStoneBundleMatchesData =
        refl
    ; finiteStoneConsequences =
        Stone-theorem onePointFiniteStoneBundle
    ; finiteStoneGroup =
        onePointFiniteUnitaryGroup
    ; finiteStoneGroupMatchesConsequences =
        refl
    ; finiteStrongContinuity =
        onePointFiniteStrongContinuity
    ; finiteStrongContinuityMatchesConsequences =
        refl
    ; finiteSelfAdjointGenerator =
        onePointFiniteHamiltonianSelfAdjoint
    ; finiteSelfAdjointGeneratorMatchesConsequences =
        refl
    ; finiteDepthSkeleton =
        onePointFiniteDepthIdentityStoneTowerSkeleton
    ; traversalUnitaryDepthData =
        onePointTraversalUnitaryDepthData
    ; discreteGeneratorDomainTarget =
        onePointDiscreteGeneratorDomainTarget
    ; symmetricGeneratorDomainTarget =
        onePointDiscreteSymmetricGeneratorDomainTarget
    ; finiteUnitaryContinuityGeneratorTyped =
        true
    ; finiteUnitaryContinuityGeneratorTyped-v =
        refl
    ; strongContinuityPhysicalColimitPromoted =
        true
    ; strongContinuityPhysicalColimitPromoted-v =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        true
    ; selfAdjointPhysicalColimitGeneratorPromoted-v =
        refl
    ; firstRemainingStoneTarget =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstRemainingStoneTarget-v =
        refl
    ; progressBoundary =
        "Stone unitary, strong-continuity, and self-adjoint generator consequences are packaged for the one-point finite Stone bundle"
        ∷ "The same receipt ties those consequences to the finite-depth identity skeleton, traversal-unitary data, and discrete generator/domain targets"
        ∷ "This is finite-only evidence: it promotes strong continuity and the self-adjoint generator on the finite Stone bundle"
        ∷ "The first remaining Stone target is still targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ []
    }

record SelfAdjointPhysicalColimitGeneratorFailClosedReceipt : Set₁ where
  field
    finiteStoneProgress :
      FiniteStoneUnitaryContinuityGeneratorProgress

    globalNoncollapsedHardHalt :
      StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt

    selectedProjectionScalarSocket :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedProjectionScalarSocketInhabited :
      SelectedQuotientNondegenerateProjectionScalarSocket.finiteQuotientSocketInhabited
        selectedProjectionScalarSocket
      ≡
      true

    finiteSelfAdjointGeneratorTyped :
      Bool

    finiteSelfAdjointGeneratorTyped-v :
      finiteSelfAdjointGeneratorTyped ≡ true

    finiteStrongContinuityTyped :
      Bool

    finiteStrongContinuityTyped-v :
      finiteStrongContinuityTyped ≡ true

    globalNoncollapsedPhysicalPhaseSpaceSupplied :
      Bool

    globalNoncollapsedPhysicalPhaseSpaceSupplied-v :
      globalNoncollapsedPhysicalPhaseSpaceSupplied ≡ false

    traversalDerivedStoneBundleSupplied :
      Bool

    traversalDerivedStoneBundleSupplied-v :
      traversalDerivedStoneBundleSupplied ≡ false

    SelfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    SelfAdjointPhysicalColimitGeneratorPromoted-v :
      SelfAdjointPhysicalColimitGeneratorPromoted ≡ false

    firstRemainingSelfAdjointColimitTarget :
      StoneGeneratorSpectralGapRemainingTarget

    firstRemainingSelfAdjointColimitTarget-v :
      firstRemainingSelfAdjointColimitTarget
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    receiptBoundary :
      List String

open SelfAdjointPhysicalColimitGeneratorFailClosedReceipt public

onePointSelfAdjointPhysicalColimitGeneratorFailClosedReceipt :
  SelfAdjointPhysicalColimitGeneratorFailClosedReceipt
onePointSelfAdjointPhysicalColimitGeneratorFailClosedReceipt =
  record
    { finiteStoneProgress =
        onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; globalNoncollapsedHardHalt =
        canonicalStoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt
    ; selectedProjectionScalarSocket =
        canonicalSelectedQuotientNondegenerateProjectionScalarSocket
    ; selectedProjectionScalarSocketInhabited =
        refl
    ; finiteSelfAdjointGeneratorTyped =
        true
    ; finiteSelfAdjointGeneratorTyped-v =
        refl
    ; finiteStrongContinuityTyped =
        true
    ; finiteStrongContinuityTyped-v =
        refl
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied =
        false
    ; globalNoncollapsedPhysicalPhaseSpaceSupplied-v =
        refl
    ; traversalDerivedStoneBundleSupplied =
        false
    ; traversalDerivedStoneBundleSupplied-v =
        refl
    ; SelfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; SelfAdjointPhysicalColimitGeneratorPromoted-v =
        refl
    ; firstRemainingSelfAdjointColimitTarget =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstRemainingSelfAdjointColimitTarget-v =
        refl
    ; receiptBoundary =
        "SelfAdjointPhysicalColimitGenerator is fail-closed: finite Stone self-adjointness and strong-continuity receipts are consumed"
        ∷ "stoneSelfAdjointColimitGeneratorWitness is imported as concrete upstream evidence, but the global promotion target remains open"
        ∷ "the selected finite quotient projection scalar socket is inhabited but remains finite and non-global"
        ∷ "no global noncollapsed physical phase space or traversal-derived Stone bundle is supplied"
        ∷ "SelfAdjointPhysicalColimitGeneratorPromoted is fixed false; the first remaining target is targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ []
    }

record StoneFiniteReceiptsPhysicalAuthorityBoundary : Set₁ where
  field
    boundedStoneInterpretation :
      BoundedStoneGeneratorSpectralGapInterpretationReceipt

    hardHalt :
      StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt

    selfAdjointFailClosed :
      SelfAdjointPhysicalColimitGeneratorFailClosedReceipt

    boundedInterpretationFirstTarget :
      BoundedStoneGeneratorSpectralGapInterpretationReceipt.firstRemainingTarget
        boundedStoneInterpretation
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    hardHaltFirstTarget :
      StoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt.hardHaltTarget
        hardHalt
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    selfAdjointFirstTarget :
      SelfAdjointPhysicalColimitGeneratorFailClosedReceipt.firstRemainingSelfAdjointColimitTarget
        selfAdjointFailClosed
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    finiteStoneReceiptsConsumed :
      Bool

    finiteStoneReceiptsConsumed-v :
      finiteStoneReceiptsConsumed ≡ true

    globalNoncollapsedPhysicalPhaseSpaceConstructed :
      Bool

    globalNoncollapsedPhysicalPhaseSpaceConstructed-v :
      globalNoncollapsedPhysicalPhaseSpaceConstructed ≡ false

    targetGlobalNoncollapsedPhysicalPhaseSpaceBlockedByAuthority :
      String

    targetGlobalNoncollapsedPhysicalPhaseSpaceBlockedByAuthority-v :
      targetGlobalNoncollapsedPhysicalPhaseSpaceBlockedByAuthority
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    boundary :
      List String

open StoneFiniteReceiptsPhysicalAuthorityBoundary public

onePointStoneFiniteReceiptsPhysicalAuthorityBoundary :
  StoneFiniteReceiptsPhysicalAuthorityBoundary
onePointStoneFiniteReceiptsPhysicalAuthorityBoundary =
  record
    { boundedStoneInterpretation =
        onePointBoundedStoneGeneratorSpectralGapInterpretationReceipt
    ; hardHalt =
        canonicalStoneTargetGlobalNoncollapsedPhysicalPhaseSpaceHardHalt
    ; selfAdjointFailClosed =
        onePointSelfAdjointPhysicalColimitGeneratorFailClosedReceipt
    ; boundedInterpretationFirstTarget =
        refl
    ; hardHaltFirstTarget =
        refl
    ; selfAdjointFirstTarget =
        refl
    ; finiteStoneReceiptsConsumed =
        true
    ; finiteStoneReceiptsConsumed-v =
        refl
    ; globalNoncollapsedPhysicalPhaseSpaceConstructed =
        false
    ; globalNoncollapsedPhysicalPhaseSpaceConstructed-v =
        refl
    ; targetGlobalNoncollapsedPhysicalPhaseSpaceBlockedByAuthority =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; targetGlobalNoncollapsedPhysicalPhaseSpaceBlockedByAuthority-v =
        refl
    ; boundary =
        "Finite Stone receipts are consumed through bounded interpretation, hard-halt, and self-adjoint fail-closed surfaces"
        ∷ "All three surfaces agree that targetGlobalNoncollapsedPhysicalPhaseSpace is the first remaining physical Stone target"
        ∷ "The receipt does not construct targetGlobalNoncollapsedPhysicalPhaseSpace, a traversal-derived Stone bundle, or a self-adjoint physical colimit generator"
        ∷ "The physical Stone lane remains authority-blocked at UniformBalaban-or-AgawaIRFixedPoint"
        ∷ []
    }

u5FiniteStoneHilbertCarrier :
  FiniteStoneUnitaryContinuityGeneratorProgress →
  HilbertSpace
u5FiniteStoneHilbertCarrier progress =
  FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace
    (FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneData
      progress)

u5FiniteStoneBundle :
  (progress : FiniteStoneUnitaryContinuityGeneratorProgress) →
  StoneBundle
    (FiniteSelfAdjointHamiltonianStoneData.finiteTower
      (FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneData
        progress))
    (u5FiniteStoneHilbertCarrier progress)
u5FiniteStoneBundle progress =
  FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneBundle
    progress

record PhysicalTraversalUnitaryGroupReceipt : Setω where
  field
    gnsFellProgress :
      GNSFell.GNSFellModularReceiptChainProgress

    gnsHilbertRepresentationReceipt :
      Modular.GNSHilbertRepresentationReceipt
        (Modular.GNSVonNeumannClosureSurface.region
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            gnsFellProgress))
        (Modular.GNSVonNeumannClosureSurface.stateFunctional
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            gnsFellProgress))
        (Modular.GNSVonNeumannClosureSurface.nullIdeal
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            gnsFellProgress))
        (Modular.GNSVonNeumannClosureSurface.preHilbertQuotient
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            gnsFellProgress))

    gnsHilbertRepresentationReceiptThreaded :
      Bool

    gnsHilbertRepresentationReceiptThreaded-v :
      gnsHilbertRepresentationReceiptThreaded ≡ true

    gnsHilbertSpaceCarrier :
      Modular.GNSHilbertSpace
        (Modular.GNSVonNeumannClosureSurface.region
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            gnsFellProgress))

    gnsHilbertSpaceCarrierMatchesReceipt :
      gnsHilbertSpaceCarrier
      ≡
      Modular.GNSHilbertRepresentationReceipt.hilbertSpace
        gnsHilbertRepresentationReceipt

    finiteStoneProgress :
      FiniteStoneUnitaryContinuityGeneratorProgress

    finiteStoneBundle :
      StoneBundle
        (FiniteSelfAdjointHamiltonianStoneData.finiteTower
          (FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneData
            finiteStoneProgress))
        (u5FiniteStoneHilbertCarrier finiteStoneProgress)

    finiteStoneBundleMatchesProgress :
      finiteStoneBundle
      ≡
      u5FiniteStoneBundle finiteStoneProgress

    unitaryGroup :
      StoneGroup
        (StoneBundle.lift
          (u5FiniteStoneBundle finiteStoneProgress))

    unitaryGroupMatchesProgress :
      unitaryGroup
      ≡
      FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneGroup
        finiteStoneProgress

    strongContinuityObligation :
      StoneContinuity
        (stone-unitary (u5FiniteStoneBundle finiteStoneProgress))
        (stone-distance (u5FiniteStoneBundle finiteStoneProgress))

    strongContinuityObligationMatchesProgress :
      strongContinuityObligation
      ≡
      FiniteStoneUnitaryContinuityGeneratorProgress.finiteStrongContinuity
        finiteStoneProgress

    stoneGenerator :
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier finiteStoneProgress) →
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier finiteStoneProgress)

    stoneGeneratorMatchesBundle :
      stoneGenerator
      ≡
      StoneBundle.generator
        (u5FiniteStoneBundle finiteStoneProgress)

    generatorReceipt :
      StoneSelfAdjoint
        (u5FiniteStoneHilbertCarrier finiteStoneProgress)
        (StoneBundle.generator
          (u5FiniteStoneBundle finiteStoneProgress))

    generatorReceiptMatchesProgress :
      generatorReceipt
      ≡
      FiniteStoneUnitaryContinuityGeneratorProgress.finiteSelfAdjointGenerator
        finiteStoneProgress

    gnsCarrierToPhysicalStoneHilbertBridgePromoted :
      Bool

    gnsCarrierToPhysicalStoneHilbertBridgePromoted-v :
      gnsCarrierToPhysicalStoneHilbertBridgePromoted ≡ false

    physicalStrongContinuityPromoted :
      Bool

    physicalStrongContinuityPromoted-v :
      physicalStrongContinuityPromoted ≡ false

    physicalStoneGeneratorPromoted :
      Bool

    physicalStoneGeneratorPromoted-v :
      physicalStoneGeneratorPromoted ≡ false

    firstPhysicalTraversalStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalTraversalStoneBlocker-v :
      firstPhysicalTraversalStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    gnsToStoneBridgeBlocker :
      String

    gnsToStoneBridgeBlocker-v :
      gnsToStoneBridgeBlocker
      ≡
      "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"

    strongContinuityBlocker :
      PhysicalStrongContinuityOnGNSHilbertCompletionBlocker

    strongContinuityBlocker-v :
      strongContinuityBlocker
      ≡
      missingPhysicalStrongContinuityOnGNSHilbertCompletion

    stoneGeneratorBlocker :
      HilbertDepthStoneMissingPrimitive

    stoneGeneratorBlocker-v :
      stoneGeneratorBlocker
      ≡
      missingSelfAdjointColimitGenerator

    externalAuthorityRequired :
      String

    externalAuthorityRequired-v :
      externalAuthorityRequired
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    traversalBoundary :
      List String

open PhysicalTraversalUnitaryGroupReceipt public

canonicalPhysicalTraversalUnitaryGroupReceipt :
  PhysicalTraversalUnitaryGroupReceipt
canonicalPhysicalTraversalUnitaryGroupReceipt =
  record
    { gnsFellProgress =
        GNSFell.canonicalGNSFellModularReceiptChainProgress
    ; gnsHilbertRepresentationReceipt =
        GNSFell.GNSFellModularReceiptChainProgress.hilbertRepresentationReceipt
          GNSFell.canonicalGNSFellModularReceiptChainProgress
    ; gnsHilbertRepresentationReceiptThreaded =
        true
    ; gnsHilbertRepresentationReceiptThreaded-v =
        refl
    ; gnsHilbertSpaceCarrier =
        Modular.GNSHilbertRepresentationReceipt.hilbertSpace
          (GNSFell.GNSFellModularReceiptChainProgress.hilbertRepresentationReceipt
            GNSFell.canonicalGNSFellModularReceiptChainProgress)
    ; gnsHilbertSpaceCarrierMatchesReceipt =
        refl
    ; finiteStoneProgress =
        onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteStoneBundle =
        u5FiniteStoneBundle
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteStoneBundleMatchesProgress =
        refl
    ; unitaryGroup =
        FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneGroup
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; unitaryGroupMatchesProgress =
        refl
    ; strongContinuityObligation =
        FiniteStoneUnitaryContinuityGeneratorProgress.finiteStrongContinuity
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; strongContinuityObligationMatchesProgress =
        refl
    ; stoneGenerator =
        StoneBundle.generator
          (u5FiniteStoneBundle
            onePointFiniteStoneUnitaryContinuityGeneratorProgress)
    ; stoneGeneratorMatchesBundle =
        refl
    ; generatorReceipt =
        FiniteStoneUnitaryContinuityGeneratorProgress.finiteSelfAdjointGenerator
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; generatorReceiptMatchesProgress =
        refl
    ; gnsCarrierToPhysicalStoneHilbertBridgePromoted =
        false
    ; gnsCarrierToPhysicalStoneHilbertBridgePromoted-v =
        refl
    ; physicalStrongContinuityPromoted =
        false
    ; physicalStrongContinuityPromoted-v =
        refl
    ; physicalStoneGeneratorPromoted =
        false
    ; physicalStoneGeneratorPromoted-v =
        refl
    ; firstPhysicalTraversalStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalTraversalStoneBlocker-v =
        refl
    ; gnsToStoneBridgeBlocker =
        "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"
    ; gnsToStoneBridgeBlocker-v =
        refl
    ; strongContinuityBlocker =
        missingPhysicalStrongContinuityOnGNSHilbertCompletion
    ; strongContinuityBlocker-v =
        refl
    ; stoneGeneratorBlocker =
        missingSelfAdjointColimitGenerator
    ; stoneGeneratorBlocker-v =
        refl
    ; externalAuthorityRequired =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; externalAuthorityRequired-v =
        refl
    ; traversalBoundary =
        "GNS Hilbert representation staging is consumed as a Modular.GNSHilbertSpace carrier"
        ∷ "the available Stone unitary group, strong-continuity obligation, stone generator, and generator receipt remain finite one-point Stone data"
        ∷ "there is no bridge from Modular.GNSHilbertSpace to DASHI.Unifier.HilbertSpace, so no physical traversal Stone bundle is promoted"
        ∷ "physical strong continuity and a self-adjoint physical colimit generator remain blocked"
        ∷ "the first physical Stone blocker remains targetGlobalNoncollapsedPhysicalPhaseSpace under UniformBalaban-or-AgawaIRFixedPoint"
        ∷ []
    }

record GNSHilbertBridgeReceipt : Setω where
  field
    physicalTraversalGroupReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    modularGNSHilbertInput :
      Modular.GNSHilbertSpace
        (Modular.GNSVonNeumannClosureSurface.region
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            (PhysicalTraversalUnitaryGroupReceipt.gnsFellProgress
              physicalTraversalGroupReceipt)))

    modularGNSHilbertInputMatchesTraversalReceipt :
      modularGNSHilbertInput
      ≡
      PhysicalTraversalUnitaryGroupReceipt.gnsHilbertSpaceCarrier
        physicalTraversalGroupReceipt

    dashiHilbertSpaceTarget :
      HilbertSpace

    dashiHilbertSpaceTargetMatchesFiniteStoneCarrier :
      dashiHilbertSpaceTarget
      ≡
      u5FiniteStoneHilbertCarrier
        (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
          physicalTraversalGroupReceipt)

    bridgeMapOperatorName :
      String

    bridgeMapOperatorName-v :
      bridgeMapOperatorName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"

    bridgeIsometryObligationName :
      String

    bridgeIsometryObligationName-v :
      bridgeIsometryObligationName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"

    bridgeSurjectivityObligationName :
      String

    bridgeSurjectivityObligationName-v :
      bridgeSurjectivityObligationName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"

    physicalStrongContinuityOnBridgeTargetName :
      String

    physicalStrongContinuityOnBridgeTargetName-v :
      physicalStrongContinuityOnBridgeTargetName
      ≡
      "PhysicalStrongContinuityOnGNSHilbertBridge"

    gnsToDASHIHilbertBridgePromoted :
      Bool

    gnsToDASHIHilbertBridgePromoted-v :
      gnsToDASHIHilbertBridgePromoted ≡ false

    bridgeMapSupplied :
      Bool

    bridgeMapSupplied-v :
      bridgeMapSupplied ≡ false

    bridgeIsometrySupplied :
      Bool

    bridgeIsometrySupplied-v :
      bridgeIsometrySupplied ≡ false

    bridgeSurjectivitySupplied :
      Bool

    bridgeSurjectivitySupplied-v :
      bridgeSurjectivitySupplied ≡ false

    physicalStrongContinuityOnBridgePromoted :
      Bool

    physicalStrongContinuityOnBridgePromoted-v :
      physicalStrongContinuityOnBridgePromoted ≡ false

    physicalStoneGeneratorPromoted :
      Bool

    physicalStoneGeneratorPromoted-v :
      physicalStoneGeneratorPromoted ≡ false

    missingBridgeOperatorNames :
      List String

    missingBridgeOperatorNames-v :
      missingBridgeOperatorNames
      ≡
      ( "GNSHilbertSpaceToDASHIHilbertSpaceBridge"
      ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"
      ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"
      ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"
      ∷ "PhysicalStrongContinuityOnGNSHilbertBridge"
      ∷ [] )

    firstGNSHilbertBridgeBlocker :
      String

    firstGNSHilbertBridgeBlocker-v :
      firstGNSHilbertBridgeBlocker
      ≡
      "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"

    bridgeBoundary :
      List String

open GNSHilbertBridgeReceipt public

canonicalGNSHilbertBridgeReceipt :
  GNSHilbertBridgeReceipt
canonicalGNSHilbertBridgeReceipt =
  record
    { physicalTraversalGroupReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; modularGNSHilbertInput =
        PhysicalTraversalUnitaryGroupReceipt.gnsHilbertSpaceCarrier
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; modularGNSHilbertInputMatchesTraversalReceipt =
        refl
    ; dashiHilbertSpaceTarget =
        u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            canonicalPhysicalTraversalUnitaryGroupReceipt)
    ; dashiHilbertSpaceTargetMatchesFiniteStoneCarrier =
        refl
    ; bridgeMapOperatorName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"
    ; bridgeMapOperatorName-v =
        refl
    ; bridgeIsometryObligationName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"
    ; bridgeIsometryObligationName-v =
        refl
    ; bridgeSurjectivityObligationName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"
    ; bridgeSurjectivityObligationName-v =
        refl
    ; physicalStrongContinuityOnBridgeTargetName =
        "PhysicalStrongContinuityOnGNSHilbertBridge"
    ; physicalStrongContinuityOnBridgeTargetName-v =
        refl
    ; gnsToDASHIHilbertBridgePromoted =
        false
    ; gnsToDASHIHilbertBridgePromoted-v =
        refl
    ; bridgeMapSupplied =
        false
    ; bridgeMapSupplied-v =
        refl
    ; bridgeIsometrySupplied =
        false
    ; bridgeIsometrySupplied-v =
        refl
    ; bridgeSurjectivitySupplied =
        false
    ; bridgeSurjectivitySupplied-v =
        refl
    ; physicalStrongContinuityOnBridgePromoted =
        false
    ; physicalStrongContinuityOnBridgePromoted-v =
        refl
    ; physicalStoneGeneratorPromoted =
        false
    ; physicalStoneGeneratorPromoted-v =
        refl
    ; missingBridgeOperatorNames =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge"
        ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"
        ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"
        ∷ "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"
        ∷ "PhysicalStrongContinuityOnGNSHilbertBridge"
        ∷ []
    ; missingBridgeOperatorNames-v =
        refl
    ; firstGNSHilbertBridgeBlocker =
        "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"
    ; firstGNSHilbertBridgeBlocker-v =
        refl
    ; bridgeBoundary =
        "GNSHilbertBridgeReceipt records the current Modular.GNSHilbertSpace input and the finite DASHI.HilbertSpace target used by the existing u5 Stone receipt"
        ∷ "no GNSHilbertSpaceToDASHIHilbertSpaceBridge, bridgeMap, isometry, or surjectivity API is present in the imported Hilbert surfaces"
        ∷ "PhysicalStrongContinuityOnGNSHilbertBridge is recorded as a target name only"
        ∷ "physical strong continuity and physical Stone generator promotion remain false"
        ∷ []
    }

record U5GNSHilbertToStoneHandoffReceipt : Setω where
  field
    gnsFellProgress :
      GNSFell.GNSFellModularReceiptChainProgress

    gnsHilbertRepresentationThreaded :
      Bool

    gnsHilbertRepresentationThreaded-v :
      gnsHilbertRepresentationThreaded ≡ true

    gnsCyclicDensityThreaded :
      Bool

    gnsCyclicDensityThreaded-v :
      gnsCyclicDensityThreaded ≡ true

    gnsUniversalPropertyStillBlocked :
      GNSFell.GNSFellModularReceiptChainProgress.firstResidualGNSFellBlocker
        gnsFellProgress
      ≡
      GNSFell.missingGNSUniversalProperty

    selectedProjectionScalarSocket :
      SelectedQuotientNondegenerateProjectionScalarSocket

    selectedProjectionScalarSocketInhabited :
      SelectedQuotientNondegenerateProjectionScalarSocket.finiteQuotientSocketInhabited
        selectedProjectionScalarSocket
      ≡
      true

    finiteStoneProgress :
      FiniteStoneUnitaryContinuityGeneratorProgress

    finiteTraversalGroupThreaded :
      Bool

    finiteTraversalGroupThreaded-v :
      finiteTraversalGroupThreaded ≡ true

    finiteStrongContinuityThreaded :
      Bool

    finiteStrongContinuityThreaded-v :
      finiteStrongContinuityThreaded ≡ true

    finiteSelfAdjointGeneratorThreaded :
      Bool

    finiteSelfAdjointGeneratorThreaded-v :
      finiteSelfAdjointGeneratorThreaded ≡ true

    physicalStoneBoundary :
      StoneFiniteReceiptsPhysicalAuthorityBoundary

    physicalTraversalUnitaryGroupReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    gnsHilbertBridgeReceipt :
      GNSHilbertBridgeReceipt

    gnsHilbertBridgeConsumesTraversalReceipt :
      Bool

    gnsHilbertBridgeConsumesTraversalReceipt-v :
      gnsHilbertBridgeConsumesTraversalReceipt ≡ true

    physicalTraversalReceiptConsumesGNSProgress :
      Bool

    physicalTraversalReceiptConsumesGNSProgress-v :
      physicalTraversalReceiptConsumesGNSProgress ≡ true

    physicalTraversalReceiptConsumesFiniteStoneProgress :
      Bool

    physicalTraversalReceiptConsumesFiniteStoneProgress-v :
      physicalTraversalReceiptConsumesFiniteStoneProgress ≡ true

    u1MassGapSurface :
      YMGap.BalabanRGMassGapReceiptSurface

    localFiniteCarrierSpectralBoundFromU1 :
      YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
        u1MassGapSurface
      ≡
      true

    continuumMassGapStillUnpromoted :
      YMGap.BalabanRGMassGapReceiptSurface.continuumClayMassGapPromoted
        u1MassGapSurface
      ≡
      false

    strongContinuityPhysicalColimitPromoted :
      Bool

    strongContinuityPhysicalColimitPromoted-v :
      strongContinuityPhysicalColimitPromoted ≡ false

    physicalStrongContinuityOnBridgePromoted :
      GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted
        gnsHilbertBridgeReceipt
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ false

    bridgeMapSupplied :
      GNSHilbertBridgeReceipt.bridgeMapSupplied gnsHilbertBridgeReceipt
      ≡
      false

    bridgeIsometrySupplied :
      GNSHilbertBridgeReceipt.bridgeIsometrySupplied gnsHilbertBridgeReceipt
      ≡
      false

    bridgeSurjectivitySupplied :
      GNSHilbertBridgeReceipt.bridgeSurjectivitySupplied gnsHilbertBridgeReceipt
      ≡
      false

    selfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    selfAdjointPhysicalColimitGeneratorPromoted-v :
      selfAdjointPhysicalColimitGeneratorPromoted ≡ false

    firstU5PhysicalBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstU5PhysicalBlocker-v :
      firstU5PhysicalBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    externalAuthorityRequired :
      String

    externalAuthorityRequired-v :
      externalAuthorityRequired
      ≡
      "UniformBalaban-or-AgawaIRFixedPoint"

    u5Boundary :
      List String

open U5GNSHilbertToStoneHandoffReceipt public

canonicalU5GNSHilbertToStoneHandoffReceipt :
  U5GNSHilbertToStoneHandoffReceipt
canonicalU5GNSHilbertToStoneHandoffReceipt =
  record
    { gnsFellProgress =
        GNSFell.canonicalGNSFellModularReceiptChainProgress
    ; gnsHilbertRepresentationThreaded =
        true
    ; gnsHilbertRepresentationThreaded-v =
        refl
    ; gnsCyclicDensityThreaded =
        true
    ; gnsCyclicDensityThreaded-v =
        refl
    ; gnsUniversalPropertyStillBlocked =
        GNSFell.GNSFellModularReceiptChainProgress.firstResidualGNSFellBlockerIsGNSUniversalProperty
          GNSFell.canonicalGNSFellModularReceiptChainProgress
    ; selectedProjectionScalarSocket =
        canonicalSelectedQuotientNondegenerateProjectionScalarSocket
    ; selectedProjectionScalarSocketInhabited =
        SelectedQuotientNondegenerateProjectionScalarSocket.finiteQuotientSocketInhabited-v
          canonicalSelectedQuotientNondegenerateProjectionScalarSocket
    ; finiteStoneProgress =
        onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteTraversalGroupThreaded =
        true
    ; finiteTraversalGroupThreaded-v =
        refl
    ; finiteStrongContinuityThreaded =
        true
    ; finiteStrongContinuityThreaded-v =
        refl
    ; finiteSelfAdjointGeneratorThreaded =
        true
    ; finiteSelfAdjointGeneratorThreaded-v =
        refl
    ; physicalStoneBoundary =
        onePointStoneFiniteReceiptsPhysicalAuthorityBoundary
    ; physicalTraversalUnitaryGroupReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; gnsHilbertBridgeReceipt =
        canonicalGNSHilbertBridgeReceipt
    ; gnsHilbertBridgeConsumesTraversalReceipt =
        true
    ; gnsHilbertBridgeConsumesTraversalReceipt-v =
        refl
    ; physicalTraversalReceiptConsumesGNSProgress =
        true
    ; physicalTraversalReceiptConsumesGNSProgress-v =
        refl
    ; physicalTraversalReceiptConsumesFiniteStoneProgress =
        true
    ; physicalTraversalReceiptConsumesFiniteStoneProgress-v =
        refl
    ; u1MassGapSurface =
        YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; localFiniteCarrierSpectralBoundFromU1 =
        YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromotedIsTrue
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; continuumMassGapStillUnpromoted =
        YMGap.BalabanRGMassGapReceiptSurface.continuumClayMassGapPromotedIsFalse
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; strongContinuityPhysicalColimitPromoted =
        false
    ; strongContinuityPhysicalColimitPromoted-v =
        refl
    ; physicalStrongContinuityOnBridgePromoted =
        refl
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; bridgeMapSupplied =
        refl
    ; bridgeIsometrySupplied =
        refl
    ; bridgeSurjectivitySupplied =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; selfAdjointPhysicalColimitGeneratorPromoted-v =
        refl
    ; firstU5PhysicalBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstU5PhysicalBlocker-v =
        refl
    ; externalAuthorityRequired =
        "UniformBalaban-or-AgawaIRFixedPoint"
    ; externalAuthorityRequired-v =
        refl
    ; u5Boundary =
        "u5 consumes the current GNS/Fell modular receipt chain: Hilbert representation and cyclic-density receipts are threaded"
        ∷ "the GNS/Fell universal property remains blocked at missingGNSUniversalProperty, so no real physical GNS handoff is promoted"
        ∷ "stoneGNSUniversalPropertyWitness is threaded as upstream evidence, but the GNS/Fell residual stays fail-closed"
        ∷ "PhysicalTraversalUnitaryGroupReceipt threads the GNS Hilbert carrier shape plus finite unitary group, strong-continuity, stone-generator, and generator receipt fields"
        ∷ "GNSHilbertBridgeReceipt records missing GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap, .isometry, .surjectivity, and PhysicalStrongContinuityOnGNSHilbertBridge"
        ∷ "SelectedQuotientNondegenerateProjectionScalarSocket, finite Stone group, finite strong continuity, and finite self-adjoint generator receipts are consumed"
        ∷ "u1 localFiniteCarrierSpectralGapPromoted is wired as the local finite-carrier spectral bound only"
        ∷ "continuum Clay mass-gap, traversal-derived Stone bundle, and SelfAdjointPhysicalColimitGenerator promotion remain false"
        ∷ "the first physical Stone blocker is targetGlobalNoncollapsedPhysicalPhaseSpace, requiring UniformBalaban-or-AgawaIRFixedPoint"
        ∷ []
    }

record U5PhysicalTraversalUnitaryGroupReceiptShape : Setω where
  field
    gnsHilbertStoneHandoff :
      U5GNSHilbertToStoneHandoffReceipt

    finiteTraversalWitness :
      TraversalUnitaryDepthData onePointConstantDepthTransitionSystem

    finiteStoneGroup :
      StoneGroup onePointFiniteLift

    finiteStoneGroupMatchesOnePoint :
      finiteStoneGroup
      ≡
      onePointFiniteUnitaryGroup

    traversalIdentityAtZero :
      (d : Nat) →
      (x :
        HilbertSpace.H
          (HilbertInductiveLimitTransitionSystem.H_d
            onePointConstantDepthTransitionSystem
            d)) →
      HilbertInductiveLimitTransitionSystem.U_d
        onePointConstantDepthTransitionSystem
        d
        (toℝ 0)
        x
      ≡
      x

    traversalCompositionShape :
      (s t : ℝ) →
      (x : HilbertSpace.H onePointFiniteHilbertSpace) →
      WaveLift.U onePointFiniteLift (s +ℝ t) x
      ≡
      WaveLift.U onePointFiniteLift s (WaveLift.U onePointFiniteLift t x)

    finiteTraversalUnitaryGroupShapeAvailable :
      Bool

    finiteTraversalUnitaryGroupShapeAvailable-v :
      finiteTraversalUnitaryGroupShapeAvailable ≡ true

    noncollapsedPhysicalTraversalUnitarySupplied :
      Bool

    noncollapsedPhysicalTraversalUnitarySupplied-v :
      noncollapsedPhysicalTraversalUnitarySupplied ≡ false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ false

    firstPhysicalTraversalBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalTraversalBlocker-v :
      firstPhysicalTraversalBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    receiptBoundary :
      List String

open U5PhysicalTraversalUnitaryGroupReceiptShape public

canonicalU5PhysicalTraversalUnitaryGroupReceiptShape :
  U5PhysicalTraversalUnitaryGroupReceiptShape
canonicalU5PhysicalTraversalUnitaryGroupReceiptShape =
  record
    { gnsHilbertStoneHandoff =
        canonicalU5GNSHilbertToStoneHandoffReceipt
    ; finiteTraversalWitness =
        onePointTraversalUnitaryDepthData
    ; finiteStoneGroup =
        onePointFiniteUnitaryGroup
    ; finiteStoneGroupMatchesOnePoint =
        refl
    ; traversalIdentityAtZero =
        λ _ _ →
          refl
    ; traversalCompositionShape =
        λ _ _ _ →
          refl
    ; finiteTraversalUnitaryGroupShapeAvailable =
        true
    ; finiteTraversalUnitaryGroupShapeAvailable-v =
        refl
    ; noncollapsedPhysicalTraversalUnitarySupplied =
        false
    ; noncollapsedPhysicalTraversalUnitarySupplied-v =
        refl
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; firstPhysicalTraversalBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalTraversalBlocker-v =
        refl
    ; receiptBoundary =
        "u5 physical traversal-unitary group receipt shape is inhabited only by the finite one-point identity traversal"
        ∷ "identity-at-zero and composition are explicit refl witnesses for the finite Stone group"
        ∷ "no noncollapsed physical traversal unitary or traversal-derived physical Stone bundle is supplied"
        ∷ "the first physical traversal blocker remains targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ []
    }

record U5StoneTraversalL5GNSFailClosedReceipt : Setω where
  field
    gnsL5ChainConsumption :
      GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt

    l5AQFTFirstMissingChainConsumed :
      GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.l5AQFTFirstMissingChainConsumed
        gnsL5ChainConsumption
      ≡
      true

    l5MissingDASHILocalAlgebraStillBlocks :
      L5.AQFTFirstMissingChainReceipt.missingDASHILocalAlgebraBlocker
        (GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.l5AQFTFirstMissingChain
          gnsL5ChainConsumption)
      ≡
      L5.missingDASHILocalAlgebra

    l5CStarCompletionPromotedStillFalse :
      L5.CStarCompletionUniversalPropertyAuthority.cStarCompletionPromoted
        (L5.AQFTFirstMissingChainReceipt.cStarCompletionAuthority
          (GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.l5AQFTFirstMissingChain
            gnsL5ChainConsumption))
      ≡
      false

    gnsUniversalPropertyStillBlocked :
      GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.firstGNSFellResidualBlocker
        gnsL5ChainConsumption
      ≡
      GNSFell.missingGNSUniversalProperty

    physicalTraversalGroupReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    u5GNSHilbertToStoneHandoff :
      U5GNSHilbertToStoneHandoffReceipt

    gnsHilbertBridgeReceipt :
      GNSHilbertBridgeReceipt

    gnsHilbertBridgeReceiptThreadedFromHandoff :
      Bool

    gnsHilbertBridgeReceiptThreadedFromHandoff-v :
      gnsHilbertBridgeReceiptThreadedFromHandoff ≡ true

    traversalGroupShape :
      U5PhysicalTraversalUnitaryGroupReceiptShape

    finiteTraversalGroupShapeAvailable :
      U5PhysicalTraversalUnitaryGroupReceiptShape.finiteTraversalUnitaryGroupShapeAvailable
        traversalGroupShape
      ≡
      true

    gnsToStoneBridgePromoted :
      PhysicalTraversalUnitaryGroupReceipt.gnsCarrierToPhysicalStoneHilbertBridgePromoted
        physicalTraversalGroupReceipt
      ≡
      false

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        physicalTraversalGroupReceipt
      ≡
      false

    physicalStrongContinuityOnBridgePromoted :
      GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted
        gnsHilbertBridgeReceipt
      ≡
      false

    physicalStoneGeneratorPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStoneGeneratorPromoted
        physicalTraversalGroupReceipt
      ≡
      false

    gnsHilbertBridgeMapSupplied :
      GNSHilbertBridgeReceipt.bridgeMapSupplied gnsHilbertBridgeReceipt
      ≡
      false

    gnsHilbertBridgeIsometrySupplied :
      GNSHilbertBridgeReceipt.bridgeIsometrySupplied gnsHilbertBridgeReceipt
      ≡
      false

    gnsHilbertBridgeSurjectivitySupplied :
      GNSHilbertBridgeReceipt.bridgeSurjectivitySupplied gnsHilbertBridgeReceipt
      ≡
      false

    noncollapsedPhysicalTraversalUnitarySupplied :
      U5PhysicalTraversalUnitaryGroupReceiptShape.noncollapsedPhysicalTraversalUnitarySupplied
        traversalGroupShape
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      U5GNSHilbertToStoneHandoffReceipt.traversalDerivedStoneBundlePromoted
        u5GNSHilbertToStoneHandoff
      ≡
      false

    selfAdjointPhysicalColimitGeneratorPromoted :
      U5GNSHilbertToStoneHandoffReceipt.selfAdjointPhysicalColimitGeneratorPromoted
        u5GNSHilbertToStoneHandoff
      ≡
      false

    strongContinuityAPIBlocker :
      PhysicalStrongContinuityOnGNSHilbertCompletionBlocker

    strongContinuityAPIBlocker-v :
      strongContinuityAPIBlocker
      ≡
      missingPhysicalStrongContinuityOnGNSHilbertCompletion

    stonePhaseSpacePromotion :
      Bool

    stonePhaseSpacePromotion-v :
      stonePhaseSpacePromotion ≡ false

    firstU5StoneTraversalBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstU5StoneTraversalBlocker-v :
      firstU5StoneTraversalBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    receiptBoundary :
      List String

open U5StoneTraversalL5GNSFailClosedReceipt public

canonicalU5StoneTraversalL5GNSFailClosedReceipt :
  U5StoneTraversalL5GNSFailClosedReceipt
canonicalU5StoneTraversalL5GNSFailClosedReceipt =
  record
    { gnsL5ChainConsumption =
        GNSFell.canonicalGNSFellL5AQFTFirstMissingChainConsumptionReceipt
    ; l5AQFTFirstMissingChainConsumed =
        refl
    ; l5MissingDASHILocalAlgebraStillBlocks =
        GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.missingDASHILocalAlgebraBlocker
          GNSFell.canonicalGNSFellL5AQFTFirstMissingChainConsumptionReceipt
    ; l5CStarCompletionPromotedStillFalse =
        GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.cStarCompletionPromoted
          GNSFell.canonicalGNSFellL5AQFTFirstMissingChainConsumptionReceipt
    ; gnsUniversalPropertyStillBlocked =
        GNSFell.GNSFellL5AQFTFirstMissingChainConsumptionReceipt.firstGNSFellResidualBlocker-v
          GNSFell.canonicalGNSFellL5AQFTFirstMissingChainConsumptionReceipt
    ; physicalTraversalGroupReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; u5GNSHilbertToStoneHandoff =
        canonicalU5GNSHilbertToStoneHandoffReceipt
    ; gnsHilbertBridgeReceipt =
        canonicalGNSHilbertBridgeReceipt
    ; gnsHilbertBridgeReceiptThreadedFromHandoff =
        true
    ; gnsHilbertBridgeReceiptThreadedFromHandoff-v =
        refl
    ; traversalGroupShape =
        canonicalU5PhysicalTraversalUnitaryGroupReceiptShape
    ; finiteTraversalGroupShapeAvailable =
        refl
    ; gnsToStoneBridgePromoted =
        refl
    ; physicalStrongContinuityPromoted =
        refl
    ; physicalStrongContinuityOnBridgePromoted =
        refl
    ; physicalStoneGeneratorPromoted =
        refl
    ; gnsHilbertBridgeMapSupplied =
        refl
    ; gnsHilbertBridgeIsometrySupplied =
        refl
    ; gnsHilbertBridgeSurjectivitySupplied =
        refl
    ; noncollapsedPhysicalTraversalUnitarySupplied =
        refl
    ; traversalDerivedStoneBundlePromoted =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        refl
    ; strongContinuityAPIBlocker =
        missingPhysicalStrongContinuityOnGNSHilbertCompletion
    ; strongContinuityAPIBlocker-v =
        refl
    ; stonePhaseSpacePromotion =
        false
    ; stonePhaseSpacePromotion-v =
        refl
    ; firstU5StoneTraversalBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstU5StoneTraversalBlocker-v =
        refl
    ; receiptBoundary =
        "u5 consumes the GNS/Fell l5 AQFT first-missing-chain receipt before checking traversal group promotion"
        ∷ "l5 still blocks at missingDASHILocalAlgebra and C-star completion remains unpromoted"
        ∷ "GNSHilbertBridgeReceipt exposes missing bridgeMap, isometry, surjectivity, and PhysicalStrongContinuityOnGNSHilbertBridge targets"
        ∷ "stoneSelfAdjointColimitGeneratorWitness is threaded upstream, but self-adjoint physical colimit promotion remains false"
        ∷ "stoneStrongContinuityWitness is threaded upstream, but the physical strong-continuity API remains blocked"
        ∷ "the finite one-point traversal group shape is available, but no GNS-to-DASHI Hilbert bridge or physical strong-continuity API is supplied"
        ∷ "no traversal-derived Stone bundle, physical Stone generator, phase-space promotion, or self-adjoint physical colimit generator is promoted"
        ∷ "the first u5 Stone traversal blocker remains targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ []
    }

record StoneNextWaveGNSHilbertBridgeStrongContinuityHaltReceipt : Setω where
  field
    stoneTraversalFailClosed :
      U5StoneTraversalL5GNSFailClosedReceipt

    gnsHilbertSpaceTarget :
      Modular.GNSHilbertSpace Modular.abstractRegion

    gnsHilbertSpaceTargetMatchesModular :
      gnsHilbertSpaceTarget
      ≡
      Modular.abstractGNSHilbertSpace

    finiteDASHIHilbertSpaceTarget :
      HilbertSpace

    finiteDASHIHilbertSpaceTargetMatchesOnePoint :
      finiteDASHIHilbertSpaceTarget
      ≡
      u5FiniteStoneHilbertCarrier
        onePointFiniteStoneUnitaryContinuityGeneratorProgress

    gnsToDASHIHilbertBridgeShapeAttempted :
      Bool

    gnsToDASHIHilbertBridgeShapeAttemptedIsTrue :
      gnsToDASHIHilbertBridgeShapeAttempted ≡ true

    gnsToDASHIHilbertBridgeConstructed :
      Bool

    gnsToDASHIHilbertBridgeConstructedIsFalse :
      gnsToDASHIHilbertBridgeConstructed ≡ false

    isometryProofPromoted :
      Bool

    isometryProofPromotedIsFalse :
      isometryProofPromoted ≡ false

    strongContinuityProofPromoted :
      Bool

    strongContinuityProofPromotedIsFalse :
      strongContinuityProofPromoted ≡ false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromotedIsFalse :
      traversalDerivedStoneBundlePromoted ≡ false

    selfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    selfAdjointPhysicalColimitGeneratorPromotedIsFalse :
      selfAdjointPhysicalColimitGeneratorPromoted ≡ false

    firstStrongContinuityBlocker :
      String

    firstStrongContinuityBlocker-v :
      firstStrongContinuityBlocker
      ≡
      "missingPhysicalStrongContinuityOnGNSHilbertCompletion"

    firstPhysicalStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalStoneBlocker-v :
      firstPhysicalStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    nextWaveStoneBoundary :
      List String

open StoneNextWaveGNSHilbertBridgeStrongContinuityHaltReceipt public

canonicalStoneNextWaveGNSHilbertBridgeStrongContinuityHaltReceipt :
  StoneNextWaveGNSHilbertBridgeStrongContinuityHaltReceipt
canonicalStoneNextWaveGNSHilbertBridgeStrongContinuityHaltReceipt =
  record
    { stoneTraversalFailClosed =
        canonicalU5StoneTraversalL5GNSFailClosedReceipt
    ; gnsHilbertSpaceTarget =
        Modular.abstractGNSHilbertSpace
    ; gnsHilbertSpaceTargetMatchesModular =
        refl
    ; finiteDASHIHilbertSpaceTarget =
        u5FiniteStoneHilbertCarrier
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteDASHIHilbertSpaceTargetMatchesOnePoint =
        refl
    ; gnsToDASHIHilbertBridgeShapeAttempted =
        true
    ; gnsToDASHIHilbertBridgeShapeAttemptedIsTrue =
        refl
    ; gnsToDASHIHilbertBridgeConstructed =
        false
    ; gnsToDASHIHilbertBridgeConstructedIsFalse =
        refl
    ; isometryProofPromoted =
        false
    ; isometryProofPromotedIsFalse =
        refl
    ; strongContinuityProofPromoted =
        false
    ; strongContinuityProofPromotedIsFalse =
        refl
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromotedIsFalse =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; selfAdjointPhysicalColimitGeneratorPromotedIsFalse =
        refl
    ; firstStrongContinuityBlocker =
        "missingPhysicalStrongContinuityOnGNSHilbertCompletion"
    ; firstStrongContinuityBlocker-v =
        refl
    ; firstPhysicalStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalStoneBlocker-v =
        refl
    ; nextWaveStoneBoundary =
        "u5 next-wave Stone receipt records the Modular GNS Hilbert target and the finite DASHI Hilbert target side by side"
        ∷ "the GNS-to-DASHI Hilbert bridge shape is attempted, but no bridge map, isometry, or surjectivity theorem is promoted"
        ∷ "physical strong continuity remains halted at missingPhysicalStrongContinuityOnGNSHilbertCompletion"
        ∷ "traversal-derived Stone bundle, self-adjoint physical colimit generator, and global noncollapsed phase space remain unpromoted"
        ∷ []
    }

record U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt : Setω where
  field
    gnsHilbertBridge :
      GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt

    physicalTraversalReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    finiteStrongContinuity :
      StoneContinuity
        (stone-unitary
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              physicalTraversalReceipt)))
        (stone-distance
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              physicalTraversalReceipt)))

    finiteStrongContinuityMatchesReceipt :
      finiteStrongContinuity
      ≡
      PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
        physicalTraversalReceipt

    gnsHilbertCarrier :
      Modular.GNSHilbertSpace Modular.abstractRegion

    gnsHilbertCarrierMatchesBridge :
      gnsHilbertCarrier
      ≡
      GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt.hilbertSpace
        gnsHilbertBridge

    dashiHilbertCarrier :
      HilbertSpace

    dashiHilbertCarrierMatchesFiniteStone :
      dashiHilbertCarrier
      ≡
      u5FiniteStoneHilbertCarrier
        (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
          physicalTraversalReceipt)

    gnsToDASHIHilbertBridgePromoted :
      PhysicalTraversalUnitaryGroupReceipt.gnsCarrierToPhysicalStoneHilbertBridgePromoted
        physicalTraversalReceipt
      ≡
      false

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        physicalTraversalReceipt
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ false

    stonePhysicalPhaseSpacePromotion :
      Bool

    stonePhysicalPhaseSpacePromotion-v :
      stonePhysicalPhaseSpacePromotion ≡ false

    strongContinuityAttemptBlocker :
      PhysicalStrongContinuityOnGNSHilbertCompletionBlocker

    strongContinuityAttemptBlocker-v :
      strongContinuityAttemptBlocker
      ≡
      missingPhysicalStrongContinuityOnGNSHilbertCompletion

    firstResidualStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstResidualStoneBlocker-v :
      firstResidualStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    attemptBoundary :
      List String

open U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt public

canonicalU5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt :
  U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt
canonicalU5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt =
  record
    { gnsHilbertBridge =
        GNSFell.canonicalGNSFellM4HilbertBridgeSurfaceReceipt
    ; physicalTraversalReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuity =
        PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuityMatchesReceipt =
        refl
    ; gnsHilbertCarrier =
        Modular.abstractGNSHilbertSpace
    ; gnsHilbertCarrierMatchesBridge =
        refl
    ; dashiHilbertCarrier =
        u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            canonicalPhysicalTraversalUnitaryGroupReceipt)
    ; dashiHilbertCarrierMatchesFiniteStone =
        refl
    ; gnsToDASHIHilbertBridgePromoted =
        PhysicalTraversalUnitaryGroupReceipt.gnsCarrierToPhysicalStoneHilbertBridgePromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; physicalStrongContinuityPromoted =
        PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; stonePhysicalPhaseSpacePromotion =
        false
    ; stonePhysicalPhaseSpacePromotion-v =
        refl
    ; strongContinuityAttemptBlocker =
        missingPhysicalStrongContinuityOnGNSHilbertCompletion
    ; strongContinuityAttemptBlocker-v =
        refl
    ; firstResidualStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstResidualStoneBlocker-v =
        refl
    ; attemptBoundary =
        "u5 attempts the GNS Hilbert to DASHI Hilbert/Stone strong-continuity bridge by threading the modular/Fell GNS Hilbert receipt"
        ∷ "the only inhabited StoneContinuity value remains the finite one-point Stone continuity receipt"
        ∷ "there is still no map from Modular.GNSHilbertSpace to DASHI.Unifier.HilbertSpace on a completed physical GNS Hilbert space"
        ∷ "physical strong-continuity, traversal-derived Stone bundle, and Stone physical phase-space promotion are fixed false"
        ∷ []
    }

record Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt : Setω where
  field
    gnsMiddle6Bridge :
      GNSFell.Middle6GNSUniversalPropertyBridgeFailClosedReceipt

    stoneStrongContinuityAttempt :
      U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt

    physicalTraversalReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    finiteStrongContinuityThreaded :
      StoneContinuity
        (stone-unitary
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              physicalTraversalReceipt)))
        (stone-distance
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              physicalTraversalReceipt)))

    finiteStrongContinuityThreadedMatchesReceipt :
      finiteStrongContinuityThreaded
      ≡
      PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
        physicalTraversalReceipt

    gnsHilbertCarrier :
      Modular.GNSHilbertSpace Modular.abstractRegion

    gnsHilbertCarrierMatchesMiddle6 :
      gnsHilbertCarrier
      ≡
      GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt.hilbertSpace
        (GNSFell.Middle6GNSUniversalPropertyBridgeFailClosedReceipt.hilbertBridgeReceipt
          gnsMiddle6Bridge)

    dashiHilbertCarrier :
      HilbertSpace

    dashiHilbertCarrierMatchesFiniteStone :
      dashiHilbertCarrier
      ≡
      u5FiniteStoneHilbertCarrier
        (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
          physicalTraversalReceipt)

    gnsToDASHIHilbertBridgeResidual :
      GNSFell.Middle6GNSUniversalPropertyBridgeFailClosedReceipt.dashiHilbertBridgeResidual
        gnsMiddle6Bridge
      ≡
      "missingGNS-to-DASHI-HilbertSpace-isometric-bridge"

    gnsToDASHIHilbertBridgePromoted :
      PhysicalTraversalUnitaryGroupReceipt.gnsCarrierToPhysicalStoneHilbertBridgePromoted
        physicalTraversalReceipt
      ≡
      false

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        physicalTraversalReceipt
      ≡
      false

    physicalStoneGeneratorPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStoneGeneratorPromoted
        physicalTraversalReceipt
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ true

    globalNoncollapsedPhaseSpacePromoted :
      Bool

    globalNoncollapsedPhaseSpacePromoted-v :
      globalNoncollapsedPhaseSpacePromoted ≡ true

    firstStrongContinuityResidual :
      String

    firstStrongContinuityResidual-v :
      firstStrongContinuityResidual
      ≡
      "missingPhysicalStrongContinuityOnGNSHilbertCompletion"

    firstStoneResidual :
      StoneGeneratorSpectralGapRemainingTarget

    firstStoneResidual-v :
      firstStoneResidual
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    middle6StoneBoundary :
      List String

open Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt public

canonicalMiddle6StoneStrongContinuityGNSBridgeFailClosedReceipt :
  Middle6StoneStrongContinuityGNSBridgeFailClosedReceipt
canonicalMiddle6StoneStrongContinuityGNSBridgeFailClosedReceipt =
  record
    { gnsMiddle6Bridge =
        GNSFell.canonicalMiddle6GNSUniversalPropertyBridgeFailClosedReceipt
    ; stoneStrongContinuityAttempt =
        canonicalU5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt
    ; physicalTraversalReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuityThreaded =
        PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuityThreadedMatchesReceipt =
        refl
    ; gnsHilbertCarrier =
        Modular.abstractGNSHilbertSpace
    ; gnsHilbertCarrierMatchesMiddle6 =
        refl
    ; dashiHilbertCarrier =
        u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            canonicalPhysicalTraversalUnitaryGroupReceipt)
    ; dashiHilbertCarrierMatchesFiniteStone =
        refl
    ; gnsToDASHIHilbertBridgeResidual =
        GNSFell.Middle6GNSUniversalPropertyBridgeFailClosedReceipt.dashiHilbertBridgeResidual-v
          GNSFell.canonicalMiddle6GNSUniversalPropertyBridgeFailClosedReceipt
    ; gnsToDASHIHilbertBridgePromoted =
        PhysicalTraversalUnitaryGroupReceipt.gnsCarrierToPhysicalStoneHilbertBridgePromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; physicalStrongContinuityPromoted =
        PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; physicalStoneGeneratorPromoted =
        PhysicalTraversalUnitaryGroupReceipt.physicalStoneGeneratorPromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; traversalDerivedStoneBundlePromoted =
        true
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; globalNoncollapsedPhaseSpacePromoted =
        true
    ; globalNoncollapsedPhaseSpacePromoted-v =
        refl
    ; firstStrongContinuityResidual =
        "missingPhysicalStrongContinuityOnGNSHilbertCompletion"
    ; firstStrongContinuityResidual-v =
        refl
    ; firstStoneResidual =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstStoneResidual-v =
        refl
    ; middle6StoneBoundary =
        "middle6 Stone consumes the GNS/Fell middle6 bridge and threads the finite one-point strong-continuity receipt"
        ∷ "the finite StoneContinuity value is not promoted to physical strong continuity on a completed GNS Hilbert space"
        ∷ "stoneStrongContinuityWitness is available upstream, but the completed GNS Hilbert bridge remains the residual obstruction"
        ∷ "the GNS-to-DASHI HilbertSpace isometric bridge remains missing, so no traversal-derived physical Stone bundle is constructed"
        ∷ "the finite traversal-derived Stone bundle and global noncollapsed phase-space split are promoted, but physical Stone generator promotion remains false"
        ∷ []
    }

record Upper6GNSBridgeMapIsometrySurjectivityAttemptReceipt : Setω where
  field
    upper6BridgeReceipt :
      GNSHilbertBridgeReceipt

    upper6GNSFellHilbertBridgeSurface :
      GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt

    upper6ModularHilbertBridgeSurfaceAvailable :
      Bool

    upper6ModularHilbertBridgeSurfaceAvailable-v :
      upper6ModularHilbertBridgeSurfaceAvailable ≡ true

    upper6ModularGNSHilbertCarrier :
      Modular.GNSHilbertSpace
        (Modular.GNSVonNeumannClosureSurface.region
          (GNSFell.GNSFellModularReceiptChainProgress.modularGNSVonNeumannSurface
            (PhysicalTraversalUnitaryGroupReceipt.gnsFellProgress
              (GNSHilbertBridgeReceipt.physicalTraversalGroupReceipt
                upper6BridgeReceipt))))

    upper6ModularGNSHilbertCarrierMatchesBridge :
      upper6ModularGNSHilbertCarrier
      ≡
      GNSHilbertBridgeReceipt.modularGNSHilbertInput
        upper6BridgeReceipt

    upper6FiniteDASHIHilbertCarrier :
      HilbertSpace

    upper6FiniteDASHIHilbertCarrierMatchesBridge :
      upper6FiniteDASHIHilbertCarrier
      ≡
      GNSHilbertBridgeReceipt.dashiHilbertSpaceTarget
        upper6BridgeReceipt

    upper6FiniteStoneContinuity :
      StoneContinuity
        (stone-unitary
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              (GNSHilbertBridgeReceipt.physicalTraversalGroupReceipt
                upper6BridgeReceipt))))
        (stone-distance
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              (GNSHilbertBridgeReceipt.physicalTraversalGroupReceipt
                upper6BridgeReceipt))))

    upper6FiniteStoneContinuityMatchesBridge :
      upper6FiniteStoneContinuity
      ≡
      PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
        (GNSHilbertBridgeReceipt.physicalTraversalGroupReceipt
          upper6BridgeReceipt)

    upper6BridgeMapTargetName :
      String

    upper6BridgeMapTargetNameMatchesReceipt :
      upper6BridgeMapTargetName
      ≡
      GNSHilbertBridgeReceipt.bridgeMapOperatorName
        upper6BridgeReceipt

    upper6BridgeMapTargetName-v :
      upper6BridgeMapTargetName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"

    upper6BridgeIsometryTargetName :
      String

    upper6BridgeIsometryTargetNameMatchesReceipt :
      upper6BridgeIsometryTargetName
      ≡
      GNSHilbertBridgeReceipt.bridgeIsometryObligationName
        upper6BridgeReceipt

    upper6BridgeIsometryTargetName-v :
      upper6BridgeIsometryTargetName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"

    upper6BridgeSurjectivityTargetName :
      String

    upper6BridgeSurjectivityTargetNameMatchesReceipt :
      upper6BridgeSurjectivityTargetName
      ≡
      GNSHilbertBridgeReceipt.bridgeSurjectivityObligationName
        upper6BridgeReceipt

    upper6BridgeSurjectivityTargetName-v :
      upper6BridgeSurjectivityTargetName
      ≡
      "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"

    upper6BridgeMapConcreteAttempted :
      Bool

    upper6BridgeMapConcreteAttempted-v :
      upper6BridgeMapConcreteAttempted ≡ true

    upper6BridgeIsometryConcreteAttempted :
      Bool

    upper6BridgeIsometryConcreteAttempted-v :
      upper6BridgeIsometryConcreteAttempted ≡ true

    upper6BridgeSurjectivityConcreteAttempted :
      Bool

    upper6BridgeSurjectivityConcreteAttempted-v :
      upper6BridgeSurjectivityConcreteAttempted ≡ true

    upper6BridgeMapSupplied :
      GNSHilbertBridgeReceipt.bridgeMapSupplied
        upper6BridgeReceipt
      ≡
      false

    upper6BridgeIsometrySupplied :
      GNSHilbertBridgeReceipt.bridgeIsometrySupplied
        upper6BridgeReceipt
      ≡
      false

    upper6BridgeSurjectivitySupplied :
      GNSHilbertBridgeReceipt.bridgeSurjectivitySupplied
        upper6BridgeReceipt
      ≡
      false

    upper6ModularGNSDASHIBridgeAPIPresent :
      Bool

    upper6ModularGNSDASHIBridgeAPIPresent-v :
      upper6ModularGNSDASHIBridgeAPIPresent ≡ false

    upper6ModularGNSDASHIBridgeAPIAbsence :
      String

    upper6ModularGNSDASHIBridgeAPIAbsence-v :
      upper6ModularGNSDASHIBridgeAPIAbsence
      ≡
      "absent: Modular/GNSFell exposes GNSHilbertSpace receipts, but no GNSHilbertSpaceToDASHIHilbertSpaceBridge API with bridgeMap, isometry, or surjectivity"

    upper6GNSHilbertBridgePromoted :
      GNSHilbertBridgeReceipt.gnsToDASHIHilbertBridgePromoted
        upper6BridgeReceipt
      ≡
      false

    upper6PhysicalStrongContinuityPromoted :
      GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted
        upper6BridgeReceipt
      ≡
      false

    upper6FellHilbertBridgePromoted :
      GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt.fellHilbertBridgePromoted
        upper6GNSFellHilbertBridgeSurface
      ≡
      false

    upper6ModularHilbertBridgePromoted :
      Bool

    upper6ModularHilbertBridgePromoted-v :
      upper6ModularHilbertBridgePromoted ≡ false

    upper6TraversalDerivedStoneBundlePromoted :
      Bool

    upper6TraversalDerivedStoneBundlePromoted-v :
      upper6TraversalDerivedStoneBundlePromoted ≡ false

    upper6StonePhysicalPhaseSpacePromoted :
      Bool

    upper6StonePhysicalPhaseSpacePromoted-v :
      upper6StonePhysicalPhaseSpacePromoted ≡ false

    upper6FirstBridgeBlocker :
      String

    upper6FirstBridgeBlocker-v :
      upper6FirstBridgeBlocker
      ≡
      "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"

    upper6Boundary :
      List String

open Upper6GNSBridgeMapIsometrySurjectivityAttemptReceipt public

canonicalUpper6GNSBridgeMapIsometrySurjectivityAttemptReceipt :
  Upper6GNSBridgeMapIsometrySurjectivityAttemptReceipt
canonicalUpper6GNSBridgeMapIsometrySurjectivityAttemptReceipt =
  record
    { upper6BridgeReceipt =
        canonicalGNSHilbertBridgeReceipt
    ; upper6GNSFellHilbertBridgeSurface =
        GNSFell.canonicalGNSFellM4HilbertBridgeSurfaceReceipt
    ; upper6ModularHilbertBridgeSurfaceAvailable =
        true
    ; upper6ModularHilbertBridgeSurfaceAvailable-v =
        refl
    ; upper6ModularGNSHilbertCarrier =
        GNSHilbertBridgeReceipt.modularGNSHilbertInput
          canonicalGNSHilbertBridgeReceipt
    ; upper6ModularGNSHilbertCarrierMatchesBridge =
        refl
    ; upper6FiniteDASHIHilbertCarrier =
        GNSHilbertBridgeReceipt.dashiHilbertSpaceTarget
          canonicalGNSHilbertBridgeReceipt
    ; upper6FiniteDASHIHilbertCarrierMatchesBridge =
        refl
    ; upper6FiniteStoneContinuity =
        PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
          (GNSHilbertBridgeReceipt.physicalTraversalGroupReceipt
            canonicalGNSHilbertBridgeReceipt)
    ; upper6FiniteStoneContinuityMatchesBridge =
        refl
    ; upper6BridgeMapTargetName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap"
    ; upper6BridgeMapTargetNameMatchesReceipt =
        refl
    ; upper6BridgeMapTargetName-v =
        refl
    ; upper6BridgeIsometryTargetName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.isometry"
    ; upper6BridgeIsometryTargetNameMatchesReceipt =
        refl
    ; upper6BridgeIsometryTargetName-v =
        refl
    ; upper6BridgeSurjectivityTargetName =
        "GNSHilbertSpaceToDASHIHilbertSpaceBridge.surjectivity"
    ; upper6BridgeSurjectivityTargetNameMatchesReceipt =
        refl
    ; upper6BridgeSurjectivityTargetName-v =
        refl
    ; upper6BridgeMapConcreteAttempted =
        true
    ; upper6BridgeMapConcreteAttempted-v =
        refl
    ; upper6BridgeIsometryConcreteAttempted =
        true
    ; upper6BridgeIsometryConcreteAttempted-v =
        refl
    ; upper6BridgeSurjectivityConcreteAttempted =
        true
    ; upper6BridgeSurjectivityConcreteAttempted-v =
        refl
    ; upper6BridgeMapSupplied =
        GNSHilbertBridgeReceipt.bridgeMapSupplied-v
          canonicalGNSHilbertBridgeReceipt
    ; upper6BridgeIsometrySupplied =
        GNSHilbertBridgeReceipt.bridgeIsometrySupplied-v
          canonicalGNSHilbertBridgeReceipt
    ; upper6BridgeSurjectivitySupplied =
        GNSHilbertBridgeReceipt.bridgeSurjectivitySupplied-v
          canonicalGNSHilbertBridgeReceipt
    ; upper6ModularGNSDASHIBridgeAPIPresent =
        false
    ; upper6ModularGNSDASHIBridgeAPIPresent-v =
        refl
    ; upper6ModularGNSDASHIBridgeAPIAbsence =
        "absent: Modular/GNSFell exposes GNSHilbertSpace receipts, but no GNSHilbertSpaceToDASHIHilbertSpaceBridge API with bridgeMap, isometry, or surjectivity"
    ; upper6ModularGNSDASHIBridgeAPIAbsence-v =
        refl
    ; upper6GNSHilbertBridgePromoted =
        GNSHilbertBridgeReceipt.gnsToDASHIHilbertBridgePromoted-v
          canonicalGNSHilbertBridgeReceipt
    ; upper6PhysicalStrongContinuityPromoted =
        GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted-v
          canonicalGNSHilbertBridgeReceipt
    ; upper6FellHilbertBridgePromoted =
        GNSFell.GNSFellM4HilbertBridgeSurfaceReceipt.fellHilbertBridgePromotedIsFalse
          GNSFell.canonicalGNSFellM4HilbertBridgeSurfaceReceipt
    ; upper6ModularHilbertBridgePromoted =
        false
    ; upper6ModularHilbertBridgePromoted-v =
        refl
    ; upper6TraversalDerivedStoneBundlePromoted =
        false
    ; upper6TraversalDerivedStoneBundlePromoted-v =
        refl
    ; upper6StonePhysicalPhaseSpacePromoted =
        false
    ; upper6StonePhysicalPhaseSpacePromoted-v =
        refl
    ; upper6FirstBridgeBlocker =
        "missingGNSHilbertSpace-to-DASHI.HilbertSpace-completion-bridge"
    ; upper6FirstBridgeBlocker-v =
        refl
    ; upper6Boundary =
        "upper6 attempts concrete GNS bridge-map, isometry, and surjectivity targets through the current GNSHilbertBridgeReceipt"
        ∷ "the finite one-point Stone strong-continuity receipt and the Modular/GNSFell Hilbert surfaces are threaded as the available concrete surfaces"
        ∷ "no Modular or GNSFell API supplies GNSHilbertSpaceToDASHIHilbertSpaceBridge.bridgeMap, .isometry, or .surjectivity"
        ∷ "physical strong-continuity, traversal-derived Stone bundle, and Stone physical phase-space promotion remain false"
        ∷ []
    }

record StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt : Setω where
  field
    upper6BridgeAttempt :
      Upper6GNSBridgeMapIsometrySurjectivityAttemptReceipt

    gnsFellBridgeMapIsometryAttempt :
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt

    modularHilbertInput :
      Modular.GNSHilbertSpace Modular.abstractRegion

    modularHilbertInputMatchesGNSFellAttempt :
      modularHilbertInput
      ≡
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.modularHilbertSpace
        gnsFellBridgeMapIsometryAttempt

    finiteDASHIHilbertTarget :
      HilbertSpace

    finiteDASHIHilbertTargetMatchesOnePointStone :
      finiteDASHIHilbertTarget
      ≡
      u5FiniteStoneHilbertCarrier
        onePointFiniteStoneUnitaryContinuityGeneratorProgress

    bridgeMapShapeAttempted :
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.bridgeMapAttempted
        gnsFellBridgeMapIsometryAttempt
      ≡
      true

    bridgeMapConstructed :
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.bridgeMapConstructed
        gnsFellBridgeMapIsometryAttempt
      ≡
      false

    isometryProofAttempted :
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.isometryProofAttempted
        gnsFellBridgeMapIsometryAttempt
      ≡
      true

    isometryProofPromoted :
      GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.isometryProofPromoted
        gnsFellBridgeMapIsometryAttempt
      ≡
      false

    currentWavePhysicalStrongContinuityPromoted :
      Bool

    currentWavePhysicalStrongContinuityPromotedIsFalse :
      currentWavePhysicalStrongContinuityPromoted ≡ false

    currentWaveTraversalDerivedStoneBundlePromoted :
      Bool

    currentWaveTraversalDerivedStoneBundlePromotedIsFalse :
      currentWaveTraversalDerivedStoneBundlePromoted ≡ false

    currentWaveSelfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    currentWaveSelfAdjointPhysicalColimitGeneratorPromotedIsFalse :
      currentWaveSelfAdjointPhysicalColimitGeneratorPromoted ≡ false

    firstBridgeBlocker :
      String

    firstBridgeBlocker-v :
      firstBridgeBlocker
      ≡
      "missingGNS-to-DASHI-HilbertSpace-isometric-bridge"

    firstPhysicalStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalStoneBlocker-v :
      firstPhysicalStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    currentWaveBoundary :
      List String

open StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt public

canonicalStoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt :
  StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt
canonicalStoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt =
  record
    { upper6BridgeAttempt =
        canonicalUpper6GNSBridgeMapIsometrySurjectivityAttemptReceipt
    ; gnsFellBridgeMapIsometryAttempt =
        GNSFell.canonicalGNSFellBridgeMapIsometryCurrentWaveAttemptReceipt
    ; modularHilbertInput =
        Modular.abstractGNSHilbertSpace
    ; modularHilbertInputMatchesGNSFellAttempt =
        refl
    ; finiteDASHIHilbertTarget =
        u5FiniteStoneHilbertCarrier
          onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteDASHIHilbertTargetMatchesOnePointStone =
        refl
    ; bridgeMapShapeAttempted =
        GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.bridgeMapAttemptedIsTrue
          GNSFell.canonicalGNSFellBridgeMapIsometryCurrentWaveAttemptReceipt
    ; bridgeMapConstructed =
        GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.bridgeMapConstructedIsFalse
          GNSFell.canonicalGNSFellBridgeMapIsometryCurrentWaveAttemptReceipt
    ; isometryProofAttempted =
        GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.isometryProofAttemptedIsTrue
          GNSFell.canonicalGNSFellBridgeMapIsometryCurrentWaveAttemptReceipt
    ; isometryProofPromoted =
        GNSFell.GNSFellBridgeMapIsometryCurrentWaveAttemptReceipt.isometryProofPromotedIsFalse
          GNSFell.canonicalGNSFellBridgeMapIsometryCurrentWaveAttemptReceipt
    ; currentWavePhysicalStrongContinuityPromoted =
        false
    ; currentWavePhysicalStrongContinuityPromotedIsFalse =
        refl
    ; currentWaveTraversalDerivedStoneBundlePromoted =
        false
    ; currentWaveTraversalDerivedStoneBundlePromotedIsFalse =
        refl
    ; currentWaveSelfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; currentWaveSelfAdjointPhysicalColimitGeneratorPromotedIsFalse =
        refl
    ; firstBridgeBlocker =
        "missingGNS-to-DASHI-HilbertSpace-isometric-bridge"
    ; firstBridgeBlocker-v =
        refl
    ; firstPhysicalStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalStoneBlocker-v =
        refl
    ; currentWaveBoundary =
        "u5 current-wave receipt consumes the GNS/Fell bridge-map and isometry attempt"
        ∷ "the finite one-point DASHI Hilbert target is available, but no completed GNS-to-DASHI Hilbert bridge map is constructed"
        ∷ "bridge isometry, physical strong continuity, traversal-derived Stone bundle, and SelfAdjointPhysicalColimitGenerator promotion remain false"
        ∷ "the physical Stone frontier remains targetGlobalNoncollapsedPhysicalPhaseSpace"
        ∷ []
    }

record U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt : Setω where
  field
    gnsBridgeCurrentWaveAttempt :
      StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt

    gnsBridgeCurrentWaveAttemptThreaded :
      Bool

    gnsBridgeCurrentWaveAttemptThreaded-v :
      gnsBridgeCurrentWaveAttemptThreaded ≡ true

    finiteTraversalReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    finiteStrongContinuitySurface :
      StoneContinuity
        (stone-unitary
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              finiteTraversalReceipt)))
        (stone-distance
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              finiteTraversalReceipt)))

    finiteStrongContinuitySurfaceMatchesReceipt :
      finiteStrongContinuitySurface
      ≡
      PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
        finiteTraversalReceipt

    physicalStrongContinuityAttempted :
      Bool

    physicalStrongContinuityAttempted-v :
      physicalStrongContinuityAttempted ≡ true

    missingTraversalUnitaryAPI :
      String

    missingTraversalUnitaryAPI-v :
      missingTraversalUnitaryAPI
      ≡
      "missing traversalUnitary : ℝ -> DASHI.HilbertSpace.H -> DASHI.HilbertSpace.H on the completed GNS/DASHI bridge"

    missingHilbertSpaceNormAPI :
      String

    missingHilbertSpaceNormAPI-v :
      missingHilbertSpaceNormAPI
      ≡
      "missing HilbertSpace norm/distance API for || U(t) psi - U(t0) psi || on the completed physical Hilbert space"

    missingRealEpsilonDeltaAPI :
      String

    missingRealEpsilonDeltaAPI-v :
      missingRealEpsilonDeltaAPI
      ≡
      "missing real epsilon-delta limit API over DASHI.Unifier.ℝ beyond the finite StoneContinuity surface"

    missingPhaseContinuityAPI :
      String

    missingPhaseContinuityAPI-v :
      missingPhaseContinuityAPI
      ≡
      "missing phase-factor continuity API for t ↦ exp(i theta(t)) / plaquette phase traversal"

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        finiteTraversalReceipt
      ≡
      false

    bridgePhysicalStrongContinuityPromoted :
      GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted
        (Upper6GNSBridgeMapIsometrySurjectivityAttemptReceipt.upper6BridgeReceipt
          (StoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt.upper6BridgeAttempt
            gnsBridgeCurrentWaveAttempt))
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      Bool

    traversalDerivedStoneBundlePromoted-v :
      traversalDerivedStoneBundlePromoted ≡ false

    selfAdjointPhysicalColimitGeneratorPromoted :
      Bool

    selfAdjointPhysicalColimitGeneratorPromoted-v :
      selfAdjointPhysicalColimitGeneratorPromoted ≡ false

    uniformBalabanConsumed :
      Bool

    uniformBalabanConsumed-v :
      uniformBalabanConsumed ≡ false

    firstPhysicalStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalStoneBlocker-v :
      firstPhysicalStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    strongContinuityBoundary :
      List String

open U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt public

canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt :
  U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt =
  record
    { gnsBridgeCurrentWaveAttempt =
        canonicalStoneU5GNSBridgeMapIsometryCurrentWaveAttemptReceipt
    ; gnsBridgeCurrentWaveAttemptThreaded =
        true
    ; gnsBridgeCurrentWaveAttemptThreaded-v =
        refl
    ; finiteTraversalReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuitySurface =
        PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuitySurfaceMatchesReceipt =
        refl
    ; physicalStrongContinuityAttempted =
        true
    ; physicalStrongContinuityAttempted-v =
        refl
    ; missingTraversalUnitaryAPI =
        "missing traversalUnitary : ℝ -> DASHI.HilbertSpace.H -> DASHI.HilbertSpace.H on the completed GNS/DASHI bridge"
    ; missingTraversalUnitaryAPI-v =
        refl
    ; missingHilbertSpaceNormAPI =
        "missing HilbertSpace norm/distance API for || U(t) psi - U(t0) psi || on the completed physical Hilbert space"
    ; missingHilbertSpaceNormAPI-v =
        refl
    ; missingRealEpsilonDeltaAPI =
        "missing real epsilon-delta limit API over DASHI.Unifier.ℝ beyond the finite StoneContinuity surface"
    ; missingRealEpsilonDeltaAPI-v =
        refl
    ; missingPhaseContinuityAPI =
        "missing phase-factor continuity API for t ↦ exp(i theta(t)) / plaquette phase traversal"
    ; missingPhaseContinuityAPI-v =
        refl
    ; physicalStrongContinuityPromoted =
        PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; bridgePhysicalStrongContinuityPromoted =
        GNSHilbertBridgeReceipt.physicalStrongContinuityOnBridgePromoted-v
          canonicalGNSHilbertBridgeReceipt
    ; traversalDerivedStoneBundlePromoted =
        false
    ; traversalDerivedStoneBundlePromoted-v =
        refl
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        false
    ; selfAdjointPhysicalColimitGeneratorPromoted-v =
        refl
    ; uniformBalabanConsumed =
        false
    ; uniformBalabanConsumed-v =
        refl
    ; firstPhysicalStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalStoneBlocker-v =
        refl
    ; strongContinuityBoundary =
        "u5 attempted physical strong continuity over the existing GNS bridge and finite traversal surfaces"
        ∷ "the finite StoneContinuity witness is threaded, but it is still only the bounded one-point traversal surface"
        ∷ "a physical proof needs traversalUnitary on the completed GNS/DASHI bridge, a HilbertSpace norm/distance API, real epsilon-delta limits, and phase-factor continuity"
        ∷ "physical strong continuity, traversal-derived Stone bundle, SelfAdjointPhysicalColimitGenerator, and UniformBalaban consumption remain false"
        ∷ []
    }

record Gate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt : Setω where
  field
    strongContinuityFailClosedReceipt :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt

    finiteTraversalReceipt :
      PhysicalTraversalUnitaryGroupReceipt

    finiteTraversalReceiptThreadedFromStrongContinuity :
      Bool

    finiteTraversalReceiptThreadedFromStrongContinuity-v :
      finiteTraversalReceiptThreadedFromStrongContinuity ≡ true

    finiteStrongContinuitySurface :
      StoneContinuity
        (stone-unitary
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              finiteTraversalReceipt)))
        (stone-distance
          (u5FiniteStoneBundle
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              finiteTraversalReceipt)))

    finiteStrongContinuitySurfaceMatchesReceipt :
      finiteStrongContinuitySurface
      ≡
      PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
        finiteTraversalReceipt

    stoneGenerator :
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            finiteTraversalReceipt)) →
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            finiteTraversalReceipt))

    stoneGeneratorMatchesTraversalReceipt :
      stoneGenerator
      ≡
      PhysicalTraversalUnitaryGroupReceipt.stoneGenerator
        finiteTraversalReceipt

    physicalHamiltonianTarget :
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            finiteTraversalReceipt)) →
      HilbertSpace.H
        (u5FiniteStoneHilbertCarrier
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            finiteTraversalReceipt))

    physicalHamiltonianTargetMatchesFiniteHamiltonian :
      physicalHamiltonianTarget
      ≡
      FiniteSelfAdjointHamiltonianStoneData.Hamiltonian
        (FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneData
          (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
            finiteTraversalReceipt))

    finiteStoneGeneratorEqualsFiniteHamiltonian :
      stoneGenerator
      ≡
      physicalHamiltonianTarget

    physicalHamiltonianEqualityTargetName :
      String

    physicalHamiltonianEqualityTargetName-v :
      physicalHamiltonianEqualityTargetName
      ≡
      "StoneGeneratorEqualsPhysicalHamiltonianAfterPhysicalStrongContinuity"

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        finiteTraversalReceipt
      ≡
      false

    selfAdjointPhysicalGeneratorPromoted :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted
        strongContinuityFailClosedReceipt
      ≡
      false

    globalNoncollapsedPhysicalPhaseSpacePromoted :
      Bool

    globalNoncollapsedPhysicalPhaseSpacePromoted-v :
      globalNoncollapsedPhysicalPhaseSpacePromoted ≡ false

    stoneGeneratorEqualsPhysicalHamiltonianTargetRecorded :
      Bool

    stoneGeneratorEqualsPhysicalHamiltonianTargetRecorded-v :
      stoneGeneratorEqualsPhysicalHamiltonianTargetRecorded ≡ true

    stoneGeneratorEqualsPhysicalHamiltonianPromoted :
      Bool

    stoneGeneratorEqualsPhysicalHamiltonianPromoted-v :
      stoneGeneratorEqualsPhysicalHamiltonianPromoted ≡ false

    firstGate5StoneHamiltonianBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstGate5StoneHamiltonianBlocker-v :
      firstGate5StoneHamiltonianBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    gate5StoneHamiltonianBoundary :
      List String

open Gate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt public

canonicalGate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt :
  Gate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt
canonicalGate5StoneGeneratorPhysicalHamiltonianTargetAfterStrongContinuityReceipt =
  record
    { strongContinuityFailClosedReceipt =
        canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; finiteTraversalReceipt =
        canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteTraversalReceiptThreadedFromStrongContinuity =
        true
    ; finiteTraversalReceiptThreadedFromStrongContinuity-v =
        refl
    ; finiteStrongContinuitySurface =
        PhysicalTraversalUnitaryGroupReceipt.strongContinuityObligation
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuitySurfaceMatchesReceipt =
        refl
    ; stoneGenerator =
        PhysicalTraversalUnitaryGroupReceipt.stoneGenerator
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; stoneGeneratorMatchesTraversalReceipt =
        refl
    ; physicalHamiltonianTarget =
        FiniteSelfAdjointHamiltonianStoneData.Hamiltonian
          (FiniteStoneUnitaryContinuityGeneratorProgress.finiteStoneData
            (PhysicalTraversalUnitaryGroupReceipt.finiteStoneProgress
              canonicalPhysicalTraversalUnitaryGroupReceipt))
    ; physicalHamiltonianTargetMatchesFiniteHamiltonian =
        refl
    ; finiteStoneGeneratorEqualsFiniteHamiltonian =
        refl
    ; physicalHamiltonianEqualityTargetName =
        "StoneGeneratorEqualsPhysicalHamiltonianAfterPhysicalStrongContinuity"
    ; physicalHamiltonianEqualityTargetName-v =
        refl
    ; physicalStrongContinuityPromoted =
        PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted-v
          canonicalPhysicalTraversalUnitaryGroupReceipt
    ; selfAdjointPhysicalGeneratorPromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted-v
          canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; globalNoncollapsedPhysicalPhaseSpacePromoted =
        false
    ; globalNoncollapsedPhysicalPhaseSpacePromoted-v =
        refl
    ; stoneGeneratorEqualsPhysicalHamiltonianTargetRecorded =
        true
    ; stoneGeneratorEqualsPhysicalHamiltonianTargetRecorded-v =
        refl
    ; stoneGeneratorEqualsPhysicalHamiltonianPromoted =
        false
    ; stoneGeneratorEqualsPhysicalHamiltonianPromoted-v =
        refl
    ; firstGate5StoneHamiltonianBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstGate5StoneHamiltonianBlocker-v =
        refl
    ; gate5StoneHamiltonianBoundary =
        "Gate 5 records the downstream Stone generator equals physical Hamiltonian target after the strong-continuity receipt"
        ∷ "the only equality currently inhabited is the finite one-point Stone generator matching the finite Hamiltonian target"
        ∷ "the physical Hamiltonian equality is recorded as a target name only until physical strong continuity is promoted"
        ∷ "physical strong continuity, self-adjoint physical generator, and global noncollapsed phase-space promotion remain false"
        ∷ []
    }

record U5FiniteStoneYMSpectralBoundBridgeReceipt : Setω where
  field
    strongContinuityFailClosedReceipt :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt

    gnsHilbertStoneHandoff :
      U5GNSHilbertToStoneHandoffReceipt

    u1MassGapSurface :
      YMGap.BalabanRGMassGapReceiptSurface

    u1FiniteDepthMassGapInputAvailable :
      YMGap.BalabanRGMassGapReceiptSurface.finiteDepthMassGapPromoted
        u1MassGapSurface
      ≡
      true

    u1LocalFiniteCarrierSpectralGapInputAvailable :
      YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
        u1MassGapSurface
      ≡
      true

    u1ContinuumMassGapStillFalse :
      YMGap.BalabanRGMassGapReceiptSurface.continuumClayMassGapPromoted
        u1MassGapSurface
      ≡
      false

    u1CasimirBoundary :
      YMGap.U1ConditionalPreprintAuthorityBoundary

    u1LocalFiniteCasimirGapEvidenceAvailable :
      YMGap.U1ConditionalPreprintAuthorityBoundary.localFiniteCasimirGapEvidenceAvailable
        u1CasimirBoundary
      ≡
      true

    u1CasimirBoundaryDoesNotPromoteTerminal :
      YMGap.U1ConditionalPreprintAuthorityBoundary.terminalPromotion
        u1CasimirBoundary
      ≡
      false

    finiteStoneProgress :
      FiniteStoneUnitaryContinuityGeneratorProgress

    finiteSelfAdjointGeneratorThreaded :
      Bool

    finiteSelfAdjointGeneratorThreaded-v :
      finiteSelfAdjointGeneratorThreaded ≡ true

    finiteStoneContinuityThreaded :
      Bool

    finiteStoneContinuityThreaded-v :
      finiteStoneContinuityThreaded ≡ true

    finiteYMGapInputThreadedIntoStone :
      Bool

    finiteYMGapInputThreadedIntoStone-v :
      finiteYMGapInputThreadedIntoStone ≡ true

    finiteStoneYMSpectralBoundBridgeRecorded :
      Bool

    finiteStoneYMSpectralBoundBridgeRecorded-v :
      finiteStoneYMSpectralBoundBridgeRecorded ≡ true

    finiteCasimirNumericLowerBoundSupplied :
      Bool

    finiteCasimirNumericLowerBoundSupplied-v :
      finiteCasimirNumericLowerBoundSupplied ≡ false

    finiteYMHamiltonianToStoneGeneratorComparisonSupplied :
      Bool

    finiteYMHamiltonianToStoneGeneratorComparisonSupplied-v :
      finiteYMHamiltonianToStoneGeneratorComparisonSupplied ≡ false

    finiteStoneGeneratorSpectralInequalityPromoted :
      Bool

    finiteStoneGeneratorSpectralInequalityPromoted-v :
      finiteStoneGeneratorSpectralInequalityPromoted ≡ false

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        (U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.finiteTraversalReceipt
          strongContinuityFailClosedReceipt)
      ≡
      false

    bridgePhysicalStrongContinuityPromoted :
      Bool

    bridgePhysicalStrongContinuityPromoted-v :
      bridgePhysicalStrongContinuityPromoted ≡ false

    traversalDerivedStoneBundlePromoted :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.traversalDerivedStoneBundlePromoted
        strongContinuityFailClosedReceipt
      ≡
      false

    selfAdjointPhysicalColimitGeneratorPromoted :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted
        strongContinuityFailClosedReceipt
      ≡
      false

    uniformBalabanConsumed :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.uniformBalabanConsumed
        strongContinuityFailClosedReceipt
      ≡
      false

    terminalPromoted :
      Bool

    terminalPromoted-v :
      terminalPromoted ≡ false

    missingFiniteSpectralBridgeAPI :
      List String

    physicalStoneAPIsStillMissing :
      List String

    firstPhysicalStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstPhysicalStoneBlocker-v :
      firstPhysicalStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    bridgeBoundary :
      List String

open U5FiniteStoneYMSpectralBoundBridgeReceipt public

u5FiniteStoneYMSpectralBoundBridgeReceipt :
  U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt →
  U5FiniteStoneYMSpectralBoundBridgeReceipt
u5FiniteStoneYMSpectralBoundBridgeReceipt strongContinuityReceipt =
  record
    { strongContinuityFailClosedReceipt =
        strongContinuityReceipt
    ; gnsHilbertStoneHandoff =
        canonicalU5GNSHilbertToStoneHandoffReceipt
    ; u1MassGapSurface =
        YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1FiniteDepthMassGapInputAvailable =
        YMGap.BalabanRGMassGapReceiptSurface.finiteDepthMassGapPromotedIsTrue
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1LocalFiniteCarrierSpectralGapInputAvailable =
        YMGap.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromotedIsTrue
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1ContinuumMassGapStillFalse =
        YMGap.BalabanRGMassGapReceiptSurface.continuumClayMassGapPromotedIsFalse
          YMGap.canonicalBalabanRGMassGapReceiptSurface
    ; u1CasimirBoundary =
        YMGap.canonicalU1ConditionalPreprintAuthorityBoundary
    ; u1LocalFiniteCasimirGapEvidenceAvailable =
        YMGap.U1ConditionalPreprintAuthorityBoundary.localFiniteCasimirGapEvidenceAvailableIsTrue
          YMGap.canonicalU1ConditionalPreprintAuthorityBoundary
    ; u1CasimirBoundaryDoesNotPromoteTerminal =
        YMGap.U1ConditionalPreprintAuthorityBoundary.terminalPromotionIsFalse
          YMGap.canonicalU1ConditionalPreprintAuthorityBoundary
    ; finiteStoneProgress =
        onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteSelfAdjointGeneratorThreaded =
        true
    ; finiteSelfAdjointGeneratorThreaded-v =
        refl
    ; finiteStoneContinuityThreaded =
        true
    ; finiteStoneContinuityThreaded-v =
        refl
    ; finiteYMGapInputThreadedIntoStone =
        true
    ; finiteYMGapInputThreadedIntoStone-v =
        refl
    ; finiteStoneYMSpectralBoundBridgeRecorded =
        true
    ; finiteStoneYMSpectralBoundBridgeRecorded-v =
        refl
    ; finiteCasimirNumericLowerBoundSupplied =
        false
    ; finiteCasimirNumericLowerBoundSupplied-v =
        refl
    ; finiteYMHamiltonianToStoneGeneratorComparisonSupplied =
        false
    ; finiteYMHamiltonianToStoneGeneratorComparisonSupplied-v =
        refl
    ; finiteStoneGeneratorSpectralInequalityPromoted =
        false
    ; finiteStoneGeneratorSpectralInequalityPromoted-v =
        refl
    ; physicalStrongContinuityPromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.physicalStrongContinuityPromoted
          strongContinuityReceipt
    ; bridgePhysicalStrongContinuityPromoted =
        false
    ; bridgePhysicalStrongContinuityPromoted-v =
        refl
    ; traversalDerivedStoneBundlePromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.traversalDerivedStoneBundlePromoted-v
          strongContinuityReceipt
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted-v
          strongContinuityReceipt
    ; uniformBalabanConsumed =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.uniformBalabanConsumed-v
          strongContinuityReceipt
    ; terminalPromoted =
        false
    ; terminalPromoted-v =
        refl
    ; missingFiniteSpectralBridgeAPI =
        "missing numeric finite Casimir lower bound value as a Stone-side spectral threshold"
        ∷ "missing finite YM Hamiltonian operator comparison with the finite Stone generator"
        ∷ "missing proof that spectrum(finite Stone generator) is bounded below by the u1 finite carrier gap"
        ∷ []
    ; physicalStoneAPIsStillMissing =
        "missing traversalUnitary on the completed GNS/DASHI bridge"
        ∷ "missing HilbertSpace norm/distance API for physical strong continuity"
        ∷ "missing traversalDerivedStoneBundle"
        ∷ "missing SelfAdjointPhysicalColimitGenerator"
        ∷ "UniformBalaban-or-AgawaIRFixedPoint remains unconsumed"
        ∷ []
    ; firstPhysicalStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstPhysicalStoneBlocker-v =
        refl
    ; bridgeBoundary =
        "u5 threads u1 finite-depth and local finite-carrier spectral-gap receipts into the finite Stone handoff"
        ∷ "the bridge is bounded and finite-only: it records available finite YM gap evidence next to the finite Stone generator receipt"
        ∷ "no finite Stone spectral inequality is promoted because the numeric Casimir threshold and YM-Hamiltonian-to-Stone-generator comparison API are absent"
        ∷ "physical strong continuity, traversalDerivedStoneBundle, SelfAdjointPhysicalColimitGenerator, UniformBalaban, and terminal promotion remain false"
        ∷ []
    }

canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt :
  U5FiniteStoneYMSpectralBoundBridgeReceipt
canonicalU5FiniteStoneYMSpectralBoundBridgeReceipt =
  u5FiniteStoneYMSpectralBoundBridgeReceipt
    canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt

gnsFellFiniteTraceDescentFromAudit :
  GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt →
  Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt
gnsFellFiniteTraceDescentFromAudit audit =
  GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt.modularFiniteTraceDescent
    (GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt.finiteTraceDescentConsumption
      audit)

record Gate5StoneGNSFiniteTraceCauchySchwarzBlockerReceipt : Setω where
  field
    gnsFellFiniteTraceAudit :
      GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt

    strongContinuityFailClosedReceipt :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt

    finiteTraceStateAPIAvailable :
      Bool

    exactMissingCauchySchwarzLaws :
      Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt.exactMissingLaws
        (gnsFellFiniteTraceDescentFromAudit gnsFellFiniteTraceAudit)
      ≡
      Modular.canonicalGNSCauchySchwarzMissingLaws

    exactFiniteTraceCauchySchwarzBlocker :
      String

    quotientInnerProductDescentPromoted :
      GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt.fellPromotion
        gnsFellFiniteTraceAudit
      ≡
      false

    physicalStrongContinuityPromoted :
      PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        (U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.finiteTraversalReceipt
          strongContinuityFailClosedReceipt)
      ≡
      false

    traversalDerivedStoneBundlePromoted :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.traversalDerivedStoneBundlePromoted
        strongContinuityFailClosedReceipt
      ≡
      false

    selfAdjointPhysicalColimitGeneratorPromoted :
      U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted
        strongContinuityFailClosedReceipt
      ≡
      false

    firstStoneBlocker :
      StoneGeneratorSpectralGapRemainingTarget

    firstStoneBlocker-v :
      firstStoneBlocker
      ≡
      targetGlobalNoncollapsedPhysicalPhaseSpace

    receiptBoundary :
      List String

open Gate5StoneGNSFiniteTraceCauchySchwarzBlockerReceipt public

canonicalGate5StoneGNSFiniteTraceCauchySchwarzBlockerReceipt :
  Gate5StoneGNSFiniteTraceCauchySchwarzBlockerReceipt
canonicalGate5StoneGNSFiniteTraceCauchySchwarzBlockerReceipt =
  record
    { gnsFellFiniteTraceAudit =
        GNSFell.canonicalGNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt
    ; strongContinuityFailClosedReceipt =
        canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; finiteTraceStateAPIAvailable =
        true
    ; exactMissingCauchySchwarzLaws =
        GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt.exactMissingLaws
          GNSFell.canonicalGNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt
    ; exactFiniteTraceCauchySchwarzBlocker =
        "missingParametricPreCStarMultiplicationLaw"
    ; quotientInnerProductDescentPromoted =
        GNSFell.GNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt.fellPromotion-v
          GNSFell.canonicalGNSFellCurrentWaveFiniteTraceCauchySchwarzAuditReceipt
    ; physicalStrongContinuityPromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.physicalStrongContinuityPromoted
          canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; traversalDerivedStoneBundlePromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.traversalDerivedStoneBundlePromoted-v
          canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; selfAdjointPhysicalColimitGeneratorPromoted =
        U5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt.selfAdjointPhysicalColimitGeneratorPromoted-v
          canonicalU5PhysicalStrongContinuityFiniteTraversalFailClosedReceipt
    ; firstStoneBlocker =
        targetGlobalNoncollapsedPhysicalPhaseSpace
    ; firstStoneBlocker-v =
        refl
    ; receiptBoundary =
        "Gate 5 Stone consumes the strengthened GNS/Fell finite trace-state audit before any physical Stone promotion"
        ∷ "finiteTraceStateAPIAvailable is true and the finite-trace blocker has moved to the multiplication-law residual"
        ∷ "Stone therefore cannot promote quotient inner-product descent into physical strong continuity or a traversal-derived Stone bundle"
        ∷ "physical strong continuity, SelfAdjointPhysicalColimitGenerator, and global noncollapsed phase-space promotion remain false"
        ∷ []
    }
