module DASHI.Physics.Closure.NSTriadKNEnergyCancellationAssembly where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit

------------------------------------------------------------------------
-- Exact lattice identifications between the ordered and three-leg orbits.
------------------------------------------------------------------------

conjugateMateIsSwapQEnergyLeg :
  ∀ τ →
  Symmetry.SameLatticeTriad
    (Symmetry.conjugateTriad (Orbit.orderedRealityMate τ))
    (Symmetry.swapTriad (Orbit.qEnergyLeg τ))
conjugateMateIsSwapQEnergyLeg τ =
  Symmetry.same-lattice-triad
    refl
    (Symmetry.negateModeInvolutive (Physical.k τ))
    (Symmetry.negateModeInvolutive (Physical.q τ))

conjugateMateOfSwapIsSwapPEnergyLeg :
  ∀ τ →
  Symmetry.SameLatticeTriad
    (Symmetry.conjugateTriad
      (Orbit.orderedRealityMate (Symmetry.swapTriad τ)))
    (Symmetry.swapTriad (Orbit.pEnergyLeg τ))
conjugateMateOfSwapIsSwapPEnergyLeg τ =
  Symmetry.same-lattice-triad
    refl
    (Symmetry.negateModeInvolutive (Physical.k τ))
    (Symmetry.negateModeInvolutive (Physical.p τ))

mateOfPEnergyLegIsQEnergyLeg :
  ∀ τ →
  Symmetry.SameLatticeTriad
    (Orbit.orderedRealityMate (Orbit.pEnergyLeg τ))
    (Orbit.qEnergyLeg τ)
mateOfPEnergyLegIsQEnergyLeg τ =
  Symmetry.same-lattice-triad
    refl
    refl
    (Symmetry.negateModeInvolutive (Physical.q τ))

------------------------------------------------------------------------
-- Additive and transfer laws.
------------------------------------------------------------------------

record OrderedTransferCancellationLaws
    {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar

    addZeroLeft : ∀ x → add zero x ≡ x
    addZeroRight : ∀ x → add x zero ≡ x

    reorderSix : ∀ a b c d e f →
      add (add (add a b) (add c d)) (add e f)
      ≡
      add (add (add a f) (add b d)) (add c e)

    orderedTransfer : Physical.PhysicalTriadIncidence → Scalar

    respectsLattice :
      ∀ {left right} →
      Symmetry.SameLatticeTriad left right →
      orderedTransfer left ≡ orderedTransfer right

    conjugateInvariant : ∀ τ →
      orderedTransfer (Symmetry.conjugateTriad τ)
      ≡ orderedTransfer τ

    orderedRealityMateCancels : ∀ τ →
      add
        (orderedTransfer τ)
        (orderedTransfer (Orbit.orderedRealityMate τ))
      ≡ zero

open OrderedTransferCancellationLaws public

orderedPairTransfer :
  ∀ {s} {Scalar : Set s} →
  OrderedTransferCancellationLaws Scalar →
  Physical.PhysicalTriadIncidence → Scalar
orderedPairTransfer laws τ =
  add laws
    (orderedTransfer laws τ)
    (orderedTransfer laws (Symmetry.swapTriad τ))

mateTransferEqualsSwapQ :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  orderedTransfer laws (Orbit.orderedRealityMate τ)
  ≡
  orderedTransfer laws (Symmetry.swapTriad (Orbit.qEnergyLeg τ))
mateTransferEqualsSwapQ laws τ =
  trans
    (sym (conjugateInvariant laws (Orbit.orderedRealityMate τ)))
    (respectsLattice laws (conjugateMateIsSwapQEnergyLeg τ))

mateOfSwapTransferEqualsSwapP :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  orderedTransfer laws
    (Orbit.orderedRealityMate (Symmetry.swapTriad τ))
  ≡
  orderedTransfer laws (Symmetry.swapTriad (Orbit.pEnergyLeg τ))
mateOfSwapTransferEqualsSwapP laws τ =
  trans
    (sym
      (conjugateInvariant laws
        (Orbit.orderedRealityMate (Symmetry.swapTriad τ))))
    (respectsLattice laws (conjugateMateOfSwapIsSwapPEnergyLeg τ))

mateOfPTransferEqualsQ :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  orderedTransfer laws (Orbit.orderedRealityMate (Orbit.pEnergyLeg τ))
  ≡ orderedTransfer laws (Orbit.qEnergyLeg τ)
mateOfPTransferEqualsQ laws τ =
  respectsLattice laws (mateOfPEnergyLegIsQEnergyLeg τ)

baseCancelsSwapQ :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  add laws
    (orderedTransfer laws τ)
    (orderedTransfer laws (Symmetry.swapTriad (Orbit.qEnergyLeg τ)))
  ≡ zero laws
baseCancelsSwapQ laws τ =
  subst
    (λ mateValue →
      add laws (orderedTransfer laws τ) mateValue ≡ zero laws)
    (mateTransferEqualsSwapQ laws τ)
    (orderedRealityMateCancels laws τ)

swapBaseCancelsSwapP :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  add laws
    (orderedTransfer laws (Symmetry.swapTriad τ))
    (orderedTransfer laws (Symmetry.swapTriad (Orbit.pEnergyLeg τ)))
  ≡ zero laws
swapBaseCancelsSwapP laws τ =
  subst
    (λ mateValue →
      add laws
        (orderedTransfer laws (Symmetry.swapTriad τ))
        mateValue
      ≡ zero laws)
    (mateOfSwapTransferEqualsSwapP laws τ)
    (orderedRealityMateCancels laws (Symmetry.swapTriad τ))

pCancelsQ :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  add laws
    (orderedTransfer laws (Orbit.pEnergyLeg τ))
    (orderedTransfer laws (Orbit.qEnergyLeg τ))
  ≡ zero laws
pCancelsQ laws τ =
  subst
    (λ mateValue →
      add laws
        (orderedTransfer laws (Orbit.pEnergyLeg τ))
        mateValue
      ≡ zero laws)
    (mateOfPTransferEqualsQ laws τ)
    (orderedRealityMateCancels laws (Orbit.pEnergyLeg τ))

orderedRealityCancellationImpliesThreeLegCancellation :
  ∀ {s} {Scalar : Set s}
    (laws : OrderedTransferCancellationLaws Scalar)
    (τ : Physical.PhysicalTriadIncidence) →
  add laws
    (add laws
      (orderedPairTransfer laws τ)
      (orderedPairTransfer laws (Orbit.pEnergyLeg τ)))
    (orderedPairTransfer laws (Orbit.qEnergyLeg τ))
  ≡ zero laws
orderedRealityCancellationImpliesThreeLegCancellation laws τ =
  begin
    add laws
      (add laws
        (orderedPairTransfer laws τ)
        (orderedPairTransfer laws (Orbit.pEnergyLeg τ)))
      (orderedPairTransfer laws (Orbit.qEnergyLeg τ))
  ≡⟨ reorderSix laws
        (orderedTransfer laws τ)
        (orderedTransfer laws (Symmetry.swapTriad τ))
        (orderedTransfer laws (Orbit.pEnergyLeg τ))
        (orderedTransfer laws (Symmetry.swapTriad (Orbit.pEnergyLeg τ)))
        (orderedTransfer laws (Orbit.qEnergyLeg τ))
        (orderedTransfer laws (Symmetry.swapTriad (Orbit.qEnergyLeg τ))) ⟩
    add laws
      (add laws
        (add laws
          (orderedTransfer laws τ)
          (orderedTransfer laws (Symmetry.swapTriad (Orbit.qEnergyLeg τ))))
        (add laws
          (orderedTransfer laws (Symmetry.swapTriad τ))
          (orderedTransfer laws (Symmetry.swapTriad (Orbit.pEnergyLeg τ)))))
      (add laws
        (orderedTransfer laws (Orbit.pEnergyLeg τ))
        (orderedTransfer laws (Orbit.qEnergyLeg τ)))
  ≡⟨ cong₂ (add laws)
        (cong₂ (add laws)
          (baseCancelsSwapQ laws τ)
          (swapBaseCancelsSwapP laws τ))
        (pCancelsQ laws τ) ⟩
    add laws (add laws (zero laws) (zero laws)) (zero laws)
  ≡⟨ cong (λ value → add laws value (zero laws))
        (addZeroLeft laws (zero laws)) ⟩
    add laws (zero laws) (zero laws)
  ≡⟨ addZeroLeft laws (zero laws) ⟩
    zero laws
  ∎
  where open ≡-Reasoning

energyCancellationAssemblyClosed : Bool
energyCancellationAssemblyClosed = true

energyCancellationAssemblyClosedIsTrue :
  energyCancellationAssemblyClosed ≡ true
energyCancellationAssemblyClosedIsTrue = refl
