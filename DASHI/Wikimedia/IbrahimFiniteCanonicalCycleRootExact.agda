module DASHI.Wikimedia.IbrahimFiniteCanonicalCycleRootExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General
import DASHI.Wikimedia.IbrahimCycleRotationRelationExact as Rotation

------------------------------------------------------------------------
-- NEW DASHI finite construction of a LEAST cycle representative.
-- Assumptions are explicit: complete finite carrier, a total
-- antisymmetric transitive/reflexive order, and DECIDABLE membership
-- in the same intrinsic terminal cycle. The latter is a mathematical
-- decision procedure obligation, NOT QID/title or source authority.
--
-- Original Wikipedia FLN methodology: Ibrahim / Danforth / Dodds,
-- DOI: 10.1016/j.jocs.2016.12.001. New canonical-root mathematics
-- is implemented in DASHI and does not revise the original paper.
------------------------------------------------------------------------

record FiniteTotalOrder (Node : Set) : Set₁ where
  constructor finiteTotalOrder
  field
    lessOrEqual : Node → Node → Set
    reflexive : (node : Node) → lessOrEqual node node
    transitive : ∀ {a b c} →
      lessOrEqual a b → lessOrEqual b c → lessOrEqual a c
    comparable : (a b : Node) →
      lessOrEqual a b ⊎ lessOrEqual b a
    antisymmetric : ∀ {a b} →
      lessOrEqual a b → lessOrEqual b a → a ≡ b
open FiniteTotalOrder public

record LeastFromSeed {Node : Set}
    (P : Node → Set) (order : FiniteTotalOrder Node)
    (seed : Node) (xs : List Node) : Set where
  constructor leastFromSeed
  field
    selected : Node
    selectedHasProperty : P selected
    selectedBelowSeed : lessOrEqual order selected seed
    selectedBelowList :
      ∀ {other} → General.Listed other xs → P other →
      lessOrEqual order selected other
open LeastFromSeed public

emptyListingImpossible :
  ∀ {Node : Set} {node : Node} →
  General.Listed node [] → ⊥
emptyListingImpossible ()

leastFromFiniteList :
  ∀ {Node : Set}
    (P : Node → Set) (order : FiniteTotalOrder Node) →
  ((node : Node) → P node ⊎ (P node → ⊥)) →
  (seed : Node) → P seed → (xs : List Node) →
  LeastFromSeed P order seed xs
leastFromFiniteList P order decide seed proof [] =
  leastFromSeed seed proof (reflexive order seed)
    (λ listed _ → ⊥-elim (emptyListingImpossible listed))
leastFromFiniteList P order decide seed proof (x ∷ xs)
  with leastFromFiniteList P order decide seed proof xs | decide x
... | prior | inj₂ missing =
  leastFromSeed
    (selected prior)
    (selectedHasProperty prior)
    (selectedBelowSeed prior)
    (λ { General.listedHere present → ⊥-elim (missing present)
       ; (General.listedThere membership) present →
           selectedBelowList prior membership present })
... | prior | inj₁ present
  with comparable order (selected prior) x
...   | inj₁ prior≤x =
  leastFromSeed
    (selected prior)
    (selectedHasProperty prior)
    (selectedBelowSeed prior)
    (λ { General.listedHere _ → prior≤x
       ; (General.listedThere membership) witness →
           selectedBelowList prior membership witness })
...   | inj₂ x≤prior =
  leastFromSeed
    x present
    (transitive order x≤prior (selectedBelowSeed prior))
    (λ { General.listedHere _ → reflexive order x
       ; (General.listedThere membership) witness →
           transitive order x≤prior
             (selectedBelowList prior membership witness) })

------------------------------------------------------------------------
-- The original carrier covers every node; hence a proven minimum
-- across that list is a minimum among ALL nodes in the same cycle.
------------------------------------------------------------------------

canonicalCycleRootExistsForFiniteDecidableOrder :
  ∀ {Node : Set} {next : Node → Node} →
  (carrier : General.CompleteFiniteCarrier Node)
  (order : FiniteTotalOrder Node) →
  (decideCycle : (base node : Node) →
    Rotation.MutualOrbitRotation next base node ⊎
    (Rotation.MutualOrbitRotation next base node → ⊥)) →
  (base : Node) →
  Rotation.CanonicalCycleRoot next (lessOrEqual order) base
canonicalCycleRootExistsForFiniteDecidableOrder {next = next}
    carrier order decideCycle base =
  Rotation.canonicalCycleRoot
    (selected minimum)
    (selectedHasProperty minimum)
    (λ other onCycle →
      selectedBelowList minimum (General.covers carrier other) onCycle)
  where
    minimum :
      LeastFromSeed
        (Rotation.MutualOrbitRotation next base)
        order base (General.allNodes carrier)
    minimum =
      leastFromFiniteList
        (Rotation.MutualOrbitRotation next base)
        order (decideCycle base) base
        Rotation.mutualOrbitRotationReflexive
        (General.allNodes carrier)

canonicalCycleChoiceIndependent :
  ∀ {Node : Set} {next : Node → Node} {start : Node} →
  (carrier : General.CompleteFiniteCarrier Node)
  (order : FiniteTotalOrder Node) →
  (decideCycle : (base node : Node) →
    Rotation.MutualOrbitRotation next base node ⊎
    (Rotation.MutualOrbitRotation next base node → ⊥)) →
  (first second : Orbit.EventualCycle next start) →
  Rotation.CanonicalCycleRoot.root
    (canonicalCycleRootExistsForFiniteDecidableOrder
      carrier order decideCycle (Orbit.representative first))
  ≡
  Rotation.CanonicalCycleRoot.root
    (canonicalCycleRootExistsForFiniteDecidableOrder
      carrier order decideCycle (Orbit.representative second))
canonicalCycleChoiceIndependent carrier order decideCycle first second =
  Rotation.canonicalCycleRepresentativeUnique
    (antisymmetric order)
    first second
    (canonicalCycleRootExistsForFiniteDecidableOrder
      carrier order decideCycle (Orbit.representative first))
    (canonicalCycleRootExistsForFiniteDecidableOrder
      carrier order decideCycle (Orbit.representative second))

-- Next possible removal of an assumption: derive decideCycle from
-- bounded reachability on an exhaustive finite graph with decidable
-- equality. That decision algorithm, and any physically sourced
-- statement about real Wikipedia, remain distinct obligations.
