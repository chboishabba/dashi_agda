module DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualUniqueExact where

------------------------------------------------------------------------
-- Duplicate-freedom of the conventional r=k*v residual enumeration.
--
-- The proof is layered by recoverable semantic coordinates:
--   unit -> partition vector -> factor pair -> decrement r.
-- No proof witness is part of residual identity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (_++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (_≢_; cong; cong₂; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteAllFinEnumerationExact as Finite
import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FinitePositiveFactorPairExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact as Split
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualDecompositionExact as Decompose
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualEnumerationExact as Classical
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact as Key
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Factor-pair record extensionality on the semantic coordinates.

factorPairCoordinatesExtensional :
  ∀ {r : Nat} {left right : Factor.PositiveFactorPair r} →
  Factor.divisor left ≡ Factor.divisor right →
  Factor.predecessor left ≡ Factor.predecessor right →
  left ≡ right
factorPairCoordinatesExtensional
    {left = Factor.positiveFactorPair d positive bound predecessor exact}
    {right = Factor.positiveFactorPair d' positive' bound' predecessor' exact'}
    divisorExact predecessorExact
  with divisorExact | predecessorExact
... | refl | refl =
  cong₃
    (λ p b e → Factor.positiveFactorPair d p b predecessor e)
    (NatP.≤-irrelevant positive positive')
    (NatP.≤-irrelevant bound bound')
    (NatP.≡-irrelevant exact exact')
  where
  cong₃ :
    ∀ {A B C D : Set} (f : A → B → C → D)
      {a a' : A} {b b' : B} {c c' : C} →
    a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
  cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Zero-padding is injective because its canonical prefix is recoverable.

unpadResidualVector :
  ∀ {n r : Nat} →
  r ≤ n → Vec.Vec Nat n → Vec.Vec Nat (n ∸ r)
unpadResidualVector {n} {r} bound vector =
  Split.takePrefix (n ∸ r) r
    (Normalize.transportVectorToDecomposition
      (Classical.differencePlus bound)
      vector)

transportBackwardForward :
  ∀ {left right : Nat}
    (equality : left ≡ right)
    (vector : Vec.Vec Nat left) →
  Normalize.transportVectorToDecomposition equality
    (Classical.transportVectorForward equality vector)
  ≡ vector
transportBackwardForward refl vector = refl

unpadPadResidualVector :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (vector : Vec.Vec Nat (n ∸ r)) →
  unpadResidualVector bound (Classical.padResidualVector bound vector)
  ≡ vector
unpadPadResidualVector {n} {r} bound vector =
  trans
    (cong
      (Split.takePrefix (n ∸ r) r)
      (transportBackwardForward
        (Classical.differencePlus bound)
        (Split.appendVec vector (Split.zeroVec r))))
    (Split.takePrefixAppend vector (Split.zeroVec r))

padResidualVectorInjective :
  ∀ {n r : Nat} (bound : r ≤ n)
    {left right : Vec.Vec Nat (n ∸ r)} →
  Classical.padResidualVector bound left
  ≡ Classical.padResidualVector bound right →
  left ≡ right
padResidualVectorInjective bound {left} {right} equality =
  trans
    (sym (unpadPadResidualVector bound left))
    (trans
      (cong (unpadResidualVector bound) equality)
      (unpadPadResidualVector bound right))

------------------------------------------------------------------------
-- Unit fibres are injectively mapped into residual keys.

classicalResidualKeyUnitInjective :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec.Vec Nat (n ∸ r))
    {left right : Fin (Partition.partValue
      (Classical.ambientDivisorIndex bound pair))} →
  Classical.classicalResidualKey bound pair vector left
  ≡ Classical.classicalResidualKey bound pair vector right →
  left ≡ right
classicalResidualKeyUnitInjective bound pair vector refl = refl

residualsForVectorUnique :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec.Vec Nat (n ∸ r)) →
  Unique (Classical.residualsForVector bound pair vector)
residualsForVectorUnique bound pair vector =
  UniqueP.map⁺
    (classicalResidualKeyUnitInjective bound pair vector)
    (Finite.allFinUnique
      (Partition.partValue (Classical.ambientDivisorIndex bound pair)))

residualsForVectorSource :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec.Vec Nat (n ∸ r))
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualsForVector bound pair vector →
  Key.residualVector residual ≡ Classical.padResidualVector bound vector
residualsForVectorSource bound pair vector member
  with ∈-map⁻ (Classical.classicalResidualKey bound pair vector) member
... | unit , unitMember , residualExact =
  cong Key.residualVector residualExact

------------------------------------------------------------------------
-- Partition-vector blocks are disjoint because zero-padding is injective.

residualsForPairUnique :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r) →
  Unique (Classical.residualsForPair bound pair)
residualsForPairUnique {n} {r} bound pair =
  Dep.concatMapUniqueRecoverable
    (Classical.residualsForVector bound pair)
    (Enumeration.partitionMultiplicityVectorsUnique (n ∸ r))
    (residualsForVectorUnique bound pair)
    recoverVector
  where
  recoverVector :
    ∀ {leftVector rightVector : Vec.Vec Nat (n ∸ r)}
      {leftResidual rightResidual : Key.ResidualKey n} →
    leftResidual ∈ Classical.residualsForVector bound pair leftVector →
    rightResidual ∈ Classical.residualsForVector bound pair rightVector →
    leftResidual ≡ rightResidual →
    leftVector ≡ rightVector
  recoverVector leftMember rightMember equality =
    padResidualVectorInjective bound
      (trans
        (sym (residualsForVectorSource bound pair _ leftMember))
        (trans
          (cong Key.residualVector equality)
          (residualsForVectorSource bound pair _ rightMember)))

------------------------------------------------------------------------
-- Every residual in a fixed factor-pair fibre recovers its pair coordinates.

residualPartValue :
  ∀ {n : Nat} → Key.ResidualKey n → Nat
residualPartValue residual =
  Partition.partValue (Key.residualIndex residual)

residualsForVectorPairCoordinates :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    (vector : Vec.Vec Nat (n ∸ r))
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualsForVector bound pair vector →
  (residualPartValue residual ≡ Factor.divisor pair)
  × (Key.residualPredecessor residual ≡ Factor.predecessor pair)
residualsForVectorPairCoordinates bound pair vector member
  with ∈-map⁻ (Classical.classicalResidualKey bound pair vector) member
... | unit , unitMember , residualExact =
  trans
    (cong residualPartValue residualExact)
    (Classical.ambientDivisorPartValue bound pair)
  , cong Key.residualPredecessor residualExact

residualsForPairCoordinates :
  ∀ {n r : Nat}
    (bound : r ≤ n)
    (pair : Factor.PositiveFactorPair r)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualsForPair bound pair →
  (residualPartValue residual ≡ Factor.divisor pair)
  × (Key.residualPredecessor residual ≡ Factor.predecessor pair)
residualsForPairCoordinates bound pair member
  with Product.concatMapMemberInverse
         (Classical.residualsForVector bound pair) member
... | vector , vectorMember , residualMember =
  residualsForVectorPairCoordinates bound pair vector residualMember

------------------------------------------------------------------------
-- Factor-pair blocks are disjoint because residual equality recovers divisor
-- and predecessor, which extensionally determine the pair record.

residualBlockUnique :
  ∀ {n r : Nat}
    (positive : suc zero ≤ r)
    (bound : r ≤ n) →
  Unique (Classical.residualBlock positive bound)
residualBlockUnique {n} {r} positive bound =
  Dep.concatMapUniqueRecoverable
    (Classical.residualsForPair bound)
    (Factor.positiveFactorPairsUnique r positive)
    (residualsForPairUnique bound)
    recoverPair
  where
  recoverPair :
    ∀ {leftPair rightPair : Factor.PositiveFactorPair r}
      {leftResidual rightResidual : Key.ResidualKey n} →
    leftResidual ∈ Classical.residualsForPair bound leftPair →
    rightResidual ∈ Classical.residualsForPair bound rightPair →
    leftResidual ≡ rightResidual →
    leftPair ≡ rightPair
  recoverPair {leftPair} {rightPair} leftMember rightMember equality =
    factorPairCoordinatesExtensional divisorExact predecessorExact
    where
    leftCoordinates = residualsForPairCoordinates bound leftPair leftMember
    rightCoordinates = residualsForPairCoordinates bound rightPair rightMember

    divisorExact : Factor.divisor leftPair ≡ Factor.divisor rightPair
    divisorExact =
      trans
        (sym (proj₁ leftCoordinates))
        (trans
          (cong residualPartValue equality)
          (proj₁ rightCoordinates))

    predecessorExact :
      Factor.predecessor leftPair ≡ Factor.predecessor rightPair
    predecessorExact =
      trans
        (sym (proj₂ leftCoordinates))
        (trans
          (cong Key.residualPredecessor equality)
          (proj₂ rightCoordinates))

------------------------------------------------------------------------
-- A fixed r-block is tagged by the decrement recovered from its residual key.

residualBlockDecrementExact :
  ∀ {n r : Nat}
    (positive : suc zero ≤ r)
    (bound : r ≤ n)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.residualBlock positive bound →
  Decompose.residualDecrement residual ≡ r
residualBlockDecrementExact positive bound member
  with Product.concatMapMemberInverse
         (Classical.residualsForPair bound) member
... | pair , pairMember , residualMember =
  trans
    (cong₂ _*_
      (cong suc (proj₂ coordinates))
      (proj₁ coordinates))
    (sym (Factor.productExact pair))
  where
  coordinates = residualsForPairCoordinates bound pair residualMember

------------------------------------------------------------------------
-- Earlier r-blocks have decrement bounded by the current upper index.

classicalResidualsUpToDecrementBound :
  ∀ {n current : Nat}
    (bound : current ≤ n)
    {residual : Key.ResidualKey n} →
  residual ∈ Classical.classicalResidualsUpTo n current bound →
  Decompose.residualDecrement residual ≤ current
classicalResidualsUpToDecrementBound {current = zero} z≤n ()
classicalResidualsUpToDecrementBound {n} {suc current} bound member
  with ∈-++⁻
         (Classical.classicalResidualsUpTo n current
           (Classical.dropPositiveBound bound))
         member
... | inj₁ earlier =
  NatP.≤-step
    (classicalResidualsUpToDecrementBound
      (Classical.dropPositiveBound bound) earlier)
... | inj₂ blockMember =
  NatP.≤-reflexive
    (residualBlockDecrementExact (s≤s z≤n) bound blockMember)

------------------------------------------------------------------------
-- Outer r-blocks are disjoint because the key itself recovers r.

classicalResidualsUpToUnique :
  (n current : Nat)
  (bound : current ≤ n) →
  Unique (Classical.classicalResidualsUpTo n current bound)
classicalResidualsUpToUnique n zero z≤n = AllPairs.[]
classicalResidualsUpToUnique n (suc current) bound =
  Dep.uniqueAppendDisjoint
    (classicalResidualsUpToUnique n current
      (Classical.dropPositiveBound bound))
    (residualBlockUnique (s≤s z≤n) bound)
    cross
  where
  cross :
    ∀ {left right : Key.ResidualKey n} →
    left ∈ Classical.classicalResidualsUpTo n current
      (Classical.dropPositiveBound bound) →
    right ∈ Classical.residualBlock (s≤s z≤n) bound →
    left ≢ right
  cross leftMember rightMember equality =
    NatP.1+n≰n impossible
    where
    leftBound : Decompose.residualDecrement left ≤ current
    leftBound =
      classicalResidualsUpToDecrementBound
        (Classical.dropPositiveBound bound) leftMember

    rightExact : Decompose.residualDecrement right ≡ suc current
    rightExact =
      residualBlockDecrementExact (s≤s z≤n) bound rightMember

    sameDecrement :
      Decompose.residualDecrement left ≡ Decompose.residualDecrement right
    sameDecrement = cong Decompose.residualDecrement equality

    impossible : suc current ≤ current
    impossible =
      subst
        (λ value → value ≤ current)
        (trans sameDecrement rightExact)
        leftBound

classicalFactorResidualEnumerationUnique :
  (n : Nat) → Unique (Classical.classicalFactorResidualEnumeration n)
classicalFactorResidualEnumerationUnique n =
  classicalResidualsUpToUnique n n NatP.≤-refl

------------------------------------------------------------------------
-- The conventional factor-pair residual list is now finite and duplicate-free.
------------------------------------------------------------------------
