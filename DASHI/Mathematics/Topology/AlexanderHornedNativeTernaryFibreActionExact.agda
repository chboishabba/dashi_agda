module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact where

------------------------------------------------------------------------
-- NATIVE LOCAL FIBRE ACTION ON THE EXISTING TERNARY END TOWER.
--
-- Existing owner: AlexanderHornedNativeBalancedTernaryEndTowerExact
-- for K_n = C3 × Trit^n and its coherent inverse limit.
-- Existing owner: FiniteC3OrbitStabilizerExact for the C3 group.
-- Existing owner: RecursiveFibreTower for the inverse-limit interface.
--
-- This source adds:
--   A_n = (K_n -> C3), with pointwise group operations;
--   A_n acts freely/transitively on C3-valued phase configurations;
--   p_n^* : A_n -> A_(n+1) is an injective group homomorphism;
--   external sector rotation commutes with every refinement;
--   finite-depth representatives evaluate on infinite end addresses.
--
-- Classical mathematical source roots: inverse limits, clopen Cantor
-- cylinders, direct limits of groups, permutation representations.
-- This is NOT a 3D wild-ball realization, a nonabelian SU2 holonomy,
-- or the pre-existing orbifold pi1 semidirect product.
-- No postulates, function extensionality axiom or unproved group law.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End

-- The local gauge group at native ternary address resolution n:
-- a C3-valued function at every one of 3 * 3^n address cells.
FibreAction : Nat → Set
FibreAction n = End.BalancedLevel n → C3.C3

PhaseField : Nat → Set
PhaseField = FibreAction

identityAction : ∀ {n} → FibreAction n
identityAction _ = C3.c0

combine : ∀ {n} → FibreAction n → FibreAction n → FibreAction n
combine a b x = C3._∙_ (a x) (b x)

inverseAction : ∀ {n} → FibreAction n → FibreAction n
inverseAction a x = C3.inverse (a x)

act : ∀ {n} → FibreAction n → PhaseField n → PhaseField n
act g f = combine g f

-- Function equality is *pointwise*, so the module needs neither
-- postulated extensionality nor a new duplicate abstract Group record.
actionAssociative : ∀ {n} (g h f : FibreAction n)
  (x : End.BalancedLevel n) →
  act (combine g h) f x ≡ act g (act h f) x
actionAssociative g h f x = C3.associative (g x) (h x) (f x)

actionIdentity : ∀ {n} (f : FibreAction n)
  (x : End.BalancedLevel n) →
  act identityAction f x ≡ f x
actionIdentity f x = C3.leftIdentity (f x)

actionInverse : ∀ {n} (g f : FibreAction n)
  (x : End.BalancedLevel n) →
  act (inverseAction g) (act g f) x ≡ f x
actionInverse g f x
  rewrite C3.inverseLeft (g x) = refl

freeAction : ∀ {n} (g f : FibreAction n)
  (h : ∀ x → act g f x ≡ f x)
  (x : End.BalancedLevel n) →
  g x ≡ C3.c0
freeAction g f h x with g x | f x | h x
... | C3.c0 | _ | _ = refl
... | C3.c1 | C3.c0 | ()
... | C3.c1 | C3.c1 | ()
... | C3.c1 | C3.c2 | ()
... | C3.c2 | C3.c0 | ()
... | C3.c2 | C3.c1 | ()
... | C3.c2 | C3.c2 | ()

-- Any phase configuration is reachable from any other, using
-- the pointwise C3 difference. This is a torsor at every depth.
difference : ∀ {n} → PhaseField n → PhaseField n → FibreAction n
difference f target x =
  C3._∙_ (target x) (C3.inverse (f x))

transitiveAction : ∀ {n} (f target : PhaseField n)
  (x : End.BalancedLevel n) →
  act (difference f target) f x ≡ target x
transitiveAction f target x
  rewrite C3.associative (target x)
                          (C3.inverse (f x)) (f x)
        | C3.inverseLeft (f x)
        | C3.rightIdentity (target x) = refl

pullback : ∀ n → FibreAction n → FibreAction (suc n)
pullback n g x = g (End.balancedProjection n x)

pullbackIdentity : ∀ n (x : End.BalancedLevel (suc n)) →
  pullback n identityAction x ≡ identityAction x
pullbackIdentity n x = refl

pullbackMultiplication : ∀ n (g h : FibreAction n)
  (x : End.BalancedLevel (suc n)) →
  pullback n (combine g h) x ≡
    combine (pullback n g) (pullback n h) x
pullbackMultiplication n g h x = refl

pullbackInverse : ∀ n (g : FibreAction n)
  (x : End.BalancedLevel (suc n)) →
  pullback n (inverseAction g) x ≡ inverseAction (pullback n g) x
pullbackInverse n g x = refl

-- The existing snoc section proves every projection is surjective.
section : ∀ n → End.BalancedLevel n → End.BalancedLevel (suc n)
section n (c , xs) = c , End.snoc xs Trit.zero

sectionProjection : ∀ n (x : End.BalancedLevel n) →
  End.balancedProjection n (section n x) ≡ x
sectionProjection n (c , xs) =
  cong (λ ys → (c , ys)) (End.dropLastSnoc xs Trit.zero)

pullbackInjective : ∀ n (g h : FibreAction n) →
  (∀ y → pullback n g y ≡ pullback n h y) →
  ∀ x → g x ≡ h x
pullbackInjective n g h equal x
  rewrite sym (sectionProjection n x) = equal (section n x)

-- Rotate sectors on BOTH field domain and the outer end address.
-- Pullback of a field by this automorphism is the natural action.
rotateField : ∀ n → FibreAction n → FibreAction n
rotateField n g x = g (End.rotateBalancedLevel n x)

rotatePullbackSquare : ∀ n (g : FibreAction n)
  (x : End.BalancedLevel (suc n)) →
  rotateField (suc n) (pullback n g) x ≡
    pullback n (rotateField n g) x
rotatePullbackSquare n g x
  rewrite End.rotateBalancedProjectionSquare n x = refl

rotateFieldCubed : ∀ n (g : FibreAction n)
  (x : End.BalancedLevel n) →
  rotateField n (rotateField n (rotateField n g)) x ≡ g x
rotateFieldCubed n g x
  rewrite End.balancedRotationCubed n x = refl

rotateActionSquare : ∀ n (g f : FibreAction n)
  (x : End.BalancedLevel n) →
  rotateField n (act g f) x ≡
    act (rotateField n g) (rotateField n f) x
rotateActionSquare n g f x = refl

-- A finite-depth representative defines a locally constant function
-- on the full native infinite address space, constant on its n-cylinder.
record LocalFibreAction : Set where
  constructor local-action
  field
    depth : Nat
    fieldAt : FibreAction depth

open LocalFibreAction public

evalLocal : LocalFibreAction → End.BalancedEndPoint → C3.C3
evalLocal (local-action n f) end =
  f (Tower.stateAt end n)

liftLocal : ∀ n → FibreAction n → LocalFibreAction
liftLocal n f = local-action n f

-- Evaluation at an infinite end is invariant under one refinement
-- of the chosen finite-depth field representative.
refinementEvaluation : ∀ n (f : FibreAction n)
  (end : End.BalancedEndPoint) →
  evalLocal (liftLocal (suc n) (pullback n f)) end ≡
    evalLocal (liftLocal n f) end
refinementEvaluation n f end
  rewrite Tower.coherent end n = refl

-- This finite-depth presentation is the compact-clopen locally
-- constant function group modulo eventual pullback equality.
-- The quotient / continuous-function universal property is a
-- SEPARATE topological implementation obligation, not assumed here.
