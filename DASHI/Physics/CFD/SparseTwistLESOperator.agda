module DASHI.Physics.CFD.SparseTwistLESOperator where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.InvolutiveTernaryDynamics as Ternary
import DASHI.Learning.GrokkingOperatorContract as Learning

------------------------------------------------------------------------
-- DASHI–LES sparse/twist operator contract.
--
-- This module connects the existing involutive ternary foundation and MDL
-- learning-operator surface to a CFD-facing proxy contract.  It formalises the
-- claim shape needed by the vorticity experiments:
--
--   * the field carrier is signed and ternary at the structural layer;
--   * sparsity is the derived support quotient, never a replacement for sign;
--   * vortical structure is carried by sparse signed atoms;
--   * a twist operator transports those atoms equivariantly;
--   * encode, proxy evolution, and decode form a commuting square;
--   * exact reconstruction is available as a law of a lossless codec;
--   * storage and update advantages are explicit witnesses, not inferred from
--     the existence of the proxy.
--
-- No asymptotic speedup, Navier–Stokes closure, or empirical fidelity claim is
-- derived merely by inhabiting these records.
------------------------------------------------------------------------

private
  cong : ∀ {a b} {A : Set a} {B : Set b}
       → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
  cong f refl = refl

  trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

------------------------------------------------------------------------
-- Signed sparse structural carrier.
--
-- `support` is required to agree with the derived support map already proved
-- involution-invariant in InvolutiveTernaryDynamics.  Hence negative
-- vorticity is active structure, not absence.
------------------------------------------------------------------------

record SignedSparseField (Index : Set) : Set where
  field
    value : Index → Trit.Trit
    support : Index → Bool
    support-is-derived : ∀ i → support i ≡ Ternary.support (value i)

open SignedSparseField public

support-invariant-under-sign :
  ∀ {Index} (F : SignedSparseField Index) i →
  Ternary.support (Trit.inv (value F i)) ≡ Ternary.support (value F i)
support-invariant-under-sign F i = Ternary.support-invariant (value F i)

------------------------------------------------------------------------
-- Sparse vorticity atom.
--
-- Position, strength, scale, and orientation are deliberately abstract.  An
-- application may instantiate these with grid cells, wavelets, vortex blobs,
-- filaments, mesh entities, or another chart family.
------------------------------------------------------------------------

record SparseTwistAtom
  (Position Strength Scale Orientation : Set) : Set where
  field
    position : Position
    strength : Strength
    scale : Scale
    orientation : Orientation
    sign : Trit.Trit

open SparseTwistAtom public

------------------------------------------------------------------------
-- Twist transport.
--
-- The involution law states that transporting the opposite signed/oriented
-- state gives the opposite transported state.  `sparseNonexpansive` is the
-- structural analogue of not creating more active atoms than the chosen
-- budget allows.
------------------------------------------------------------------------

record TwistOperator : Set₁ where
  field
    Field : Set
    Control : Set

    fieldι : Field → Field
    controlι : Control → Control
    fieldι-involutive : ∀ x → fieldι (fieldι x) ≡ x
    controlι-involutive : ∀ u → controlι (controlι u) ≡ u

    twist : Field → Control → Field
    twist-equivariant :
      ∀ x u → twist (fieldι x) (controlι u) ≡ fieldι (twist x u)

    activeCost : Field → Nat
    sparseNonexpansive : ∀ x u → activeCost (twist x u) ≤ activeCost x

open TwistOperator public

------------------------------------------------------------------------
-- Lossless structural codec.
--
-- `decode-encode` is the full-fidelity law.  A quality-controlled lossy codec
-- is obtained by weakening this equality to an application-specific error
-- relation; that relation is intentionally not guessed here.
------------------------------------------------------------------------

record LosslessStructuralCodec : Set₁ where
  field
    FullState : Set
    ProxyState : Set

    encode : FullState → ProxyState
    decode : ProxyState → FullState

    decode-encode : ∀ x → decode (encode x) ≡ x

    fullStorageCost : FullState → Nat
    proxyStorageCost : ProxyState → Nat
    storageNonexpansive : ∀ x → proxyStorageCost (encode x) ≤ fullStorageCost x

open LosslessStructuralCodec public

------------------------------------------------------------------------
-- Learned proxy operator and exact commuting square.
--
-- The central solver-replacement obligation is not low reconstruction error
-- at one snapshot.  It is the commuting law below: decoding one proxy update
-- must equal one full-state update.  Iteration then gives exact rollout for
-- every finite horizon.
------------------------------------------------------------------------

record ExactLearnedProxyOperator (C : LosslessStructuralCodec) : Set₁ where
  field
    fullStep : FullState C → FullState C
    proxyStep : ProxyState C → ProxyState C

    step-commutes :
      ∀ p → decode C (proxyStep p) ≡ fullStep (decode C p)

    learner : Learning.LearningOperator (ProxyState C)
    learner-step-agrees :
      ∀ p → Learning.step learner p ≡ proxyStep p

    fullUpdateCost : FullState C → Nat
    proxyUpdateCost : ProxyState C → Nat
    updateNonexpansive :
      ∀ x → proxyUpdateCost (encode C x) ≤ fullUpdateCost x

open ExactLearnedProxyOperator public

iterate : ∀ {A : Set} → Nat → (A → A) → A → A
iterate zero f x = x
iterate (suc n) f x = f (iterate n f x)

proxy-rollout-exact :
  ∀ (C : LosslessStructuralCodec)
    (O : ExactLearnedProxyOperator C)
    n p →
  decode C (iterate n (proxyStep O) p) ≡
  iterate n (fullStep O) (decode C p)
proxy-rollout-exact C O zero p = refl
proxy-rollout-exact C O (suc n) p =
  trans
    (step-commutes O (iterate n (proxyStep O) p))
    (cong (fullStep O) (proxy-rollout-exact C O n p))

encoded-rollout-exact :
  ∀ (C : LosslessStructuralCodec)
    (O : ExactLearnedProxyOperator C)
    n x →
  decode C (iterate n (proxyStep O) (encode C x)) ≡
  iterate n (fullStep O) x
encoded-rollout-exact C O n x =
  trans
    (proxy-rollout-exact C O n (encode C x))
    (cong (iterate n (fullStep O)) (decode-encode C x))

------------------------------------------------------------------------
-- DASHI–LES bundle.
--
-- This is the reusable theorem-facing object: signed sparse structure, twist
-- transport, codec, learned operator, and explicit cost witnesses are carried
-- together.  Concrete CFD scenes must still instantiate and validate every
-- field.
------------------------------------------------------------------------

record DASHILESSystem : Setω where
  field
    codec : LosslessStructuralCodec
    learnedOperator : ExactLearnedProxyOperator codec
    twistOperator : TwistOperator

    structuralIndex : Set
    signedStructure : FullState codec → SignedSparseField structuralIndex

    twistIsFullStep :
      ∀ x →
      fullStep learnedOperator x ≡ fullStep learnedOperator x

open DASHILESSystem public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record DASHILESClaimBoundary : Set where
  field
    signedTernaryCarrierReused : Bool
    binarySupportIsDerived : Bool
    sparseTwistChannelPresent : Bool
    exactnessRequiresCommutingWitness : Bool
    asymptoticSpeedupProved : Bool
    navierStokesSolved : Bool
    empiricalCFDFidelityProved : Bool
