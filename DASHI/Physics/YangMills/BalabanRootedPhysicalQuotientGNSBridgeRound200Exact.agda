module DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientGNSBridgeRound200Exact where

------------------------------------------------------------------------
-- ROUND 200
--
-- BIDI terminal-carrier bridge.
--
-- This module deliberately does not invent positivity, a measure, or a
-- Hamiltonian.  It isolates the exact representation payment needed to reuse
-- any existing positive/GNS completion on the rooted physical quotient built
-- in the finite Balaban lane.
--
-- The mathematical point is simple but important: once a canonical rooted
-- normal form N is available, a GNS null quotient need not be a second,
-- unrelated quotient.  It is enough to provide a same-object realization of
-- the GNS pre-Hilbert carrier on rooted representatives and prove that its
-- null relation is exactly the physical zero-norm relation there.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

record RootedPhysicalQuotientGNSBridge
    (Configuration RootedCarrier Scalar : Set) : Set₁ where
  field
    normalise : Configuration → RootedCarrier

    -- The pre-Hilbert/GNS carrier is literally the rooted physical carrier.
    GNSCarrier : Set
    sameCarrier : GNSCarrier ≡ RootedCarrier

    zero : Scalar
    normSquared : RootedCarrier → Scalar

    PhysicalNull : RootedCarrier → Set
    GNSNull : GNSCarrier → Set

    -- Same-object nullity after transporting the GNS carrier to the rooted
    -- carrier.  This is the only semantic payment needed for quotient reuse.
    gnsNullOnRooted : RootedCarrier → Set
    gnsNullOnRootedIsPhysicalNull :
      ∀ x → gnsNullOnRooted x ≡ PhysicalNull x

    physicalNullIsZeroNorm :
      ∀ x → PhysicalNull x ≡ (normSquared x ≡ zero)

open RootedPhysicalQuotientGNSBridge public

PhysicalQuotientPoint :
  ∀ {Configuration RootedCarrier Scalar} →
  RootedPhysicalQuotientGNSBridge Configuration RootedCarrier Scalar → Set
PhysicalQuotientPoint bridge = RootedCarrier

GNSQuotientPoint :
  ∀ {Configuration RootedCarrier Scalar} →
  RootedPhysicalQuotientGNSBridge Configuration RootedCarrier Scalar → Set
GNSQuotientPoint bridge = RootedCarrier

-- No new quotient data are introduced: both terminal points are represented
-- by the same rooted carrier.
physicalAndGNSPointCarriersCoincide :
  ∀ {Configuration RootedCarrier Scalar}
    (bridge : RootedPhysicalQuotientGNSBridge
      Configuration RootedCarrier Scalar) →
  PhysicalQuotientPoint bridge ≡ GNSQuotientPoint bridge
physicalAndGNSPointCarriersCoincide bridge = refl

-- The null seam has now been reduced to equality of predicates on one object.
rootedGNSNullIsPhysicalNull :
  ∀ {Configuration RootedCarrier Scalar}
    (bridge : RootedPhysicalQuotientGNSBridge
      Configuration RootedCarrier Scalar)
    (x : RootedCarrier) →
  gnsNullOnRooted bridge x ≡ PhysicalNull bridge x
rootedGNSNullIsPhysicalNull = gnsNullOnRootedIsPhysicalNull

rootedGNSNullIsZeroNorm :
  ∀ {Configuration RootedCarrier Scalar}
    (bridge : RootedPhysicalQuotientGNSBridge
      Configuration RootedCarrier Scalar)
    (x : RootedCarrier) →
  gnsNullOnRooted bridge x ≡
    (normSquared bridge x ≡ zero bridge)
rootedGNSNullIsZeroNorm bridge x =
  transSet
    (gnsNullOnRootedIsPhysicalNull bridge x)
    (physicalNullIsZeroNorm bridge x)
  where
  transSet : ∀ {A B C : Set} → A ≡ B → B ≡ C → A ≡ C
  transSet refl refl = refl

-- A compact receipt for downstream terminal compilers: the normalized
-- configuration already lands in the unique carrier on which physical and
-- GNS nullity are compared.
record RootedGNSReuseReceipt
    {Configuration RootedCarrier Scalar : Set}
    (bridge : RootedPhysicalQuotientGNSBridge
      Configuration RootedCarrier Scalar)
    (configuration : Configuration) : Set₁ where
  field
    point : RootedCarrier
    pointIsNormalForm : point ≡ normalise bridge configuration
    nullPredicatesAgree :
      gnsNullOnRooted bridge point ≡ PhysicalNull bridge point

compileRootedGNSReuseReceipt :
  ∀ {Configuration RootedCarrier Scalar}
    (bridge : RootedPhysicalQuotientGNSBridge
      Configuration RootedCarrier Scalar)
    (configuration : Configuration) →
  RootedGNSReuseReceipt bridge configuration
compileRootedGNSReuseReceipt bridge configuration = record
  { point = normalise bridge configuration
  ; pointIsNormalForm = refl
  ; nullPredicatesAgree =
      gnsNullOnRootedIsPhysicalNull bridge (normalise bridge configuration)
  }
