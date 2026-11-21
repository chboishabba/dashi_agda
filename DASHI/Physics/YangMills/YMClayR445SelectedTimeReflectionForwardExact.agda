module DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact where

-- Exact original side4->side2 geometry and non-Abelian two-link group law.
-- Owners: BalabanPeriodicTorus4Carrier, BalabanClayGate4PeriodicBondPathBianchiExact,
-- YMClayNativeBlockedPositiveHolonomyGaugeExact.
-- This is a source-level constructive lemma, NOT an inhabited
-- YMClayOriginalWilsonNativeOSPullbackExact.NativeBlockReflectsExactly.
-- Physical fine Wilson RP, positive-time word grammar and Agda kernel OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Native

Two : Nat
Two = suc (suc zero)
Four : Nat
Four = Torus.four
C2 : Set
C2 = Torus.CyclicIndex Two
C4 : Set
C4 = Torus.CyclicIndex Four
FineSite : Set
FineSite = Torus.periodicTorus4Definition Four
CoarseSite : Set
CoarseSite = Torus.periodicTorus4Definition Two

-- Selected mirror at the even R445 block boundary: t -> -t (mod 4).
reflectFineTime : C4 → C4
reflectFineTime Torus.zeroᵢ = Torus.zeroᵢ
reflectFineTime (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
reflectFineTime (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)
reflectFineTime (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) =
  Torus.sucᵢ Torus.zeroᵢ

-- On C2, negation fixes both coordinates.
reflectCoarseTime : C2 → C2
reflectCoarseTime Torus.zeroᵢ = Torus.zeroᵢ
reflectCoarseTime (Torus.sucᵢ Torus.zeroᵢ) = Torus.sucᵢ Torus.zeroᵢ

evenTime : C2 → C4
evenTime Torus.zeroᵢ = Torus.zeroᵢ
evenTime (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)

fineReflectionInvolutive :
  (t : C4) → reflectFineTime (reflectFineTime t) ≡ t
fineReflectionInvolutive Torus.zeroᵢ = refl
fineReflectionInvolutive (Torus.sucᵢ Torus.zeroᵢ) = refl
fineReflectionInvolutive (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
fineReflectionInvolutive
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

evenOriginReflects :
  (t : C2) →
  reflectFineTime (evenTime t) ≡ evenTime (reflectCoarseTime t)
evenOriginReflects Torus.zeroᵢ = refl
evenOriginReflects (Torus.sucᵢ Torus.zeroᵢ) = refl

reflectFineSite : FineSite → FineSite
reflectFineSite
  (Torus.pair (Torus.pair t x) (Torus.pair y z)) =
  Torus.pair (Torus.pair (reflectFineTime t) x) (Torus.pair y z)

reflectCoarseSite : CoarseSite → CoarseSite
reflectCoarseSite
  (Torus.pair (Torus.pair t x) (Torus.pair y z)) =
  Torus.pair (Torus.pair (reflectCoarseTime t) x) (Torus.pair y z)

evenCoarseOrigin : CoarseSite → FineSite
evenCoarseOrigin
  (Torus.pair (Torus.pair t x) (Torus.pair y z)) =
  Torus.pair
    (Torus.pair (evenTime t) (evenTime x))
    (Torus.pair (evenTime y) (evenTime z))

reflectEvenCoarseOrigin :
  (site : CoarseSite) →
  reflectFineSite (evenCoarseOrigin site) ≡
  evenCoarseOrigin (reflectCoarseSite site)
reflectEvenCoarseOrigin
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite evenOriginReflects t = refl

-- A selected coarse positive temporal path starts at T=0 and
-- consumes original fine time-link starts t=0 and t=1.
data SelectedPositiveFineTimeStart : C4 → Set where
  positive0 : SelectedPositiveFineTimeStart Torus.zeroᵢ
  positive1 : SelectedPositiveFineTimeStart (Torus.sucᵢ Torus.zeroᵢ)

firstFineTimeStartPositive :
  SelectedPositiveFineTimeStart (evenTime Torus.zeroᵢ)
firstFineTimeStartPositive = positive0
secondFineTimeStartPositive :
  SelectedPositiveFineTimeStart (Torus.sucᵢ Torus.zeroᵢ)
secondFineTimeStartPositive = positive1

module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where
  originalNativeTwoLink :
    Bond.PeriodicBondField 3 Value → FineSite → Torus.Axis4 → Value
  originalNativeTwoLink field site axis =
    Native.positiveHolonomy group field site axis (suc (suc zero))

  originalTwoLinkOrderedProduct :
    (field : Bond.PeriodicBondField 3 Value)
    (site : FineSite) (axis : Torus.Axis4) →
    originalNativeTwoLink field site axis ≡
    Bond.multiply group
      (field (Torus.pair site axis))
      (field (Torus.pair (Bond.positiveStep site axis) axis))
  originalTwoLinkOrderedProduct field site axis =
    cong (Bond.multiply group (field (Torus.pair site axis)))
      (Bond.identityRight group
        (field (Torus.pair (Bond.positiveStep site axis) axis)))

  reflectedOrderedTimeBlock :
    (u v : Value) →
    Bond.multiply group (Bond.inverse group v) (Bond.inverse group u)
      ≡ Bond.inverse group (Bond.multiply group u v)
  reflectedOrderedTimeBlock u v =
    sym (Bond.inverseProduct group u v)

-- OPEN: prove original SUN native field reflection (all four axes),
-- NativeBlockReflectsExactly for ALL original coarse observables,
-- physical positive-time support, and published Wilson fine RP.
