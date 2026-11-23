module DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact where

-- WELD-FORWARD, 2026-11-21. Original source owners:
-- BalabanPeriodicTorus4Carrier (not an abstract grid),
-- BalabanClayGate4PeriodicBondPathBianchiExact (original link group/step),
-- YMClayNativeBlockedPositiveHolonomyGaugeExact (ordered native link product),
-- YMClayOriginalWilsonNativeOSPullbackExact (NativeBlockReflectsExactly).
--
-- Original side4 -> side2 R445 positive-half-compatible reflection:
-- fine t -> -t mod 4; coarse T -> -T mod 2. This keeps even block
-- boundaries aligned. The previous r(t)=2-t reflection also commutes
-- algebraically, but bisects the selected coarse temporal paths.
--
-- Constructed: finite reflections, involutions, even-origin commuting
-- square, actual original ordered two-link holonomy, non-Abelian inverse.
-- OPEN: actual native block/field reflection intertwiner, published
-- fine Wilson positive-time support and RP, continuum OS, Clay gap.
-- Original source uses real analysis axioms; no fake --safe/Golden claim.

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

reflectFineTime : C4 → C4
reflectFineTime Torus.zeroᵢ = Torus.zeroᵢ
reflectFineTime (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
reflectFineTime (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)
reflectFineTime (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) =
  Torus.sucᵢ Torus.zeroᵢ

reflectCoarseTime : C2 → C2
reflectCoarseTime Torus.zeroᵢ = Torus.zeroᵢ
reflectCoarseTime (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ Torus.zeroᵢ

evenTime : C2 → C4
evenTime Torus.zeroᵢ = Torus.zeroᵢ
evenTime (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)

reflectFineTimeInvolution :
  (t : C4) → reflectFineTime (reflectFineTime t) ≡ t
reflectFineTimeInvolution Torus.zeroᵢ = refl
reflectFineTimeInvolution (Torus.sucᵢ Torus.zeroᵢ) = refl
reflectFineTimeInvolution (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
reflectFineTimeInvolution
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

reflectCoarseTimeInvolution :
  (t : C2) → reflectCoarseTime (reflectCoarseTime t) ≡ t
reflectCoarseTimeInvolution Torus.zeroᵢ = refl
reflectCoarseTimeInvolution (Torus.sucᵢ Torus.zeroᵢ) = refl

reflectEvenTime :
  (t : C2) →
  reflectFineTime (evenTime t) ≡ evenTime (reflectCoarseTime t)
reflectEvenTime Torus.zeroᵢ = refl
reflectEvenTime (Torus.sucᵢ Torus.zeroᵢ) = refl

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
  rewrite reflectEvenTime t = refl

reflectFineSiteInvolution :
  (site : FineSite) →
  reflectFineSite (reflectFineSite site) ≡ site
reflectFineSiteInvolution
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite reflectFineTimeInvolution t = refl

reflectCoarseSiteInvolution :
  (site : CoarseSite) →
  reflectCoarseSite (reflectCoarseSite site) ≡ site
reflectCoarseSiteInvolution
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite reflectCoarseTimeInvolution t = refl

-- Positive fine temporal link STARTS for the coarse T=0 time bond
-- (native path 0->1->2); full positive-time Wilson word proof is open.
data OriginalSelectedPositiveTimeStart : C4 → Set where
  timeBond0 : OriginalSelectedPositiveTimeStart Torus.zeroᵢ
  timeBond1 : OriginalSelectedPositiveTimeStart
    (Torus.sucᵢ Torus.zeroᵢ)

selectedFirstFineTimeBondPositive :
  OriginalSelectedPositiveTimeStart (evenTime Torus.zeroᵢ)
selectedFirstFineTimeBondPositive = timeBond0

selectedSecondFineTimeBondPositive :
  OriginalSelectedPositiveTimeStart (Torus.sucᵢ Torus.zeroᵢ)
selectedSecondFineTimeBondPositive = timeBond1

-- Universal group-valued original positive two-link path (any SU(N)
-- group supplied by the existing certified source). Not a scalar proxy.
module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where

  actualNativeTwoLink :
    Bond.PeriodicBondField 3 Value → FineSite → Torus.Axis4 → Value
  actualNativeTwoLink field site axis =
    Native.positiveHolonomy group field site axis (suc (suc zero))

  originalTwoLinkReducesToOrderedProduct :
    (field : Bond.PeriodicBondField 3 Value)
    (site : FineSite) (axis : Torus.Axis4) →
    actualNativeTwoLink field site axis ≡
    Bond.multiply group
      (field (Torus.pair site axis))
      (field (Torus.pair (Bond.positiveStep site axis) axis))
  originalTwoLinkReducesToOrderedProduct field site axis =
    cong (Bond.multiply group (field (Torus.pair site axis)))
      (Bond.identityRight group
        (field (Torus.pair (Bond.positiveStep site axis) axis)))

  reflectedOrderedTimeBlock :
    (u v : Value) →
    Bond.multiply group (Bond.inverse group v) (Bond.inverse group u)
      ≡ Bond.inverse group (Bond.multiply group u v)
  reflectedOrderedTimeBlock u v =
    sym (Bond.inverseProduct group u v)

-- Remaining exact Agda original-source weld:
-- * show original Native.fineBlockOrigin is evenCoarseOrigin;
-- * prove reflection/positive-step commutation with temporal inversion;
-- * inhabit original NativeBlockReflectsExactly for actual fine/coarse
--   field reflections, not by assuming it as an extra input;
-- * prove published Wilson half-space and reflected all-word RP.
