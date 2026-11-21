module DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact where

-- Original 4D site-coordinate reflection, without replacing the existing\n-- YMClayNativeR445TemporalReversalExact non-Abelian two-link theorem.
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


-- Original native non-Abelian two-link reversal and Fin-combine coordinate
-- producers are already on master. The remaining selected original-field
-- reflection requires a site-index commuting theorem; see the separate
-- source-owned word bridge. No false claim of Agda kernel acceptance.

------------------------------------------------------------------------
-- Exact C4/C2 TIME-TRANSLATION SQUARE on the SELECTED native EVEN sites.
-- For the original 2-link block, ONE coarse time step corresponds to
-- TWO original fine time steps. A single fine step is NOT equivariant.
-- No continuum/unbounded physical time is inferred from finite C2.
------------------------------------------------------------------------

shiftFineTimeByTwo : C4 → C4
shiftFineTimeByTwo Torus.zeroᵢ =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)
shiftFineTimeByTwo (Torus.sucᵢ Torus.zeroᵢ) =
  Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))
shiftFineTimeByTwo (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.zeroᵢ
shiftFineTimeByTwo
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) =
  Torus.sucᵢ Torus.zeroᵢ

shiftCoarseTimeByOne : C2 → C2
shiftCoarseTimeByOne Torus.zeroᵢ = Torus.sucᵢ Torus.zeroᵢ
shiftCoarseTimeByOne (Torus.sucᵢ Torus.zeroᵢ) = Torus.zeroᵢ

shiftFineSiteByTwo : FineSite → FineSite
shiftFineSiteByTwo
  (Torus.pair (Torus.pair t x) (Torus.pair y z)) =
  Torus.pair
    (Torus.pair (shiftFineTimeByTwo t) x)
    (Torus.pair y z)

shiftCoarseSiteByOne : CoarseSite → CoarseSite
shiftCoarseSiteByOne
  (Torus.pair (Torus.pair t x) (Torus.pair y z)) =
  Torus.pair
    (Torus.pair (shiftCoarseTimeByOne t) x)
    (Torus.pair y z)

selectedEvenTimeTranslationCommutes :
  (time : C2) →
  shiftFineTimeByTwo (evenTime time) ≡
  evenTime (shiftCoarseTimeByOne time)
selectedEvenTimeTranslationCommutes Torus.zeroᵢ = refl
selectedEvenTimeTranslationCommutes
  (Torus.sucᵢ Torus.zeroᵢ) = refl

selectedNativeSiteTimeSquare :
  (site : CoarseSite) →
  shiftFineSiteByTwo (evenCoarseOrigin site) ≡
  evenCoarseOrigin (shiftCoarseSiteByOne site)
selectedNativeSiteTimeSquare
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite selectedEvenTimeTranslationCommutes t = refl

selectedFineReflectShiftDihedral :
  (time : C4) →
  reflectFineTime (shiftFineTimeByTwo time) ≡
  shiftFineTimeByTwo (reflectFineTime time)
selectedFineReflectShiftDihedral Torus.zeroᵢ = refl
selectedFineReflectShiftDihedral
  (Torus.sucᵢ Torus.zeroᵢ) = refl
selectedFineReflectShiftDihedral
  (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) = refl
selectedFineReflectShiftDihedral
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) = refl

selectedFineSiteReflectShiftDihedral :
  (site : FineSite) →
  reflectFineSite (shiftFineSiteByTwo site) ≡
  shiftFineSiteByTwo (reflectFineSite site)
selectedFineSiteReflectShiftDihedral
  (Torus.pair (Torus.pair t x) (Torus.pair y z))
  rewrite selectedFineReflectShiftDihedral t = refl

selectedCoarseSiteShiftHasPeriodTwo :
  (site : CoarseSite) →
  shiftCoarseSiteByOne (shiftCoarseSiteByOne site) ≡ site
selectedCoarseSiteShiftHasPeriodTwo
  (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) = refl
selectedCoarseSiteShiftHasPeriodTwo
  (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x)
              (Torus.pair y z)) = refl

-- Explicit unclosed seam: establish evenCoarseOrigin above equals
-- source-original Native.fineBlockOrigin on all 16 coarse native sites,
-- then prove the SAME translated ordered link product intertwines
-- original nativeSUNBlockLinks, not just these coordinate constructors.
