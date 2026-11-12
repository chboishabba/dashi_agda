module DASHI.Physics.YangMills.YMClayR445OriginalNativeParityPairWeldExact where

------------------------------------------------------------------------
-- P0.A/C ORIGINAL R445 SOURCE WELD, not a second blocking model.
--
-- The already proved original CyclicIndex/Fin source codec and
-- Balaban fineBlockOrigin at m=l=1 are tied to the same explicit
-- parity indices that have a constructive inverse in
-- YMClayR445OriginalAxialBondParityInjectiveExact.
--
-- Two finite computation obligations are paid by exhaustive
-- original CyclicIndex cases (16 coarse sites for the native origin,
-- 8 source axis/parity cases for one selected axial step).
-- Original native blocked holonomy is then the exact product of
-- the two globally distinct selected side-four positive bonds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as Parity
import DASHI.Physics.YangMills.YMClayR445NativePairHolonomyIdentityExact as Native
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Signed
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as SUNBlock

originalR445EvenFineSite : Parity.Site2 → Parity.Site4
originalR445EvenFineSite
  (T.pair (T.pair a b) (T.pair c d)) =
  T.pair (T.pair (Parity.even a) (Parity.even b))
    (T.pair (Parity.even c) (Parity.even d))

originalR445NativeOriginIsEvenSite :
  (site : Parity.Site2) →
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  Block.fineBlockOrigin {m = 1} {l = 1} group site
  ≡ originalR445EvenFineSite site

originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ T.zeroᵢ) (T.pair T.zeroᵢ T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ T.zeroᵢ) (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ T.zeroᵢ) (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ T.zeroᵢ) (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ)) (T.pair T.zeroᵢ T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ)) (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ)) (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ)) (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ) (T.pair T.zeroᵢ T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ) (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ) (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ) (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ)) (T.pair T.zeroᵢ T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ)) (T.pair T.zeroᵢ (T.sucᵢ T.zeroᵢ))) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ)) (T.pair (T.sucᵢ T.zeroᵢ) T.zeroᵢ)) group = refl
originalR445NativeOriginIsEvenSite (T.pair (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ)) (T.pair (T.sucᵢ T.zeroᵢ) (T.sucᵢ T.zeroᵢ))) group = refl

-- The original fine positive step uses exactly the same cyclic
-- successor as the native R445 signed/positive Wilson path.
originalR445EvenSiteOneStepIsOddPhase :
  (site : Parity.Site2) (axis : T.Axis4) →
  T.pair
    (Bond.positiveStep (originalR445EvenFineSite site) axis)
    axis
  ≡ Parity.originalR445SelectedFineBond
      (T.pair site axis) (T.sucᵢ T.zeroᵢ)
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair T.zeroᵢ b) (T.pair c d)) T.zeroᵢ = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair (T.sucᵢ T.zeroᵢ) b) (T.pair c d)) T.zeroᵢ = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a T.zeroᵢ) (T.pair c d)) (T.sucᵢ T.zeroᵢ) = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a (T.sucᵢ T.zeroᵢ)) (T.pair c d)) (T.sucᵢ T.zeroᵢ) = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a b) (T.pair T.zeroᵢ d)) (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a b) (T.pair (T.sucᵢ T.zeroᵢ) d)) (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a b) (T.pair c T.zeroᵢ)) (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = refl
originalR445EvenSiteOneStepIsOddPhase
  (T.pair (T.pair a b) (T.pair c (T.sucᵢ T.zeroᵢ))) (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = refl

originalR445NativeFirstBondIsParity :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  (site : Parity.Site2) (axis : T.Axis4) →
  T.pair (Block.fineBlockOrigin {m = 1} {l = 1} group site) axis
  ≡ Parity.originalR445SelectedFineBond
      (T.pair site axis) T.zeroᵢ
originalR445NativeFirstBondIsParity group site axis =
  trans
    (cong (λ x → T.pair x axis)
      (originalR445NativeOriginIsEvenSite site group))
    (originalR445EvenSiteFirstBondIsParity site axis)

originalR445EvenSiteFirstBondIsParity :
  (site : Parity.Site2) (axis : T.Axis4) →
  T.pair (originalR445EvenFineSite site) axis
  ≡ Parity.originalR445SelectedFineBond
      (T.pair site axis) T.zeroᵢ
originalR445EvenSiteFirstBondIsParity
  (T.pair (T.pair a b) (T.pair c d)) T.zeroᵢ = refl
originalR445EvenSiteFirstBondIsParity
  (T.pair (T.pair a b) (T.pair c d))
  (T.sucᵢ T.zeroᵢ) = refl
originalR445EvenSiteFirstBondIsParity
  (T.pair (T.pair a b) (T.pair c d))
  (T.sucᵢ (T.sucᵢ T.zeroᵢ)) = refl
originalR445EvenSiteFirstBondIsParity
  (T.pair (T.pair a b) (T.pair c d))
  (T.sucᵢ (T.sucᵢ (T.sucᵢ T.zeroᵢ))) = refl

originalR445NativeSecondBondIsParity :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  (site : Parity.Site2) (axis : T.Axis4) →
  T.pair
    (Bond.positiveStep
      (Block.fineBlockOrigin {m = 1} {l = 1} group site)
      axis)
    axis
  ≡ Parity.originalR445SelectedFineBond
      (T.pair site axis) (T.sucᵢ T.zeroᵢ)
originalR445NativeSecondBondIsParity group site axis =
  trans
    (cong (λ origin → T.pair (Bond.positiveStep origin axis) axis)
      (originalR445NativeOriginIsEvenSite site group))
    (originalR445EvenSiteOneStepIsOddPhase site axis)

-- The SAME source literal R445 blocked link is obtained from the
-- parity-coded pair, and injectivity is already source-proved.
originalR445NativeBlockAgreesExplicitParity :
  ∀ {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (fine : Variable.SUNPeriodicLinks theory 3)
    (site : Parity.Site2) (axis : T.Axis4) →
  SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
    theory fine (T.pair site axis)
  ≡ SUN.sunMultiply theory
      (fine (Parity.originalR445SelectedFineBond
        (T.pair site axis) T.zeroᵢ))
      (fine (Parity.originalR445SelectedFineBond
        (T.pair site axis) (T.sucᵢ T.zeroᵢ)))
originalR445NativeBlockAgreesExplicitParity theory fine site axis =
  trans
    (Native.originalR445NativeBlockAgreesPairedCodec
      theory fine (T.pair site axis))
    (cong₂ (SUN.sunMultiply theory)
      (cong fine
        (originalR445NativeFirstBondIsParity
          (Signed.sunExactSignedLinkGroup theory) site axis))
      (cong fine
        (originalR445NativeSecondBondIsParity
          (Signed.sunExactSignedLinkGroup theory) site axis)))
