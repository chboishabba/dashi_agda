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


------------------------------------------------------------------------
-- W0 SOURCE GEOMETRIC WELD: native R445 <-> genuine F19 fibre pair.
--
-- Source geometry, NOT a fresh block map: for every one of 64 native
-- side-two bonds, the pair consists of its two distinct original
-- parity-selected side-four positive bonds. Recover the FIRST fine
-- holonomy from (native W, SECOND fine holonomy V) as W V^-1.
-- The normal F19 fibre coordinates therefore reconstruct exactly
-- the native R445 holonomy, pointwise on the ORIGINAL fine field.
--
-- No integration, arbitrary activity equality, gauge-fixing or
-- scale-dependent CMP119 T is smuggled into this geometry theorem.
------------------------------------------------------------------------

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  NativeLink : Set
  NativeLink = SUN.SUNMatrixElement theory

  nativeSourceGroup : Bond.ExactLinkGroup NativeLink
  nativeSourceGroup = Signed.sunExactSignedLinkGroup theory

  originalSecondFineBond :
    (site : Parity.Site2) (axis : T.Axis4) → T.PositiveBond 4
  originalSecondFineBond site axis =
    Parity.originalR445SelectedFineBond
      (T.pair site axis) (T.sucᵢ T.zeroᵢ)

  originalFirstFineBond :
    (site : Parity.Site2) (axis : T.Axis4) → T.PositiveBond 4
  originalFirstFineBond site axis =
    Parity.originalR445SelectedFineBond
      (T.pair site axis) T.zeroᵢ

  -- An actual native F19 fibre codec, not an alternative averaging.
  originalR445NativeF19RecoveredPair :
    (fine : Variable.SUNPeriodicLinks theory 3)
    (site : Parity.Site2) (axis : T.Axis4) →
    T.Product NativeLink NativeLink
  originalR445NativeF19RecoveredPair fine site axis =
    T.pair
      (SUN.sunMultiply theory
        (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
          theory fine (T.pair site axis))
        (SUN.sunInverse theory (fine (originalSecondFineBond site axis))))
      (fine (originalSecondFineBond site axis))

  -- U = (U V) V^-1, with the genuine native path and the selected
  -- source parity indices, not an equality supplied as a field.
  originalR445NativeFirstRecoveredFromF19 :
    (fine : Variable.SUNPeriodicLinks theory 3)
    (site : Parity.Site2) (axis : T.Axis4) →
    SUN.sunMultiply theory
      (SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
        theory fine (T.pair site axis))
      (SUN.sunInverse theory (fine (originalSecondFineBond site axis)))
    ≡ fine (originalFirstFineBond site axis)
  originalR445NativeFirstRecoveredFromF19 fine site axis =
    let
      first = fine (originalFirstFineBond site axis)
      second = fine (originalSecondFineBond site axis)
    in
    trans
      (cong
        (λ block → SUN.sunMultiply theory
          block (SUN.sunInverse theory second))
        (originalR445NativeBlockAgreesExplicitParity theory fine site axis))
      (trans
        (Bond.multiplyAssociative nativeSourceGroup
          first second (SUN.sunInverse theory second))
        (trans
          (cong (SUN.sunMultiply theory first)
            (Bond.inverseRight nativeSourceGroup second))
          (Bond.identityRight nativeSourceGroup first)))

  -- Inverse fibre decode: exact original two physical link values.
  originalR445NativeF19RecoveredPairIsOriginal :
    (fine : Variable.SUNPeriodicLinks theory 3)
    (site : Parity.Site2) (axis : T.Axis4) →
    originalR445NativeF19RecoveredPair fine site axis
    ≡ T.pair
        (fine (originalFirstFineBond site axis))
        (fine (originalSecondFineBond site axis))
  originalR445NativeF19RecoveredPairIsOriginal fine site axis =
    cong₂ T.pair
      (originalR445NativeFirstRecoveredFromF19 fine site axis)
      refl

  -- Forward fibre encode: F19's U V = W on the genuine native R445
  -- blocked bond. This closes the source-selected local geometric
  -- triangle in BOTH directions, not the full CMP119 T integral.
  originalR445F19RecoveredPairBlockIsNative :
    (fine : Variable.SUNPeriodicLinks theory 3)
    (site : Parity.Site2) (axis : T.Axis4) →
    SUN.sunMultiply theory
      (T.first (originalR445NativeF19RecoveredPair fine site axis))
      (T.second (originalR445NativeF19RecoveredPair fine site axis))
    ≡ SUNBlock.nativeSUNBlockLinks {m = 1} {l = 1}
        theory fine (T.pair site axis)
  originalR445F19RecoveredPairBlockIsNative fine site axis =
    trans
      (cong₂ (SUN.sunMultiply theory)
        (originalR445NativeFirstRecoveredFromF19 fine site axis)
        refl)
      (sym (originalR445NativeBlockAgreesExplicitParity
        theory fine site axis))
