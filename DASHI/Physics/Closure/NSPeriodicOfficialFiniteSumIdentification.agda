module DASHI.Physics.Closure.NSPeriodicOfficialFiniteSumIdentification where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSIntegerFourierLattice using
  (FourierMode)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One owner for finite Fourier enumeration and official norm definitions.
--
-- The official cutoff L², homogeneous-H¹ and shell norms are defined from the
-- same literal duplicate-free mode list.  Consequently the fold-identification
-- theorems are definitional equalities; completeness, duplicate-freeness,
-- reality compatibility and zero-mode handling cannot be supplied by unrelated
-- packages.
------------------------------------------------------------------------

sumBy :
  ∀ {A : AbsorptionArithmetic} {Item : Set} →
  (Item → Scalar A) →
  List Item →
  Scalar A
sumBy {A = A} weight [] = zero A
sumBy {A = A} weight (item ∷ items) =
  _+_ A (weight item) (sumBy weight items)

record ConcreteFiniteFourierNormCarrier
    (A : AbsorptionArithmetic) : Set₁ where
  field
    cutoffModes : Nat → List FourierMode
    InCutoff : Nat → FourierMode → Set
    Listed : FourierMode → List FourierMode → Set
    DuplicateFree : List FourierMode → Set

    cutoffModeEnumerationComplete : ∀ N k →
      InCutoff N k → Listed k (cutoffModes N)

    cutoffModeEnumerationSound : ∀ N k →
      Listed k (cutoffModes N) → InCutoff N k

    cutoffModeEnumerationNoDuplicates : ∀ N →
      DuplicateFree (cutoffModes N)

    l2ModeWeight h1ModeWeight :
      Nat → FourierMode → Scalar A

    shellModeWeight :
      Nat → Nat → FourierMode → Scalar A

    RealityCompatible : Set
    realityCompatible : RealityCompatible

    ZeroModeHandledExactlyOnce : Nat → Set
    zeroModeHandledExactlyOnce : ∀ N →
      ZeroModeHandledExactlyOnce N

open ConcreteFiniteFourierNormCarrier public

officialL2Squared :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Scalar A
officialL2Squared C N =
  sumBy (l2ModeWeight C N) (cutoffModes C N)

officialHomogeneousH1Squared :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Scalar A
officialHomogeneousH1Squared C N =
  sumBy (h1ModeWeight C N) (cutoffModes C N)

officialShellL2Squared :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Nat → Scalar A
officialShellL2Squared C N shell =
  sumBy (shellModeWeight C N shell) (cutoffModes C N)

literalL2Fold :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Scalar A
literalL2Fold = officialL2Squared

literalH1Fold :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Scalar A
literalH1Fold = officialHomogeneousH1Squared

literalShellFold :
  ∀ {A : AbsorptionArithmetic} →
  ConcreteFiniteFourierNormCarrier A →
  Nat → Nat → Scalar A
literalShellFold = officialShellL2Squared

literalL2FoldIsOfficialL2 :
  ∀ {A : AbsorptionArithmetic}
    (C : ConcreteFiniteFourierNormCarrier A) N →
  literalL2Fold C N ≡ officialL2Squared C N
literalL2FoldIsOfficialL2 C N = refl

literalH1FoldIsOfficialH1 :
  ∀ {A : AbsorptionArithmetic}
    (C : ConcreteFiniteFourierNormCarrier A) N →
  literalH1Fold C N ≡ officialHomogeneousH1Squared C N
literalH1FoldIsOfficialH1 C N = refl

literalShellFoldIsOfficialShellNorm :
  ∀ {A : AbsorptionArithmetic}
    (C : ConcreteFiniteFourierNormCarrier A) N shell →
  literalShellFold C N shell ≡ officialShellL2Squared C N shell
literalShellFoldIsOfficialShellNorm C N shell = refl

record OfficialFiniteSumIdentification
    {A : AbsorptionArithmetic}
    (C : ConcreteFiniteFourierNormCarrier A)
    (N : Nat) : Set where
  field
    enumeration-is-duplicate-free :
      DuplicateFree C (cutoffModes C N)

    zero-mode-is-handled-once :
      ZeroModeHandledExactlyOnce C N

    reality-is-compatible : RealityCompatible C

    l2-identification :
      literalL2Fold C N ≡ officialL2Squared C N

    h1-identification :
      literalH1Fold C N ≡ officialHomogeneousH1Squared C N

    shell-identification : ∀ shell →
      literalShellFold C N shell ≡ officialShellL2Squared C N shell

open OfficialFiniteSumIdentification public

officialFiniteSumIdentification :
  ∀ {A : AbsorptionArithmetic}
    (C : ConcreteFiniteFourierNormCarrier A) N →
  OfficialFiniteSumIdentification C N
officialFiniteSumIdentification C N = record
  { enumeration-is-duplicate-free = cutoffModeEnumerationNoDuplicates C N
  ; zero-mode-is-handled-once = zeroModeHandledExactlyOnce C N
  ; reality-is-compatible = realityCompatible C
  ; l2-identification = literalL2FoldIsOfficialL2 C N
  ; h1-identification = literalH1FoldIsOfficialH1 C N
  ; shell-identification = literalShellFoldIsOfficialShellNorm C N
  }

------------------------------------------------------------------------
-- Status: once the literal enumerator is supplied, no second norm owner or
-- conjugate-symmetry convention can enter the official estimates.
------------------------------------------------------------------------

officialFiniteSumIdentificationLevel : ProofLevel
officialFiniteSumIdentificationLevel = machineChecked
