module DASHI.Physics.Closure.NSPeriodicFarLowEnergyPairingCancellation where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Periodic transport cancellation at the exact energy pairing.
--
-- The mixed integration-by-parts identity is the primitive analytic law:
--
--   <a · ∇u , v> + <a · ∇v , u> = 0        when div a = 0.
--
-- Over a characteristic-zero scalar carrier, the self-tested case follows by
-- taking u=v and cancelling the factor two.  The official Wall-I application
-- therefore has a visible same-shell obligation; no theorem below claims that
-- a mixed test field vanishes termwise.
------------------------------------------------------------------------

record PeriodicTransportEnergyStructure
    {ℓ : Level}
    (Field Scalar : Set ℓ) : Set (lsuc ℓ) where
  field
    scalarZero : Scalar
    scalarAdd : Scalar → Scalar → Scalar

    transport : Field → Field → Field
    pairing : Field → Field → Scalar
    DivergenceFree : Field → Set ℓ

    transportSkew : ∀ a u v →
      DivergenceFree a →
      scalarAdd
        (pairing (transport a u) v)
        (pairing (transport a v) u)
      ≡ scalarZero

    doubleZeroImpliesZero : ∀ x →
      scalarAdd x x ≡ scalarZero →
      x ≡ scalarZero

open PeriodicTransportEnergyStructure public

homogeneousTransportCancellation :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (S : PeriodicTransportEnergyStructure Field Scalar) →
  ∀ a w → DivergenceFree S a →
  pairing S (transport S a w) w ≡ scalarZero S
homogeneousTransportCancellation S a w divFree =
  doubleZeroImpliesZero S
    (pairing S (transport S a w) w)
    (transportSkew S a w w divFree)

mixedTransportTermsAreSkew :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (S : PeriodicTransportEnergyStructure Field Scalar) →
  ∀ a u v → DivergenceFree S a →
  scalarAdd S
    (pairing S (transport S a u) v)
    (pairing S (transport S a v) u)
  ≡ scalarZero S
mixedTransportTermsAreSkew S = transportSkew S

------------------------------------------------------------------------
-- The official energy lane may use the cancellation only after identifying
-- the advected shell with the tested shell.
------------------------------------------------------------------------

record OfficialSelfTestPairing
    {ℓ : Level}
    (Field : Set ℓ) : Set ℓ where
  field
    advectedShell : Field
    testedShell : Field
    advectedIsTested : advectedShell ≡ testedShell

open OfficialSelfTestPairing public

officialPrincipalTermCancels :
  ∀ {ℓ} {Field Scalar : Set ℓ} →
  (S : PeriodicTransportEnergyStructure Field Scalar) →
  ∀ a → (P : OfficialSelfTestPairing Field) →
  DivergenceFree S a →
  pairing S (transport S a (advectedShell P)) (testedShell P)
  ≡ scalarZero S
officialPrincipalTermCancels S a P divFree =
  subst
    (λ tested →
      pairing S (transport S a (advectedShell P)) tested
      ≡ scalarZero S)
    (advectedIsTested P)
    (homogeneousTransportCancellation S a (advectedShell P) divFree)

------------------------------------------------------------------------
-- Proof boundary.
--
-- The derivation from skewness to self-cancellation is checked locally.  The
-- periodic integration-by-parts theorem and characteristic-zero scalar law are
-- standard analytic/algebraic authorities until instantiated on the official
-- concrete carrier.
------------------------------------------------------------------------

farLowEnergyPairingCancellationLevel : ProofLevel
farLowEnergyPairingCancellationLevel = machineChecked

periodicTransportSkewAuthorityLevel : ProofLevel
periodicTransportSkewAuthorityLevel = standardImported

characteristicZeroDoubleCancellationLevel : ProofLevel
characteristicZeroDoubleCancellationLevel = standardImported

officialFarLowSelfTestIdentificationLevel : ProofLevel
officialFarLowSelfTestIdentificationLevel = conditional
