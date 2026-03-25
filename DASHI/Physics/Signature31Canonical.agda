module DASHI.Physics.Signature31Canonical where

-- Canonical signature seam:
-- theorem-primary route is intrinsic-core axioms -> causal Lorentz forcing.
-- Shift/profile witnesses remain secondary certification data.

open import DASHI.Geometry.ConeTimeIsotropy as CTI
open import DASHI.Geometry.SignatureUniqueness31 as SU using (Signature31Theorem)
open import DASHI.Geometry.Signature31FromIntrinsicShellForcing as S31ISF
open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import DASHI.Physics.Signature31IntrinsicShiftInstance as S31I
import DASHI.Physics.Signature31IntrinsicSyntheticInstance as S31S
import DASHI.Physics.Signature31IntrinsicRootSystemB4Instance as S31B4

open S31ISF public
  using
    ( IntrinsicSignatureCoreAxioms
    ; IntrinsicProfileWitness
    ; profileEqFromIntrinsic
    ; signature31-theoremFromIntrinsic
    ; profileSignatureLawFromIntrinsic
    ; signature31FromIntrinsic
    ; lorentzLockFromIntrinsic
    )

data IntrinsicCoreProviderSource : Set where
  shiftOrbitProfileSource : IntrinsicCoreProviderSource
  syntheticOneMinusSource : IntrinsicCoreProviderSource
  rootSystemB4Source : IntrinsicCoreProviderSource

record IntrinsicCoreProvider : Setω where
  field
    providerSource : IntrinsicCoreProviderSource
    providerLabel : String
    coreAxioms : IntrinsicSignatureCoreAxioms

open IntrinsicCoreProvider public

signature31-theoremFromProvider :
  IntrinsicCoreProvider → Signature31Theorem
signature31-theoremFromProvider p =
  signature31-theoremFromIntrinsic (coreAxioms p)

signature31FromProvider :
  IntrinsicCoreProvider → CTI.Signature
signature31FromProvider p =
  signature31FromIntrinsic (coreAxioms p)

shiftCoreProvider : IntrinsicCoreProvider
shiftCoreProvider =
  record
    { providerSource = shiftOrbitProfileSource
    ; providerLabel = "shift-intrinsic-core"
    ; coreAxioms = S31I.shiftIntrinsicCoreAxioms
    }

syntheticCoreProvider : IntrinsicCoreProvider
syntheticCoreProvider =
  record
    { providerSource = syntheticOneMinusSource
    ; providerLabel = S31S.syntheticLabel
    ; coreAxioms = S31S.syntheticIntrinsicCoreAxioms
    }

b4CoreProvider : IntrinsicCoreProvider
b4CoreProvider =
  record
    { providerSource = rootSystemB4Source
    ; providerLabel = S31B4.b4Label
    ; coreAxioms = S31B4.b4IntrinsicCoreAxioms
    }

canonicalCoreAxioms : IntrinsicSignatureCoreAxioms
canonicalCoreAxioms = coreAxioms shiftCoreProvider

canonicalProfileWitness : IntrinsicProfileWitness canonicalCoreAxioms
canonicalProfileWitness = S31I.shiftProfileWitness

signature31-theorem : Signature31Theorem
signature31-theorem =
  signature31-theoremFromProvider shiftCoreProvider

signature31 : CTI.Signature
signature31 = signature31FromProvider shiftCoreProvider

signature31FromProviderDerivedFromCausal :
  (provider : IntrinsicCoreProvider) →
  signature31FromProvider provider ≡ CTI.sig31
signature31FromProviderDerivedFromCausal provider =
  S31ISF.signature31FromIntrinsicMatchesCTI
    (IntrinsicCoreProvider.coreAxioms provider)

canonicalSignatureIsCTI :
  signature31 ≡ CTI.sig31
canonicalSignatureIsCTI =
  sym (signature31FromProviderDerivedFromCausal shiftCoreProvider)

syntheticSignature31-theorem : Signature31Theorem
syntheticSignature31-theorem =
  signature31-theoremFromProvider syntheticCoreProvider

syntheticSignature31 : CTI.Signature
syntheticSignature31 = signature31FromProvider syntheticCoreProvider

syntheticSignatureMatchesCanonical :
  signature31FromProvider syntheticCoreProvider
  ≡ signature31FromProvider shiftCoreProvider
syntheticSignatureMatchesCanonical = refl
