module DASHI.Codec.TriadicPAdicCodec369BridgeRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using ([]; _∷_)

open import DASHI.Algebra.Trit using (neg; zer; pos)
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Codec.TriadicPAdicCodec369Bridge as Bridge
import DASHI.Geometry.SSP369Ultrametric as Geo

three : Nat
three = suc (suc (suc zero))

canonicalKernel : Codec.Kernel three
canonicalKernel = neg Codec.∷ᵥ zer Codec.∷ᵥ pos Codec.∷ᵥ Codec.[]ᵥ

canonicalAddress : Geo.Address three
canonicalAddress = Geo.digit3 ∷ Geo.digit6 ∷ Geo.digit9 ∷ []

canonicalKernelMapsTo369 :
  Bridge.kernel→369 canonicalKernel ≡ canonicalAddress
canonicalKernelMapsTo369 = refl

canonicalInvertedKernelMapsTo963 :
  Bridge.kernel→369 (Codec.invertKernel canonicalKernel)
  ≡
  Geo.digit9 ∷ Geo.digit6 ∷ Geo.digit3 ∷ []
canonicalInvertedKernelMapsTo963 = refl

canonicalKernelSelfDistanceZero :
  Geo.distance (Bridge.kernel→369 canonicalKernel)
               (Bridge.kernel→369 canonicalKernel)
  ≡ zero
canonicalKernelSelfDistanceZero =
  Bridge.kernel369-self-distance-zero canonicalKernel

canonicalSheet : Codec.Sheet9
canonicalSheet = Codec.sheet neg pos

canonicalLiftCompatibility :
  Bridge.kernel→369 (Codec.lift9 canonicalSheet canonicalKernel)
  ≡
  Bridge.prefixSheet369
    (Bridge.sheet→369-prefix canonicalSheet)
    (Bridge.kernel→369 canonicalKernel)
canonicalLiftCompatibility =
  Bridge.lift9→369-compatible canonicalSheet canonicalKernel

crossPollinationPositiveChecks :
  Bridge.Codec369CrossPollinationBoundary.tritKernelTo369AddressChecked
    Bridge.canonicalCrossPollinationBoundary
  ≡ true
crossPollinationPositiveChecks = refl

crossPollinationAnalyticBoundaryClosed :
  Bridge.Codec369CrossPollinationBoundary.analyticThreeAdicNormProvedHere
    Bridge.canonicalCrossPollinationBoundary
  ≡ false
crossPollinationAnalyticBoundaryClosed = refl

crossPollinationRateBoundaryClosed :
  Bridge.Codec369CrossPollinationBoundary.entropyRateTheoremProvedHere
    Bridge.canonicalCrossPollinationBoundary
  ≡ false
crossPollinationRateBoundaryClosed = refl
