module DASHI.Codec.TriadicPAdicCodec369Bridge where

-- Constructive cross-pollination between the codec bridge and existing DASHI
-- carrier spines.
--
-- A codec trit kernel is read as a depth-indexed 369 address:
--   neg -> 3, zer -> 6, pos -> 9.
-- Under this reading trit inversion is exactly the 369 polarity action
--   3 <-> 9, 6 -> 6,
-- and the codec's 9-lift becomes prefix extension by two 369 digits.
-- This gives the residual-kernel lane the repo's existing prefix ultrametric
-- without claiming an analytic 3-adic norm.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_)
open import Data.Vec using ([]; _∷_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Geometry.SSP369Ultrametric as Geo
import DASHI.MDL.MDLLyapunov as MDL

------------------------------------------------------------------------
-- Trit kernels as 369 addresses
------------------------------------------------------------------------

trit→369 : Trit → Geo.Digit369
trit→369 neg = Geo.digit3
trit→369 zer = Geo.digit6
trit→369 pos = Geo.digit9

invert369 : Geo.Digit369 → Geo.Digit369
invert369 Geo.digit3 = Geo.digit9
invert369 Geo.digit6 = Geo.digit6
invert369 Geo.digit9 = Geo.digit3

trit→369-inversion :
  (t : Trit) →
  trit→369 (inv t) ≡ invert369 (trit→369 t)
trit→369-inversion neg = refl
trit→369-inversion zer = refl
trit→369-inversion pos = refl

kernel→369 :
  {d : Nat} →
  Codec.Kernel d →
  Geo.Address d
kernel→369 Codec.[]ᵥ = []
kernel→369 (x Codec.∷ᵥ xs) = trit→369 x ∷ kernel→369 xs

map369 :
  {d : Nat} →
  (Geo.Digit369 → Geo.Digit369) →
  Geo.Address d →
  Geo.Address d
map369 f [] = []
map369 f (x ∷ xs) = f x ∷ map369 f xs

kernel→369-inversion-compatible :
  {d : Nat} →
  (u : Codec.Kernel d) →
  kernel→369 (Codec.invertKernel u)
  ≡
  map369 invert369 (kernel→369 u)
kernel→369-inversion-compatible Codec.[]ᵥ = refl
kernel→369-inversion-compatible (x Codec.∷ᵥ xs)
  rewrite trit→369-inversion x
        | kernel→369-inversion-compatible xs = refl

kernel369-self-prefix :
  {d : Nat} →
  (u : Codec.Kernel d) →
  Geo.PrefixMatch d (kernel→369 u) (kernel→369 u)
kernel369-self-prefix u = Geo.prefixMatch-refl (kernel→369 u)

kernel369-self-distance-zero :
  {d : Nat} →
  (u : Codec.Kernel d) →
  Geo.distance (kernel→369 u) (kernel→369 u) ≡ zero
kernel369-self-distance-zero u = Geo.distance-self-zero (kernel→369 u)

------------------------------------------------------------------------
-- The codec 9-lift is two-digit 369 prefix extension
------------------------------------------------------------------------

sheet→369-prefix :
  Codec.Sheet9 →
  Geo.Address (suc (suc zero))
sheet→369-prefix (a Codec.∷ᵥ b Codec.∷ᵥ Codec.[]ᵥ) =
  trit→369 a ∷ trit→369 b ∷ []

prefixSheet369 :
  {d : Nat} →
  Geo.Address (suc (suc zero)) →
  Geo.Address d →
  Geo.Address (suc (suc d))
prefixSheet369 (a ∷ b ∷ []) tail = a ∷ b ∷ tail

lift9→369-compatible :
  {d : Nat} →
  (s : Codec.Sheet9) →
  (u : Codec.Kernel d) →
  kernel→369 (Codec.lift9 s u)
  ≡
  prefixSheet369 (sheet→369-prefix s) (kernel→369 u)
lift9→369-compatible (a Codec.∷ᵥ b Codec.∷ᵥ Codec.[]ᵥ) u = refl

record Codec369UltrametricReceipt {d : Nat} (u : Codec.Kernel d) : Set where
  field
    address : Geo.Address d
    addressIsKernelImage : address ≡ kernel→369 u
    selfPrefix : Geo.PrefixMatch d address address
    selfDistanceZero : Geo.distance address address ≡ zero

canonicalCodec369UltrametricReceipt :
  {d : Nat} →
  (u : Codec.Kernel d) →
  Codec369UltrametricReceipt u
canonicalCodec369UltrametricReceipt u =
  record
    { address = kernel→369 u
    ; addressIsKernelImage = refl
    ; selfPrefix = kernel369-self-prefix u
    ; selfDistanceZero = kernel369-self-distance-zero u
    }

------------------------------------------------------------------------
-- Direct adapter into the existing canonical MDL functional
------------------------------------------------------------------------

codecMDLFunctional :
  {Chart : Set} →
  (model residual : Chart → Nat) →
  MDL.MDLFunctional Chart
codecMDLFunctional model residual =
  record
    { model = model
    ; residual = residual
    ; mdl = λ chart → model chart + residual chart
    ; mdl≡ = λ chart → refl
    }

record NatMDLSelectionAdapter : Set₁ where
  field
    Chart : Set
    modelBits : Chart → Nat
    residualBits : Chart → Nat
    selected : Chart
    selectedMinimal :
      (candidate : Chart) →
      modelBits selected + residualBits selected
      ≤
      modelBits candidate + residualBits candidate

  functional : MDL.MDLFunctional Chart
  functional = codecMDLFunctional modelBits residualBits

  codecSelection : Codec.MDLChartSelection
  codecSelection =
    record
      { Chart = Chart
      ; Bits = Nat
      ; descriptionLength = MDL.MDLFunctional.mdl functional
      ; noLongerThan = _≤_
      ; selected = selected
      ; selectedMinimal = selectedMinimal
      }

------------------------------------------------------------------------
-- Boundary: exact finite bridge, not analytic/empirical promotion
------------------------------------------------------------------------

record Codec369CrossPollinationBoundary : Set where
  constructor boundary
  field
    tritKernelTo369AddressChecked : Agda.Builtin.Bool.Bool
    inversionAs369PolarityChecked : Agda.Builtin.Bool.Bool
    lift9AsTwoDigitPrefixChecked : Agda.Builtin.Bool.Bool
    prefixUltrametricReused : Agda.Builtin.Bool.Bool
    canonicalMDLFunctionalReused : Agda.Builtin.Bool.Bool
    analyticThreeAdicNormProvedHere : Agda.Builtin.Bool.Bool
    entropyRateTheoremProvedHere : Agda.Builtin.Bool.Bool
    physicalSpeedupProvedHere : Agda.Builtin.Bool.Bool

canonicalCrossPollinationBoundary : Codec369CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  boundary
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.false
    Agda.Builtin.Bool.false
    Agda.Builtin.Bool.false
