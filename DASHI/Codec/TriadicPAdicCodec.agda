module DASHI.Codec.TriadicPAdicCodec where

-- Typed bridge for the triadic/p-adic residual codec.
--
-- This module deliberately separates:
--   * constructive finite carrier and fold facts;
--   * abstract codec contracts needed for lossless reconstruction; and
--   * empirical / asymptotic claims which remain receipt-gated.
--
-- Existing repo anchors:
--   DASHI.Algebra.Trit
--   DASHI.Foundations.SurrealCompactificationBalancedTernaryEmbedding
--   DASHI.MDL.MDLLyapunov
--   DASHI.Physics.Closure.W9MDLTerminationSeamRoute

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)
import DASHI.Foundations.SurrealCompactificationBalancedTernaryEmbedding as BalancedEmbedding
import DASHI.MDL.MDLLyapunov as ExistingMDL
import DASHI.Physics.Closure.W9MDLTerminationSeamRoute as W9MDL

------------------------------------------------------------------------
-- Finite triadic carriers: kernels and sheets
------------------------------------------------------------------------

data Vec {ℓ : Level} (A : Set ℓ) : Nat → Set ℓ where
  []ᵥ  : Vec A zero
  _∷ᵥ_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _∷ᵥ_

Kernel : Nat → Set
Kernel d = Vec Trit d

Sheet9 : Set
Sheet9 = Kernel (suc (suc zero))

sheet : Trit → Trit → Sheet9
sheet a b = a ∷ᵥ b ∷ᵥ []ᵥ

lift9 : {d : Nat} → Sheet9 → Kernel d → Kernel (suc (suc d))
lift9 (a ∷ᵥ b ∷ᵥ []ᵥ) u = a ∷ᵥ b ∷ᵥ u

lift9-shape :
  {d : Nat} →
  (a b : Trit) →
  (u : Kernel d) →
  lift9 (sheet a b) u ≡ a ∷ᵥ b ∷ᵥ u
lift9-shape a b u = refl

mapKernel : {d : Nat} → (Trit → Trit) → Kernel d → Kernel d
mapKernel f []ᵥ = []ᵥ
mapKernel f (x ∷ᵥ xs) = f x ∷ᵥ mapKernel f xs

invertKernel : {d : Nat} → Kernel d → Kernel d
invertKernel = mapKernel inv

mapKernel-compose :
  {d : Nat} →
  (f g : Trit → Trit) →
  (u : Kernel d) →
  mapKernel f (mapKernel g u) ≡ mapKernel (λ x → f (g x)) u
mapKernel-compose f g []ᵥ = refl
mapKernel-compose f g (x ∷ᵥ xs)
  rewrite mapKernel-compose f g xs = refl

invertKernel-invol :
  {d : Nat} →
  (u : Kernel d) →
  invertKernel (invertKernel u) ≡ u
invertKernel-invol []ᵥ = refl
invertKernel-invol (x ∷ᵥ xs)
  rewrite inv-invol x
        | invertKernel-invol xs = refl

lift9-inversion-compatible :
  {d : Nat} →
  (s : Sheet9) →
  (u : Kernel d) →
  invertKernel (lift9 s u)
  ≡
  lift9 (invertKernel s) (invertKernel u)
lift9-inversion-compatible (a ∷ᵥ b ∷ᵥ []ᵥ) u = refl

------------------------------------------------------------------------
-- Exact support/sign factorisation of one trit
------------------------------------------------------------------------

data Sign : Set where
  minus : Sign
  plus  : Sign

data FoldedTrit : Set where
  zeroFold : FoldedTrit
  signed   : Sign → FoldedTrit

foldTrit : Trit → FoldedTrit
foldTrit neg = signed minus
foldTrit zer = zeroFold
foldTrit pos = signed plus

unfoldTrit : FoldedTrit → Trit
unfoldTrit zeroFold = zer
unfoldTrit (signed minus) = neg
unfoldTrit (signed plus) = pos

unfold-fold : (t : Trit) → unfoldTrit (foldTrit t) ≡ t
unfold-fold neg = refl
unfold-fold zer = refl
unfold-fold pos = refl

fold-unfold : (f : FoldedTrit) → foldTrit (unfoldTrit f) ≡ f
fold-unfold zeroFold = refl
fold-unfold (signed minus) = refl
fold-unfold (signed plus) = refl

support : Trit → Bool
support neg = true
support zer = false
support pos = true

foldedSupport : FoldedTrit → Bool
foldedSupport zeroFold = false
foldedSupport (signed _) = true

support-preserved : (t : Trit) → foldedSupport (foldTrit t) ≡ support t
support-preserved neg = refl
support-preserved zer = refl
support-preserved pos = refl

------------------------------------------------------------------------
-- Five-trit byte code: constructive encoder, decoder obligation explicit
------------------------------------------------------------------------

tritCode : Trit → Nat
tritCode neg = zero
tritCode zer = suc zero
tritCode pos = suc (suc zero)

record FiveTrits : Set where
  constructor five
  field
    t0 t1 t2 t3 t4 : Trit

open FiveTrits public

encode5 : FiveTrits → Nat
encode5 x =
  tritCode (t0 x)
  + 3 * (tritCode (t1 x)
  + 3 * (tritCode (t2 x)
  + 3 * (tritCode (t3 x)
  + 3 * tritCode (t4 x))))

record Pack5Contract : Set where
  field
    decode5 : Nat → FiveTrits
    decodeEncode5 : (x : FiveTrits) → decode5 (encode5 x) ≡ x
    encodedRangeLt243 : FiveTrits → Set

-- The mathematical cardinality fact is 3^5 = 243 <= 256.  The executable
-- byte-level decoder and bounded-Nat proof are intentionally isolated in the
-- contract so this bridge does not pretend that a raw Nat is already a byte.

------------------------------------------------------------------------
-- Finite p-adic cylinder interface
------------------------------------------------------------------------

record BalancedDigitSystem : Set₁ where
  field
    Integer : Set
    digit : Nat → Integer → Trit
    truncate : Nat → Integer → Integer
    reconstructFinite : Nat → Vec Trit Nat.zero → Integer

-- The repo's existing checked balanced-trit embedding is imported above as
-- BalancedEmbedding.  This codec interface keeps integer residual expansion
-- abstract because the current embedding uses its own bounded QQ/tower carrier.

record CylinderSystem : Set₁ where
  field
    Residual : Set
    Cylinder : Nat → Set
    project : (k : Nat) → Residual → Cylinder k
    refine : (k : Nat) → Cylinder (suc k) → Cylinder k
    project-compatible :
      (k : Nat) →
      (r : Residual) →
      refine k (project (suc k) r) ≡ project k r

------------------------------------------------------------------------
-- Causal predictor charts
------------------------------------------------------------------------

record VideoCarrier : Set₁ where
  field
    Pixel : Set
    Sample : Set
    Frame : Set
    lookup : Frame → Pixel → Sample

record CausalChart (V : VideoCarrier) (t : Nat) : Set₁ where
  open VideoCarrier V
  field
    Past : Set
    pastContainsOnlyEarlierFrames : Past → Set
    Block : Set
    blockOf : Pixel → Block
    Lag : Block → Nat
    WarpFamily : Set
    WarpParameter : WarpFamily → Set
    family : Block → WarpFamily
    parameter : (b : Block) → WarpParameter (family b)
    predict : Past → Pixel → Sample

record CausalChartFamily (V : VideoCarrier) : Set₁ where
  field
    chart : (t : Nat) → CausalChart V t

------------------------------------------------------------------------
-- Residual planes, entropy streams, and lossless reconstruction
------------------------------------------------------------------------

record ResidualCodec (V : VideoCarrier) : Set₁ where
  open VideoCarrier V
  field
    Residual : Set
    subtract : Sample → Sample → Residual
    addResidual : Sample → Residual → Sample
    subtractAddRoundtrip :
      (x p : Sample) → addResidual p (subtract x p) ≡ x

    Depth : Set
    PlaneIndex : Depth → Set
    plane : (K : Depth) → PlaneIndex K → Residual → Trit
    assemble : (K : Depth) → (PlaneIndex K → Trit) → Residual
    planeAssembleRoundtrip :
      (K : Depth) →
      (r : Residual) →
      assemble K (λ k → plane K k r) ≡ r

record MatchedEntropyCoder : Set₁ where
  field
    Symbol : Set
    Context : Set
    Bitstream : Set
    encode : List Symbol → List Context → Bitstream
    decode : Bitstream → List Context → List Symbol
    matched :
      (symbols : List Symbol) →
      (contexts : List Context) →
      decode (encode symbols contexts) contexts ≡ symbols

record LosslessCodecReceipt : Set₁ where
  field
    Source : Set
    Bitstream : Set
    encode : Source → Bitstream
    decode : Bitstream → Source
    lossless : (x : Source) → decode (encode x) ≡ x

------------------------------------------------------------------------
-- MDL selection and rate claims: typed, but not silently promoted
------------------------------------------------------------------------

record MDLChartSelection : Set₁ where
  field
    Chart : Set
    Bits : Set
    descriptionLength : Chart → Bits
    noLongerThan : Bits → Bits → Set
    selected : Chart
    selectedMinimal :
      (candidate : Chart) →
      noLongerThan (descriptionLength selected) (descriptionLength candidate)

record PhysicalCodecLayout : Set₁ where
  field
    MaskWord : Set
    SignWord : Set
    PackedTritWord : Set
    SideWord : Set
    maskPlane : List MaskWord
    signOnSupport : List SignWord
    packedTritFallback : List PackedTritWord
    sideInformation : List SideWord
    deterministicDecodeOrder : Set

record EmpiricalRateReceipt : Set₁ where
  field
    measuredSequence : Set
    activeTritDensityByPlane : Nat → Set
    sideBitsPerPixelPerFrame : Set
    achievedBitsPerPixelPerFrame : Set
    comparisonTarget : Set
    measurementProtocol : Set
    losslessOrLossyMode : Set

record TriadicPAdicCodecBoundary : Set where
  constructor boundary
  field
    finiteTritCarrierChecked : Bool
    sheetLiftChecked : Bool
    inversionInvolutionChecked : Bool
    supportSignBijectionChecked : Bool
    causalCodecContractTyped : Bool
    losslessContractTyped : Bool
    mdlSelectionContractTyped : Bool
    pack5ExecutableDecoderProvedHere : Bool
    asymptoticSideCollapseProvedHere : Bool
    entropyOptimalityProvedHere : Bool
    av1SuperiorityProvedHere : Bool
    physicalSiliconSpeedupProvedHere : Bool

canonicalBoundary : TriadicPAdicCodecBoundary
canonicalBoundary =
  boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Cross-reference receipt: this bridge reuses, not replaces, repo spines
------------------------------------------------------------------------

record ExistingFormalismCrossReference : Setω where
  field
    tritCarrier : Set
    tritCarrierIsCanonical : tritCarrier ≡ Trit
    balancedEmbeddingSurface : Set
    balancedEmbeddingSurfaceIsExisting :
      balancedEmbeddingSurface
      ≡
      BalancedEmbedding.BalancedTernaryEmbeddingShapeReceipt
    mdlFunctionalSurface : Setω
    mdlFunctionalSurfaceIsExisting :
      mdlFunctionalSurface ≡ ExistingMDL.MDLFunctional
    w9TerminationRouteSurface : Setω
    w9TerminationRouteSurfaceIsExisting :
      w9TerminationRouteSurface ≡ W9MDL.MDLTerminationSeamWitness

canonicalCrossReference : ExistingFormalismCrossReference
canonicalCrossReference =
  record
    { tritCarrier = Trit
    ; tritCarrierIsCanonical = refl
    ; balancedEmbeddingSurface =
        BalancedEmbedding.BalancedTernaryEmbeddingShapeReceipt
    ; balancedEmbeddingSurfaceIsExisting = refl
    ; mdlFunctionalSurface = ExistingMDL.MDLFunctional
    ; mdlFunctionalSurfaceIsExisting = refl
    ; w9TerminationRouteSurface = W9MDL.MDLTerminationSeamWitness
    ; w9TerminationRouteSurfaceIsExisting = refl
    }
