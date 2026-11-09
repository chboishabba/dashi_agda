module DASHI.Information.PNFMarchenkoPasturFiniteExact where

-- Finite, assumption-explicit bridge to the existing PNF spectral carrier.
-- No asymptotic MP convergence theorem or empirical PNF null-model admission
-- is asserted by this module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import DASHI.Information.PNFSpectralGeometry

------------------------------------------------------------------------
-- A constructive finite Gram positivity lemma.
-- The backend must supply a genuine finite sum and its order laws.
------------------------------------------------------------------------

record FiniteGramOrder (𝕂 : ScalarStructure) : Set₁ where
  open ScalarStructure 𝕂
  field
    Row : Set
    sum : (Row → Scalar) → Scalar
    square-nonnegative : (x : Scalar) → 0# ≤ (x * x)
    sum-nonnegative :
      (f : Row → Scalar) →
      ((r : Row) → 0# ≤ f r) →
      0# ≤ sum f

open FiniteGramOrder public

record GramQuadratic
  (𝕂 : ScalarStructure)
  (O : FiniteGramOrder 𝕂) : Set₁ where
  open ScalarStructure 𝕂
  open FiniteGramOrder O
  field
    Vector : Set
    evaluation : Row → Vector → Scalar
    quadratic : Vector → Scalar
    same-gram :
      (v : Vector) →
      quadratic v ≡ sum (λ r → evaluation r v * evaluation r v)

open GramQuadratic public

finiteGramPositiveSemidefinite :
  (𝕂 : ScalarStructure) →
  (O : FiniteGramOrder 𝕂) →
  (G : GramQuadratic 𝕂 O) →
  (v : GramQuadratic.Vector G) →
  ScalarStructure._≤_ 𝕂
    (ScalarStructure.0# 𝕂)
    (GramQuadratic.quadratic G v)
finiteGramPositiveSemidefinite 𝕂 O G v
  rewrite GramQuadratic.same-gram G v =
    FiniteGramOrder.sum-nonnegative O
      (λ r → GramQuadratic.evaluation G r v *
             GramQuadratic.evaluation G r v)
      (λ r → FiniteGramOrder.square-nonnegative O
               (GramQuadratic.evaluation G r v))

------------------------------------------------------------------------
-- MP deterministic edge formulas, with explicit calibration obligations.
-- The variance and square-root witnesses are provided by the real backend.
------------------------------------------------------------------------

record MPFiniteCalibration (𝕂 : ScalarStructure) : Set₁ where
  open ScalarStructure 𝕂
  field
    aspectRatio variance sqrtAspect : Scalar
    lowerEdge upperEdge : Scalar
    lower-definition :
      lowerEdge ≡
      variance * ((1# + (- sqrtAspect)) * (1# + (- sqrtAspect)))
    upper-definition :
      upperEdge ≡
      variance * ((1# + sqrtAspect) * (1# + sqrtAspect))
    edgeOrdered : lowerEdge ≤ upperEdge

open MPFiniteCalibration public

calibratedMPBand :
  (𝕂 : ScalarStructure) →
  MPFiniteCalibration 𝕂 →
  SpectralNoiseBand 𝕂
calibratedMPBand 𝕂 c = record
  { lower = MPFiniteCalibration.lowerEdge c
  ; upper = MPFiniteCalibration.upperEdge c
  ; ordered = MPFiniteCalibration.edgeOrdered c
  }

------------------------------------------------------------------------
-- Evidence separation: a candidate signal does not itself promote a claim.
------------------------------------------------------------------------

record PNFModePromotion (Candidate : Set) : Set₁ where
  field
    selectedCandidate : Candidate
    SourceReceipt : Set
    StructuralReceipt : Set
    StabilityReceipt : Set
    sourcePaid : SourceReceipt
    structurePaid : StructuralReceipt
    stabilityPaid : StabilityReceipt

open PNFModePromotion public

promotionRequiresSource :
  {Candidate : Set} (p : PNFModePromotion Candidate) →
  PNFModePromotion.SourceReceipt p
promotionRequiresSource p = PNFModePromotion.sourcePaid p

promotionRequiresStructure :
  {Candidate : Set} (p : PNFModePromotion Candidate) →
  PNFModePromotion.StructuralReceipt p
promotionRequiresStructure p = PNFModePromotion.structurePaid p

promotionRequiresStability :
  {Candidate : Set} (p : PNFModePromotion Candidate) →
  PNFModePromotion.StabilityReceipt p
promotionRequiresStability p = PNFModePromotion.stabilityPaid p

------------------------------------------------------------------------
-- Historical matrix-shape check only; not a spectral analysis receipt.
-- 120 / 200 = 3 / 5, by exact cross multiplication.
------------------------------------------------------------------------

historicalAspectCrossProduct :
  (120 * 5) ≡ (200 * 3)
historicalAspectCrossProduct = refl
