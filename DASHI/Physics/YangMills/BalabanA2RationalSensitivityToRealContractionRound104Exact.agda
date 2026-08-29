{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact where

------------------------------------------------------------------------
-- ROUND104 A2: EXACT-RATIONAL q CERTIFICATE -> LITERAL-REAL SHOOTING q
--
-- The source/cubic-drift sensitivity compiler is intentionally exact-rational;
-- the literal CMP109 dynamics and tube consumer use the repository's abstract
-- real carrier.  This file removes that representation seam.  We require only
-- the standard additive/order laws of the canonical Q -> R embedding.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanA2LiteralSameHistoryPrefixSensitivityRound103Exact as Literal
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Rational
import DASHI.Physics.YangMills.BalabanBetaPrefixSensitivityToTubeContractionExact as Shoot

record OrderedAdditiveRationalRealEmbedding : Set₁ where
  field
    base : Embed.OrderedRationalRealEmbedding
    oneExact : Embed.embed base 1ℚ ≡ 1ℝ
    addExact : ∀ a b →
      Embed.embed base (a ℚ.+ b)
      ≡ Embed.embed base a +ℝ Embed.embed base b

open OrderedAdditiveRationalRealEmbedding public

sumEmbedExact :
  (embedding : OrderedAdditiveRationalRealEmbedding) →
  (q : Nat → ℚ) → ∀ n →
  Embed.embed (base embedding) (Rational.sum₀ q n)
  ≡ Literal.sumReal (λ j → Embed.embed (base embedding) (q j)) n
sumEmbedExact embedding q Nat.zero = Embed.zeroExact (base embedding)
sumEmbedExact embedding q (Nat.suc n) =
  trans
    (addExact embedding (Rational.sum₀ q n) (q n))
    (cong (λ x → x +ℝ Embed.embed (base embedding) (q n))
      (sumEmbedExact embedding q n))

sumRealPointwiseExact :
  (f g : Nat → ℝ) →
  (pointwise : ∀ j → f j ≡ g j) → ∀ n →
  Literal.sumReal f n ≡ Literal.sumReal g n
sumRealPointwiseExact f g pointwise Nat.zero = refl
sumRealPointwiseExact f g pointwise (Nat.suc n) =
  trans
    (cong (λ x → x +ℝ f n) (sumRealPointwiseExact f g pointwise n))
    (cong (λ x → Literal.sumReal g n +ℝ x) (pointwise n))

record RationallyCertifiedLiteralSensitivity
    (TubePoint : Set) (K : Nat) : Set₁ where
  field
    embedding : OrderedAdditiveRationalRealEmbedding
    literal : Literal.LiteralSameHistoryShootingData TubePoint K
    rational : Rational.CumulativeSensitivityData K

    -- Same physical shell coefficient, merely represented in two scalar carriers.
    shellSensitivityExact : ∀ j →
      Literal.shellSensitivity (Literal.shells literal) j
      ≡ Embed.embed (base embedding) (Rational.CumulativeSensitivityData.sensitivity rational j)

open RationallyCertifiedLiteralSensitivity public

rationalQ :
  ∀ {TubePoint K} → RationallyCertifiedLiteralSensitivity TubePoint K → ℚ
rationalQ dataSet =
  Rational.sum₀
    (Rational.CumulativeSensitivityData.sensitivity (rational dataSet)) _

realQ :
  ∀ {TubePoint K} → RationallyCertifiedLiteralSensitivity TubePoint K → ℝ
realQ dataSet = Embed.embed (base (embedding dataSet)) (rationalQ dataSet)

literalSensitivitySumIsRealQ :
  ∀ {TubePoint K}
    (dataSet : RationallyCertifiedLiteralSensitivity TubePoint K) →
  Literal.sumReal
    (Literal.shellSensitivity (Literal.shells (literal dataSet))) K
  ≡ realQ dataSet
literalSensitivitySumIsRealQ {K = K} dataSet =
  let
    q = Rational.CumulativeSensitivityData.sensitivity (rational dataSet)
    pointwise = shellSensitivityExact dataSet
    first = sumRealPointwiseExact
      (Literal.shellSensitivity (Literal.shells (literal dataSet)))
      (λ j → Embed.embed (base (embedding dataSet)) (q j))
      pointwise K
    second = sym (sumEmbedExact (embedding dataSet) q K)
  in
  trans first second

realQBelowOne :
  ∀ {TubePoint K}
    (dataSet : RationallyCertifiedLiteralSensitivity TubePoint K) →
  realQ dataSet <ℝ 1ℝ
realQBelowOne {K = K} dataSet =
  let
    qBelow : rationalQ dataSet < 1ℚ
    qBelow = Rational.Sensitivity.cumulativeSensitivityBelowOne
      (rational dataSet) K ℕP.≤-refl
    embedded = Embed.strictOrderPreserving (base (embedding dataSet)) qBelow
  in
  Relation.Binary.PropositionalEquality.subst
    (λ right → realQ dataSet <ℝ right)
    (oneExact (embedding dataSet))
    embedded

literalCumulativeSensitivityWithRealQ :
  ∀ {TubePoint K}
    (dataSet : RationallyCertifiedLiteralSensitivity TubePoint K) u v →
  absℝ
    (Shoot.cumulativeBeta
        (Literal.asBetaPrefixShootingMap (literal dataSet)) u
      -ℝ Shoot.cumulativeBeta
        (Literal.asBetaPrefixShootingMap (literal dataSet)) v)
  ≤ℝ realQ dataSet *ℝ
      absℝ
        (Shoot.initialInverseSquare
            (Literal.asBetaPrefixShootingMap (literal dataSet)) u
          -ℝ Shoot.initialInverseSquare
            (Literal.asBetaPrefixShootingMap (literal dataSet)) v)
literalCumulativeSensitivityWithRealQ dataSet u v =
  let
    old = Literal.literalCumulativePrefixSensitivity (literal dataSet) u v
    distance = absℝ
      (Shoot.initialInverseSquare
          (Literal.asBetaPrefixShootingMap (literal dataSet)) u
        -ℝ Shoot.initialInverseSquare
          (Literal.asBetaPrefixShootingMap (literal dataSet)) v)
    upperExact = cong (λ coefficient → coefficient *ℝ distance)
      (literalSensitivitySumIsRealQ dataSet)
  in
  transportUpper upperExact old
  where
    transportUpper : ∀ {a b c : ℝ} → b ≡ c → a ≤ℝ b → a ≤ℝ c
    transportUpper refl proof = proof

literalShootingContractionWithSubunitRealQ :
  ∀ {TubePoint K}
    (dataSet : RationallyCertifiedLiteralSensitivity TubePoint K) u v →
  absℝ
    (Shoot.initialInverseSquare
        (Literal.asBetaPrefixShootingMap (literal dataSet))
        (Shoot.renormalisationMap
          (Literal.asBetaPrefixShootingMap (literal dataSet)) u)
      -ℝ
      Shoot.initialInverseSquare
        (Literal.asBetaPrefixShootingMap (literal dataSet))
        (Shoot.renormalisationMap
          (Literal.asBetaPrefixShootingMap (literal dataSet)) v))
  ≤ℝ realQ dataSet *ℝ
      absℝ
        (Shoot.initialInverseSquare
            (Literal.asBetaPrefixShootingMap (literal dataSet)) u
          -ℝ Shoot.initialInverseSquare
            (Literal.asBetaPrefixShootingMap (literal dataSet)) v)
literalShootingContractionWithSubunitRealQ dataSet =
  Shoot.prefixSensitivityImpliesShootingContraction
    (Literal.asBetaPrefixShootingMap (literal dataSet))
    (realQ dataSet)
    (literalCumulativeSensitivityWithRealQ dataSet)

rationalSensitivityToLiteralRealContractionLevel : ProofLevel
rationalSensitivityToLiteralRealContractionLevel = machineChecked

orderedAdditiveRationalRealEmbeddingLevel : ProofLevel
orderedAdditiveRationalRealEmbeddingLevel = standardImported

-- Physical A2 leaf after this weld: prove the literal shellwise CMP109 history
-- differences are bounded by the embedded rational sensitivity coefficients
-- already generated by the mixed-Cauchy/current + irrelevant-response package.
literalCMP109ShellSensitivityRationalIdentificationLevel : ProofLevel
literalCMP109ShellSensitivityRationalIdentificationLevel = conditional
