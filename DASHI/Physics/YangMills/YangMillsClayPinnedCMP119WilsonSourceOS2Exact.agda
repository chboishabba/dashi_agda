{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSourceOS2Exact where

------------------------------------------------------------------------
-- A / PUBLISHED WILSON RP -> LITERAL CMP119 FINITE OS2
--
-- Alternative to reconstructing the Peter-Weyl square factorization in-repo.
-- Menotti-Pelissetto / Osterwalder-Seiler reflection positivity is a standard
-- imported theorem.  The only YM-specific input here is same-object
-- identification: the selected finite normalized CMP119 expectation and its
-- positive-time/reflection observable are exactly the Wilson objects to which
-- the imported theorem applies.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as Wilson
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit

record LiteralCMP119WilsonRPApplication
    (Configuration : Set)
    {sequenceLimit limitLaws quotient division}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (algebra : OS2.CylinderOSAlgebra (Configuration → ℝ))
    : Set₂ where
  field
    -- Imported source theorem instantiated on the repository observable/scalar
    -- types.  Its proof content comes from the standard source authority.
    published :
      Wilson.WilsonReflectionPositivityData
        (Configuration → ℝ) ℝ

    -- Same-object source identification.  These are the only physical
    -- application fields retained by this adapter.
    publishedThetaIsLiteralReflection :
      Wilson.theta published ≡ OS2.reflectObservable algebra

    publishedReflectedExpectationIsLiteral :
      ∀ cutoff observable →
      Wilson.reflectedProductExpectation published observable
      ≡
      Limit.finiteExpectation family cutoff
        (OS2.multiplyObservable algebra
          (OS2.reflectObservable algebra observable)
          observable)

    positiveTimeGaugeInvariant :
      ∀ observable →
      Wilson.GaugeInvariant published observable

    positiveTimeMeaning :
      ∀ observable →
      Wilson.PositiveTimeObservable published observable

    publishedNonnegativeIsRealOrder :
      ∀ value →
      Wilson.Nonnegative published value →
      0ℝ ≤ℝ value

open LiteralCMP119WilsonRPApplication public

singleObservableReflectionPositive :
  ∀ {Configuration sequenceLimit limitLaws quotient division family algebra}
    (application :
      LiteralCMP119WilsonRPApplication
        Configuration {sequenceLimit} {limitLaws} {quotient} {division}
        family algebra)
    cutoff observable →
  0ℝ ≤ℝ
    Limit.finiteExpectation family cutoff
      (OS2.multiplyObservable algebra
        (OS2.reflectObservable algebra observable)
        observable)
singleObservableReflectionPositive application cutoff observable =
  publishedNonnegativeIsRealOrder application _
    (substExpectation
      (publishedReflectedExpectationIsLiteral application cutoff observable)
      (Wilson.wilsonPositivityAtAnySeparationParity
        (published application)
        Wilson.evenSitePlane
        observable
        (positiveTimeGaugeInvariant application observable)
        (positiveTimeMeaning application observable)))
  where
  substExpectation :
    ∀ {left right : ℝ} →
    left ≡ right →
    Wilson.Nonnegative (published application) left →
    Wilson.Nonnegative (published application) right
  substExpectation Agda.Builtin.Equality.refl proof = proof

wilsonPublishedRPAuthorityLevel : ProofLevel
wilsonPublishedRPAuthorityLevel =
  Wilson.wilsonSitePlaneReflectionPositivityLevel

literalCMP119WilsonSourceIdentificationLevel : ProofLevel
literalCMP119WilsonSourceIdentificationLevel = conditional

literalCMP119SingleObservableOS2CompilerLevel : ProofLevel
literalCMP119SingleObservableOS2CompilerLevel = machineChecked

-- Finite Gram-family OS2 still needs the standard polarization/finite linear
-- combination step from single F positivity to arbitrary test families.  The
-- preferred constructive square route already performs that directly.
