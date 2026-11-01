module DASHI.Analysis.RiemannHermitianTopDownAssemblyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Top-down, proof-relevant assembly of the Hermitian transverse-defect route.
-- Each stage is literally built from the output of the preceding stage:
--
--   complex-Poisson/coercive finite retention
--      -> mixed-channel ledger on that finite energy
--      -> retained target-pair excess
--      -> prime-side normalization of exactly that retained excess
--      -> arithmetic error ledger
--      -> strict pair-above-error detectability
--      -> contradiction
--      -> RiemannHypothesisFor the repo's actual AnalyticSubstrate.
--
-- This module deliberately does not manufacture any source-facing analytic
-- estimate.  Its value is that after this point every unfilled field is a real
-- mathematical gap, not missing assembly glue.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Empty using (⊥)

open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.WeilConvolutionSquare
open import DASHI.Analysis.RiemannWeilSquareCriterion

open import DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact
  using
    ( CoerciveFiniteRetention
    ; FiniteRetentionCertificate
    ; coerciveFiniteRetentionImpliesCertificate
    ; doubledFiniteGridExcess
    )
open import DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact
  using
    ( MixedChannelGlobalLedger
    ; mixedChannelGlobalLedger
    ; PairInsideDiagonalLedger
    ; pairInsideDiagonalLedger
    ; PairAlmostOrthogonality
    ; pairAlmostOrthogonality
    ; RetainedPairCertificate
    ; retainedMargin
    ; retainedContainsPair
    ; pairAlmostOrthogonalityRetainsTarget
    )
open import DASHI.Analysis.RiemannPrimeSideExcessNormalizationExact
  using
    ( PrimeSideExcessNormalization
    ; primeSideExcessNormalization
    ; PrimeSideExcessErrorLedger
    ; primeSideExcessErrorLedger
    )
open import DASHI.Analysis.RiemannHermitianExcessDetectabilityAssemblyExact
  using
    ( HermitianExcessDetectabilityAssembly
    ; hermitianExcessDetectabilityAssembly
    ; hermitianExcessDetectabilityContradiction
    )

Neg : Set → Set
Neg P = P → ⊥

------------------------------------------------------------------------
-- STAGE 1.
--
-- The input to the top-down ladder is exactly the object obtained once the
-- complex-Poisson identity, alpha^2 coercivity, and finite-grid tail estimate
-- have been proved.  The finite retention certificate itself is no longer an
-- extra assumption: the preceding module derives it algebraically.
------------------------------------------------------------------------

finiteCertificate :
  CoerciveFiniteRetention → Set
finiteCertificate r = FiniteRetentionCertificate r

------------------------------------------------------------------------
-- STAGE 2: mixed interference is accounted against THE finite energy from
-- Stage 1, rather than against an unrelated global scalar.
------------------------------------------------------------------------

record MixedRetentionFromFinite (r : CoerciveFiniteRetention) : Set where
  constructor mixedRetentionFromFinite
  field
    mixedInterferenceBudget : Nat
    retainedGlobalExcess : Nat
    targetPairDefect : Nat
    otherDiagonalEnergy : Nat
    orthogonalityMargin : Nat

    mixedPlusRetainedIsFiniteEnergy :
      mixedInterferenceBudget + retainedGlobalExcess
        ≡ doubledFiniteGridExcess
            (coerciveFiniteRetentionImpliesCertificate r)

    pairPlusOtherIsFiniteEnergy :
      targetPairDefect + otherDiagonalEnergy
        ≡ doubledFiniteGridExcess
            (coerciveFiniteRetentionImpliesCertificate r)

    mixedPlusMarginIsOtherDiagonal :
      mixedInterferenceBudget + orthogonalityMargin
        ≡ otherDiagonalEnergy

open MixedRetentionFromFinite public

mixedGlobalLedger :
  (r : CoerciveFiniteRetention) →
  MixedRetentionFromFinite r →
  MixedChannelGlobalLedger
mixedGlobalLedger r m =
  mixedChannelGlobalLedger
    (doubledFiniteGridExcess
      (coerciveFiniteRetentionImpliesCertificate r))
    (mixedInterferenceBudget m)
    (retainedGlobalExcess m)
    (mixedPlusRetainedIsFiniteEnergy m)

mixedPairEmbedding :
  (r : CoerciveFiniteRetention) →
  (m : MixedRetentionFromFinite r) →
  PairInsideDiagonalLedger (mixedGlobalLedger r m)
mixedPairEmbedding r m =
  pairInsideDiagonalLedger
    (targetPairDefect m)
    (otherDiagonalEnergy m)
    (pairPlusOtherIsFiniteEnergy m)

mixedAlmostOrthogonality :
  (r : CoerciveFiniteRetention) →
  (m : MixedRetentionFromFinite r) →
  PairAlmostOrthogonality
    (mixedGlobalLedger r m)
    (mixedPairEmbedding r m)
mixedAlmostOrthogonality r m =
  pairAlmostOrthogonality
    (orthogonalityMargin m)
    (mixedPlusMarginIsOtherDiagonal m)

retainedPairFromFiniteMixed :
  (r : CoerciveFiniteRetention) →
  (m : MixedRetentionFromFinite r) →
  RetainedPairCertificate
    (mixedGlobalLedger r m)
    (mixedPairEmbedding r m)
retainedPairFromFiniteMixed r m =
  pairAlmostOrthogonalityRetainsTarget
    (mixedGlobalLedger r m)
    (mixedPairEmbedding r m)
    (mixedAlmostOrthogonality r m)

------------------------------------------------------------------------
-- STAGE 3: normalize the prime-side raw Frobenius trace using exactly the
-- retained mixed-channel excess from Stage 2.
------------------------------------------------------------------------

record PrimeNormalizationFromMixed
  (r : CoerciveFiniteRetention)
  (m : MixedRetentionFromFinite r) : Set where
  constructor primeNormalizationFromMixed
  field
    criticalCompatibleMainTerm : Nat
    rawFrobeniusTrace : Nat
    arithmeticErrorBudget : Nat
    arithmeticErrorSlack : Nat

    normalizedTraceIdentity :
      criticalCompatibleMainTerm + retainedGlobalExcess m
        ≡ rawFrobeniusTrace

    retainedExcessWithinArithmeticError :
      retainedGlobalExcess m + arithmeticErrorSlack
        ≡ arithmeticErrorBudget

open PrimeNormalizationFromMixed public

primeNormalization :
  (r : CoerciveFiniteRetention) →
  (m : MixedRetentionFromFinite r) →
  PrimeNormalizationFromMixed r m →
  PrimeSideExcessNormalization
primeNormalization r m p =
  primeSideExcessNormalization
    (criticalCompatibleMainTerm p)
    (retainedGlobalExcess m)
    (rawFrobeniusTrace p)
    (normalizedTraceIdentity p)

primeErrorLedger :
  (r : CoerciveFiniteRetention) →
  (m : MixedRetentionFromFinite r) →
  (p : PrimeNormalizationFromMixed r m) →
  PrimeSideExcessErrorLedger (primeNormalization r m p)
primeErrorLedger r m p =
  primeSideExcessErrorLedger
    (arithmeticErrorBudget p)
    (arithmeticErrorSlack p)
    (retainedExcessWithinArithmeticError p)

------------------------------------------------------------------------
-- STAGE 4: the only remaining scalar endgame input is a STRICT detectability
-- gap for the target pair over the arithmetic error floor.
------------------------------------------------------------------------

record DetectabilityFromPrime
  (r : CoerciveFiniteRetention)
  (m : MixedRetentionFromFinite r)
  (p : PrimeNormalizationFromMixed r m) : Set where
  constructor detectabilityFromPrime
  field
    detectabilityGapPredecessor : Nat
    targetPairBeatsArithmeticError :
      arithmeticErrorBudget p + suc detectabilityGapPredecessor
        ≡ targetPairDefect m

open DetectabilityFromPrime public

------------------------------------------------------------------------
-- COMPLETE OFF-LINE CERTIFICATE.
------------------------------------------------------------------------

record TopDownOffLineCertificate : Set where
  constructor topDownOffLineCertificate
  field
    finite : CoerciveFiniteRetention
    mixed : MixedRetentionFromFinite finite
    prime : PrimeNormalizationFromMixed finite mixed
    detectability : DetectabilityFromPrime finite mixed prime

open TopDownOffLineCertificate public

topDownToDetectabilityAssembly :
  TopDownOffLineCertificate → HermitianExcessDetectabilityAssembly
topDownToDetectabilityAssembly c =
  hermitianExcessDetectabilityAssembly
    (retainedGlobalExcess m)
    (arithmeticErrorBudget p)
    (arithmeticErrorSlack p)
    (targetPairDefect m)
    (retainedMargin pairRetained)
    (detectabilityGapPredecessor d)
    (retainedExcessWithinArithmeticError p)
    (retainedContainsPair pairRetained)
    (targetPairBeatsArithmeticError d)
  where
  r : CoerciveFiniteRetention
  r = finite c

  m : MixedRetentionFromFinite r
  m = mixed c

  p : PrimeNormalizationFromMixed r m
  p = prime c

  d : DetectabilityFromPrime r m p
  d = detectability c

  pairRetained :
    RetainedPairCertificate
      (mixedGlobalLedger r m)
      (mixedPairEmbedding r m)
  pairRetained = retainedPairFromFiniteMixed r m

topDownOffLineContradiction : TopDownOffLineCertificate → ⊥
topDownOffLineContradiction c =
  hermitianExcessDetectabilityContradiction
    (topDownToDetectabilityAssembly c)

------------------------------------------------------------------------
-- ACTUAL ZETA OWNERSHIP.
--
-- Unlike the earlier abstract ZeroOrbit surface, this producer is indexed by
-- the repo's genuine completed-zeta carrier.  It says exactly what remains to
-- be produced for a hypothetical nontrivial zero that is assumed off-line.
------------------------------------------------------------------------

record ActualZetaHermitianTopDownProducer
  (analytic : AnalyticSubstrate) : Set₁ where
  field
    certificateForOffLineZero :
      (s : ComplexAnalyticCarrier.Complex
        (AnalyticSubstrate.carrier analytic)) →
      CompletedRiemannZeta.nontrivialZero
        (AnalyticSubstrate.completed analytic) s →
      Neg
        (CompletedRiemannZeta.criticalLine
          (AnalyticSubstrate.completed analytic) s) →
      TopDownOffLineCertificate

actualZetaProducerExcludesOffLine :
  (analytic : AnalyticSubstrate) →
  ActualZetaHermitianTopDownProducer analytic →
  (s : ComplexAnalyticCarrier.Complex
    (AnalyticSubstrate.carrier analytic)) →
  CompletedRiemannZeta.nontrivialZero
    (AnalyticSubstrate.completed analytic) s →
  Neg
    (CompletedRiemannZeta.criticalLine
      (AnalyticSubstrate.completed analytic) s) →
  ⊥
actualZetaProducerExcludesOffLine analytic producer s hz hnot =
  topDownOffLineContradiction
    (ActualZetaHermitianTopDownProducer.certificateForOffLineZero
      producer s hz hnot)

------------------------------------------------------------------------
-- TOP-DOWN RH THEOREM.
--
-- The only logical closure needed is stability of the critical-line predicate.
-- The existing Weil-square separator ALREADY owns exactly this field, so the
-- second theorem reuses that existing connection directly.
------------------------------------------------------------------------

actualZetaHermitianTopDownImpliesRH :
  (analytic : AnalyticSubstrate) →
  ((s : ComplexAnalyticCarrier.Complex
      (AnalyticSubstrate.carrier analytic)) →
    Neg (Neg
      (CompletedRiemannZeta.criticalLine
        (AnalyticSubstrate.completed analytic) s)) →
    CompletedRiemannZeta.criticalLine
      (AnalyticSubstrate.completed analytic) s) →
  ActualZetaHermitianTopDownProducer analytic →
  RiemannHypothesisFor analytic
actualZetaHermitianTopDownImpliesRH analytic criticalLineStable producer s hz =
  criticalLineStable s
    (λ hnot →
      actualZetaProducerExcludesOffLine analytic producer s hz hnot)

hermitianTopDownPlusExistingWeilSeparatorImpliesRH :
  (analytic : AnalyticSubstrate) →
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (algebra : WeilConvolutionAlgebra space) →
  WeilSquareOffLineSeparator analytic space formula algebra →
  ActualZetaHermitianTopDownProducer analytic →
  RiemannHypothesisFor analytic
hermitianTopDownPlusExistingWeilSeparatorImpliesRH
  analytic space formula algebra separator producer =
  actualZetaHermitianTopDownImpliesRH
    analytic
    (WeilSquareOffLineSeparator.criticalLineStable separator)
    producer

------------------------------------------------------------------------
-- GAP INTERPRETATION
--
-- After the algebraic constructors above, `certificateForOffLineZero` factors
-- into only four genuinely analytic producers:
--
-- G1  CoerciveFiniteRetention
--     complex Hermitian Poisson + alpha^2 coercivity + finite-grid retention.
--
-- G2  MixedRetentionFromFinite
--     control of sum_{rho != sigma}[(a_rho.d_sigma)^2+(b_rho.c_sigma)^2]
--     strong enough to pay interference from non-target diagonal energy.
--
-- G3  PrimeNormalizationFromMixed
--     identify the retained Hermitian excess inside the source Frobenius trace
--     after removing the critical-compatible main term, with an error budget.
--
-- G4  DetectabilityFromPrime
--     localization OR higher moments OR arithmetic rigidity makes the one-pair
--     defect strictly larger than that error budget.
--
-- Everything from G1+G2+G3+G4 to RH is now executable composition.
------------------------------------------------------------------------
