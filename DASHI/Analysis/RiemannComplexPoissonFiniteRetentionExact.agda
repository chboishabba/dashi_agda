module DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact subtraction-free assembly for the two analytic steps that remain
-- between complex Poisson and a finite Alpöge--Furman compression.
--
-- Analytic calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- Source audit against the accompanying `zeta-23-lean` development:
--
-- * `Zeta23/Poisson.lean` proves the Gabor Poisson identity for REAL arguments.
--   Its module header explicitly says the complex continuation mentioned in
--   [rem:pairblock] is not used/proved there.
-- * `Zeta23/Taper/Strip.lean` DOES prove the complex strip estimate
--
--     |phiHat(r-i y)| <= exp(L/4) C1 / |r-i y|^2,  |y| <= 1/2,
--
--   and `Zeta23/Tail.lean` consumes precisely that bound for the finite
--   zero-side tail estimate.
--
-- Thus the genuinely new source-facing edge is narrower than "build complex
-- Fourier control": it is the complexified Poisson/Hermitian identity and the
-- quantitative comparison of its full-grid excess with the chosen finite
-- compression.  Once a tail ledger exists, the retention certificate below is
-- now DERIVED rather than left as another premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

congPlusRight : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
congPlusRight refl c = refl

congPlusLeft : {a b : Nat} → a ≡ b → (c : Nat) → c + a ≡ c + b
congPlusLeft refl c = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

record ComplexPoissonNormContract : Set₁ where
  field
    AnalyticPair : Set
    squaredTransverseDisplacement : AnalyticPair → Nat
    coerciveWeight : Nat
    criticalBaseline : AnalyticPair → Nat
    fullGridHermitianNorm : AnalyticPair → Nat
    fullGridExcess : AnalyticPair → Nat
    coercivitySlack : AnalyticPair → Nat

    baselinePlusExcessIsFullNorm :
      (x : AnalyticPair) →
      criticalBaseline x + fullGridExcess x ≡ fullGridHermitianNorm x

    weightedDisplacementPlusSlackIsExcess :
      (x : AnalyticPair) →
      coerciveWeight * squaredTransverseDisplacement x + coercivitySlack x
        ≡ fullGridExcess x

record ComplexPoissonStripContinuation : Set₁ where
  field
    ComplexArgument : Set
    inRequiredStrip : ComplexArgument → Set
    conjugateArgument : ComplexArgument → ComplexArgument
    phiKernel : ComplexArgument → ComplexArgument → Nat
    gaborFullGrid : ComplexArgument → ComplexArgument → Nat
    continuedPoissonIdentity :
      (z w : ComplexArgument) →
      inRequiredStrip z → inRequiredStrip w →
      gaborFullGrid z w ≡ phiKernel z w

record FiniteGridTailLedger : Set where
  constructor finiteGridTailLedger
  field
    fullGridExcess : Nat
    finiteGridExcess : Nat
    tailLoss : Nat
    retentionMargin : Nat
    fullIsFinitePlusTail :
      fullGridExcess ≡ finiteGridExcess + tailLoss
    tailPlusMarginIsFinite :
      tailLoss + retentionMargin ≡ finiteGridExcess

open FiniteGridTailLedger public

record CoerciveFiniteRetention : Set where
  constructor coerciveFiniteRetention
  field
    weightedTransverseDefect : Nat
    coercivitySlack : Nat
    tailLedger : FiniteGridTailLedger
    coerciveFullGridIdentity :
      weightedTransverseDefect + coercivitySlack ≡ fullGridExcess tailLedger

open CoerciveFiniteRetention public

record FiniteRetentionCertificate (r : CoerciveFiniteRetention) : Set where
  constructor finiteRetentionCertificate
  field
    doubledFiniteGridExcess : Nat
    dominationIdentity :
      (weightedTransverseDefect r + coercivitySlack r)
        + retentionMargin (tailLedger r)
      ≡ doubledFiniteGridExcess
    doubledFiniteDefinition :
      doubledFiniteGridExcess
        ≡ finiteGridExcess (tailLedger r) + finiteGridExcess (tailLedger r)

------------------------------------------------------------------------
-- CONNECTION WE ALREADY HAVE.
--
-- No extra analytic premise is needed after `CoerciveFiniteRetention` has been
-- produced.  Its four ledger identities algebraically imply the doubled-finite
-- retention certificate.  This removes one former prose seam from the route.
------------------------------------------------------------------------

coerciveFiniteRetentionImpliesCertificate :
  (r : CoerciveFiniteRetention) → FiniteRetentionCertificate r
coerciveFiniteRetentionImpliesCertificate r =
  finiteRetentionCertificate
    (finiteGridExcess ledger + finiteGridExcess ledger)
    domination
    refl
  where
  ledger : FiniteGridTailLedger
  ledger = tailLedger r

  wToFull :
    weightedTransverseDefect r + coercivitySlack r
      ≡ fullGridExcess ledger
  wToFull = coerciveFullGridIdentity r

  fullToFiniteTail :
    fullGridExcess ledger
      ≡ finiteGridExcess ledger + tailLoss ledger
  fullToFiniteTail = fullIsFinitePlusTail ledger

  tailToFinite :
    tailLoss ledger + retentionMargin ledger
      ≡ finiteGridExcess ledger
  tailToFinite = tailPlusMarginIsFinite ledger

  domination :
    (weightedTransverseDefect r + coercivitySlack r)
      + retentionMargin ledger
      ≡ finiteGridExcess ledger + finiteGridExcess ledger
  domination =
    trans
      (congPlusRight wToFull (retentionMargin ledger))
      (trans
        (congPlusRight fullToFiniteTail (retentionMargin ledger))
        (trans
          (+-assoc
            (finiteGridExcess ledger)
            (tailLoss ledger)
            (retentionMargin ledger))
          (congPlusLeft tailToFinite (finiteGridExcess ledger))))

record ComplexPoissonFiniteRetentionProducer : Set₁ where
  field
    AnalyticPair : Set
    fullGridIdentityAvailable : AnalyticPair → Set
    coshCoercivityAvailable : AnalyticPair → Set
    finiteTailEstimateAvailable : AnalyticPair → Set
    retainedCertificate : AnalyticPair → CoerciveFiniteRetention

retentionCertificateFromProducer :
  (p : ComplexPoissonFiniteRetentionProducer) →
  (x : ComplexPoissonFiniteRetentionProducer.AnalyticPair p) →
  FiniteRetentionCertificate
    (ComplexPoissonFiniteRetentionProducer.retainedCertificate p x)
retentionCertificateFromProducer p x =
  coerciveFiniteRetentionImpliesCertificate
    (ComplexPoissonFiniteRetentionProducer.retainedCertificate p x)

record ComplexPoissonFiniteRetentionBoundary : Set where
  field
    complexPoissonAnalyticSocketConstructed : Bool
    finiteTailLedgerConstructed : Bool
    retentionCertificateDerivedFromLedger : Bool
    realPoissonIdentitySourceOwned : Bool
    complexPhiHatStripDecaySourceOwned : Bool
    sourceZeroSideTailMachineryExists : Bool
    analyticComplexPoissonContinuationProvedHere : Bool
    analyticCoshCoercivityProvedHere : Bool
    sourceFiniteWindowHermitianRetentionProvedHere : Bool
    zetaFiniteRetentionInstantiatedHere : Bool

complexPoissonFiniteRetentionBoundary : ComplexPoissonFiniteRetentionBoundary
complexPoissonFiniteRetentionBoundary = record
  { complexPoissonAnalyticSocketConstructed = true
  ; finiteTailLedgerConstructed = true
  ; retentionCertificateDerivedFromLedger = true
  ; realPoissonIdentitySourceOwned = true
  ; complexPhiHatStripDecaySourceOwned = true
  ; sourceZeroSideTailMachineryExists = true
  ; analyticComplexPoissonContinuationProvedHere = false
  ; analyticCoshCoercivityProvedHere = false
  ; sourceFiniteWindowHermitianRetentionProvedHere = false
  ; zetaFiniteRetentionInstantiatedHere = false
  }
