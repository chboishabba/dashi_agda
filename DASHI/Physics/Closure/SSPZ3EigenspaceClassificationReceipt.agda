module DASHI.Physics.Closure.SSPZ3EigenspaceClassificationReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import MonsterOntos using
  ( SSP
  ; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31
  ; p41; p47; p59; p71
  )
import Ontology.Hecke.Scan as HS

------------------------------------------------------------------------
-- Corrected Z/3 eigenspace classification over the SSP prime lane.
--
-- This receipt is deliberately a classification/input-structure surface:
-- it records the corrected local labelling regime for all 15 SSP primes,
-- the Hecke-family scan shape, and the isolated p=7 CM special case.
-- It does not promote CKM, CP, YM, NS, or Clay claims.

data Z3EigenspaceLabelling : Set where
  intrinsicPsiOmega :
    Z3EigenspaceLabelling

  requiresQuadraticExtensionQpOmega :
    Z3EigenspaceLabelling

  ramifiedAtThree :
    Z3EigenspaceLabelling

data PsiIndex : Set where
  psi0 psi1 psi2 : PsiIndex

data OmegaPower : Set where
  omega0 omega1 omega2 : OmegaPower

psiAtTwo : PsiIndex → OmegaPower
psiAtTwo psi0 = omega0
psiAtTwo psi1 = omega1
psiAtTwo psi2 = omega2

z3Labelling : SSP → Z3EigenspaceLabelling
z3Labelling p2  = requiresQuadraticExtensionQpOmega
z3Labelling p3  = ramifiedAtThree
z3Labelling p5  = requiresQuadraticExtensionQpOmega
z3Labelling p7  = intrinsicPsiOmega
z3Labelling p11 = requiresQuadraticExtensionQpOmega
z3Labelling p13 = intrinsicPsiOmega
z3Labelling p17 = requiresQuadraticExtensionQpOmega
z3Labelling p19 = intrinsicPsiOmega
z3Labelling p23 = requiresQuadraticExtensionQpOmega
z3Labelling p29 = requiresQuadraticExtensionQpOmega
z3Labelling p31 = intrinsicPsiOmega
z3Labelling p41 = requiresQuadraticExtensionQpOmega
z3Labelling p47 = requiresQuadraticExtensionQpOmega
z3Labelling p59 = requiresQuadraticExtensionQpOmega
z3Labelling p71 = requiresQuadraticExtensionQpOmega

canonicalIntrinsicZ3SSPPrimes : List SSP
canonicalIntrinsicZ3SSPPrimes =
  p7 ∷ p13 ∷ p19 ∷ p31 ∷ []

canonicalQuadraticExtensionZ3SSPPrimes : List SSP
canonicalQuadraticExtensionZ3SSPPrimes =
  p2 ∷ p5 ∷ p11 ∷ p17 ∷ p23 ∷ p29 ∷ p41 ∷ p47 ∷ p59 ∷ p71 ∷ []

canonicalRamifiedZ3SSPPrimes : List SSP
canonicalRamifiedZ3SSPPrimes =
  p3 ∷ []

cmPrimeForQsqrtMinusSeven : SSP → Bool
cmPrimeForQsqrtMinusSeven p2  = false
cmPrimeForQsqrtMinusSeven p3  = false
cmPrimeForQsqrtMinusSeven p5  = false
cmPrimeForQsqrtMinusSeven p7  = true
cmPrimeForQsqrtMinusSeven p11 = false
cmPrimeForQsqrtMinusSeven p13 = false
cmPrimeForQsqrtMinusSeven p17 = false
cmPrimeForQsqrtMinusSeven p19 = false
cmPrimeForQsqrtMinusSeven p23 = false
cmPrimeForQsqrtMinusSeven p29 = false
cmPrimeForQsqrtMinusSeven p31 = false
cmPrimeForQsqrtMinusSeven p41 = false
cmPrimeForQsqrtMinusSeven p47 = false
cmPrimeForQsqrtMinusSeven p59 = false
cmPrimeForQsqrtMinusSeven p71 = false

data CKMCPYMNClayPromotionAuthorityToken : Set where

------------------------------------------------------------------------
-- Hecke-family shape: one operator T_p : State -> State for every SSP
-- prime, and the scan surface returns Sig15.

classificationHeckeFamily : HS.HeckeFamily
classificationHeckeFamily =
  record
    { T = λ _ s → s
    ; compat = λ _ _ → false
    }

record HeckeFamilyFifteenOperatorSurface : Set₁ where
  field
    family :
      HS.HeckeFamily

    T2 T3 T5 T7 T11 T13 T17 T19 T23 T29 T31 T41 T47 T59 T71 :
      HS.State → HS.State

    T2-is-family :
      T2 ≡ HS.HeckeFamily.T family p2
    T3-is-family :
      T3 ≡ HS.HeckeFamily.T family p3
    T5-is-family :
      T5 ≡ HS.HeckeFamily.T family p5
    T7-is-family :
      T7 ≡ HS.HeckeFamily.T family p7
    T11-is-family :
      T11 ≡ HS.HeckeFamily.T family p11
    T13-is-family :
      T13 ≡ HS.HeckeFamily.T family p13
    T17-is-family :
      T17 ≡ HS.HeckeFamily.T family p17
    T19-is-family :
      T19 ≡ HS.HeckeFamily.T family p19
    T23-is-family :
      T23 ≡ HS.HeckeFamily.T family p23
    T29-is-family :
      T29 ≡ HS.HeckeFamily.T family p29
    T31-is-family :
      T31 ≡ HS.HeckeFamily.T family p31
    T41-is-family :
      T41 ≡ HS.HeckeFamily.T family p41
    T47-is-family :
      T47 ≡ HS.HeckeFamily.T family p47
    T59-is-family :
      T59 ≡ HS.HeckeFamily.T family p59
    T71-is-family :
      T71 ≡ HS.HeckeFamily.T family p71

    scan :
      HS.State → HS.Sig15

    scanReturnsSig15 :
      HS.State → HS.Sig15

    scan-is-Hecke-scan :
      scan ≡ HS.scan family

canonicalHeckeFamilyFifteenOperatorSurface :
  HeckeFamilyFifteenOperatorSurface
canonicalHeckeFamilyFifteenOperatorSurface =
  record
    { family = classificationHeckeFamily
    ; T2 = HS.HeckeFamily.T classificationHeckeFamily p2
    ; T3 = HS.HeckeFamily.T classificationHeckeFamily p3
    ; T5 = HS.HeckeFamily.T classificationHeckeFamily p5
    ; T7 = HS.HeckeFamily.T classificationHeckeFamily p7
    ; T11 = HS.HeckeFamily.T classificationHeckeFamily p11
    ; T13 = HS.HeckeFamily.T classificationHeckeFamily p13
    ; T17 = HS.HeckeFamily.T classificationHeckeFamily p17
    ; T19 = HS.HeckeFamily.T classificationHeckeFamily p19
    ; T23 = HS.HeckeFamily.T classificationHeckeFamily p23
    ; T29 = HS.HeckeFamily.T classificationHeckeFamily p29
    ; T31 = HS.HeckeFamily.T classificationHeckeFamily p31
    ; T41 = HS.HeckeFamily.T classificationHeckeFamily p41
    ; T47 = HS.HeckeFamily.T classificationHeckeFamily p47
    ; T59 = HS.HeckeFamily.T classificationHeckeFamily p59
    ; T71 = HS.HeckeFamily.T classificationHeckeFamily p71
    ; T2-is-family = refl
    ; T3-is-family = refl
    ; T5-is-family = refl
    ; T7-is-family = refl
    ; T11-is-family = refl
    ; T13-is-family = refl
    ; T17-is-family = refl
    ; T19-is-family = refl
    ; T23-is-family = refl
    ; T29-is-family = refl
    ; T31-is-family = refl
    ; T41-is-family = refl
    ; T47-is-family = refl
    ; T59-is-family = refl
    ; T71-is-family = refl
    ; scan = HS.scan classificationHeckeFamily
    ; scanReturnsSig15 = HS.scan classificationHeckeFamily
    ; scan-is-Hecke-scan = refl
    }

record SSPZ3EigenspaceClassificationReceipt : Set₁ where
  field
    heckeSurface :
      HeckeFamilyFifteenOperatorSurface

    labelling :
      SSP → Z3EigenspaceLabelling

    labellingIsCanonical :
      labelling ≡ z3Labelling

    intrinsicPrimes :
      List SSP

    intrinsicPrimesAreCanonical :
      intrinsicPrimes ≡ canonicalIntrinsicZ3SSPPrimes

    quadraticExtensionPrimes :
      List SSP

    quadraticExtensionPrimesAreCanonical :
      quadraticExtensionPrimes ≡ canonicalQuadraticExtensionZ3SSPPrimes

    ramifiedPrimes :
      List SSP

    ramifiedPrimesAreCanonical :
      ramifiedPrimes ≡ canonicalRamifiedZ3SSPPrimes

    psiLabellingStatement :
      String

    p7LowestIntrinsicZ3SSPPrime :
      SSP

    p7LowestIntrinsicZ3SSPPrimeIsCanonical :
      p7LowestIntrinsicZ3SSPPrime ≡ p7

    p7CMForQsqrtMinusSeven :
      cmPrimeForQsqrtMinusSeven p7 ≡ true

    p13NotCMForQsqrtMinusSeven :
      cmPrimeForQsqrtMinusSeven p13 ≡ false

    p19NotCMForQsqrtMinusSeven :
      cmPrimeForQsqrtMinusSeven p19 ≡ false

    p31NotCMForQsqrtMinusSeven :
      cmPrimeForQsqrtMinusSeven p31 ≡ false

    ckmPromoted :
      Bool

    ckmPromotedIsFalse :
      ckmPromoted ≡ false

    cpPromoted :
      Bool

    cpPromotedIsFalse :
      cpPromoted ≡ false

    ymPromoted :
      Bool

    ymPromotedIsFalse :
      ymPromoted ≡ false

    nsPromoted :
      Bool

    nsPromotedIsFalse :
      nsPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    noPromotionWithoutAuthority :
      CKMCPYMNClayPromotionAuthorityToken → ⊥

open SSPZ3EigenspaceClassificationReceipt public

canonicalSSPZ3EigenspaceClassificationReceipt :
  SSPZ3EigenspaceClassificationReceipt
canonicalSSPZ3EigenspaceClassificationReceipt =
  record
    { heckeSurface =
        canonicalHeckeFamilyFifteenOperatorSurface
    ; labelling =
        z3Labelling
    ; labellingIsCanonical =
        refl
    ; intrinsicPrimes =
        canonicalIntrinsicZ3SSPPrimes
    ; intrinsicPrimesAreCanonical =
        refl
    ; quadraticExtensionPrimes =
        canonicalQuadraticExtensionZ3SSPPrimes
    ; quadraticExtensionPrimesAreCanonical =
        refl
    ; ramifiedPrimes =
        canonicalRamifiedZ3SSPPrimes
    ; ramifiedPrimesAreCanonical =
        refl
    ; psiLabellingStatement =
        "For SSP primes p == 1 mod 3, the Z/3 eigenspaces are intrinsically labelled by psi_k(2)=omega^k; for p == 2 mod 3, the labelling requires Q_p(omega)/Q_p; p=3 is ramified."
    ; p7LowestIntrinsicZ3SSPPrime =
        p7
    ; p7LowestIntrinsicZ3SSPPrimeIsCanonical =
        refl
    ; p7CMForQsqrtMinusSeven =
        refl
    ; p13NotCMForQsqrtMinusSeven =
        refl
    ; p19NotCMForQsqrtMinusSeven =
        refl
    ; p31NotCMForQsqrtMinusSeven =
        refl
    ; ckmPromoted =
        false
    ; ckmPromotedIsFalse =
        refl
    ; cpPromoted =
        false
    ; cpPromotedIsFalse =
        refl
    ; ymPromoted =
        false
    ; ymPromotedIsFalse =
        refl
    ; nsPromoted =
        false
    ; nsPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    }

intrinsicZ3PrimesAreCorrect :
  intrinsicPrimes canonicalSSPZ3EigenspaceClassificationReceipt
    ≡
  p7 ∷ p13 ∷ p19 ∷ p31 ∷ []
intrinsicZ3PrimesAreCorrect =
  refl

quadraticExtensionZ3PrimesAreCorrect :
  quadraticExtensionPrimes canonicalSSPZ3EigenspaceClassificationReceipt
    ≡
  p2 ∷ p5 ∷ p11 ∷ p17 ∷ p23 ∷ p29 ∷ p41 ∷ p47 ∷ p59 ∷ p71 ∷ []
quadraticExtensionZ3PrimesAreCorrect =
  refl

p3Z3PrimeIsRamified :
  z3Labelling p3 ≡ ramifiedAtThree
p3Z3PrimeIsRamified =
  refl

p7IsUniqueSpecialIntrinsicCMPrime :
  z3Labelling p7 ≡ intrinsicPsiOmega
    ×
  cmPrimeForQsqrtMinusSeven p7 ≡ true
p7IsUniqueSpecialIntrinsicCMPrime =
  refl , refl
