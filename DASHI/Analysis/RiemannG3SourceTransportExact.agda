module DASHI.Analysis.RiemannG3SourceTransportExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Source-native G3 transport.
--
-- The Hermitian excess is first a finite ZERO-SIDE A-energy.  The paper/source
-- then gives G=A+E with E controlled by prop:tail and a prime-side estimate for
-- the raw G Frobenius square.  Therefore the faithful route is an inequality
-- chain, not the overly strong exact identity
--
--     criticalMain + excess = rawPrimeTrace.
--
-- Abstractly:
--
--   criticalMain + retainedExcess            = finiteAenergy
--   finiteAenergy + tailSlack                 = rawGenergy + tailBudget
--   rawGenergy + primeSlack                   = primeMain + primeError
--   criticalMain                              = primeMain
--
-- cancel the common main term to obtain
--
--   retainedExcess + (tailSlack+primeSlack)
--       = tailBudget + primeError.
--
-- Thus the arithmetic error floor consumed by detectability is exactly the
-- sum of the zero-side matrix-tail transport budget and the prime trace error.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

congPlusLeft : {a b : Nat} → a ≡ b → (c : Nat) → c + a ≡ c + b
congPlusLeft refl c = refl

congPlusRight : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
congPlusRight refl c = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b = sym (zeroRight b)
  where
  zeroRight : (n : Nat) → n + zero ≡ n
  zeroRight zero = refl
  zeroRight (suc n) rewrite zeroRight n = refl
+-comm (suc a) b rewrite +-comm a b = sym (sucRight b a)
  where
  sucRight : (n m : Nat) → n + suc m ≡ suc (n + m)
  sucRight zero m = refl
  sucRight (suc n) m rewrite sucRight n m = refl

cancelLeft : (c a b : Nat) → c + a ≡ c + b → a ≡ b
cancelLeft zero a b eq = eq
cancelLeft (suc c) a b refl = cancelLeft c a b refl

record G3SourceTransportLedger : Set where
  constructor g3SourceTransportLedger
  field
    criticalCompatibleMain : Nat
    retainedHermitianExcess : Nat
    finiteZeroSideFrobenius : Nat

    rawPrimeSideFrobenius : Nat
    zeroSideTailBudget : Nat
    zeroSideTailSlack : Nat

    primeCompatibleMain : Nat
    primeTraceError : Nat
    primeTraceSlack : Nat

    finiteADecomposition :
      criticalCompatibleMain + retainedHermitianExcess
        ≡ finiteZeroSideFrobenius

    zeroToPrimeTransport :
      finiteZeroSideFrobenius + zeroSideTailSlack
        ≡ rawPrimeSideFrobenius + zeroSideTailBudget

    primeTraceUpper :
      rawPrimeSideFrobenius + primeTraceSlack
        ≡ primeCompatibleMain + primeTraceError

    criticalMainMatchesPrimeMain :
      criticalCompatibleMain ≡ primeCompatibleMain

open G3SourceTransportLedger public

combinedArithmeticError : G3SourceTransportLedger → Nat
combinedArithmeticError g = zeroSideTailBudget g + primeTraceError g

combinedTransportSlack : G3SourceTransportLedger → Nat
combinedTransportSlack g = zeroSideTailSlack g + primeTraceSlack g

------------------------------------------------------------------------
-- Exact cancellation theorem.
------------------------------------------------------------------------

retainedExcessWithinCombinedSourceError :
  (g : G3SourceTransportLedger) →
  retainedHermitianExcess g + combinedTransportSlack g
    ≡ combinedArithmeticError g
retainedExcessWithinCombinedSourceError g =
  cancelLeft
    (criticalCompatibleMain g)
    (retainedHermitianExcess g + combinedTransportSlack g)
    (combinedArithmeticError g)
    chain
  where
  C : Nat
  C = criticalCompatibleMain g

  D : Nat
  D = retainedHermitianExcess g

  A : Nat
  A = finiteZeroSideFrobenius g

  G : Nat
  G = rawPrimeSideFrobenius g

  Et : Nat
  Et = zeroSideTailBudget g

  st : Nat
  st = zeroSideTailSlack g

  Ep : Nat
  Ep = primeTraceError g

  sp : Nat
  sp = primeTraceSlack g

  chain :
    C + (D + (st + sp)) ≡ C + (Et + Ep)
  chain =
    trans
      (sym (+-assoc C D (st + sp)))
      (trans
        (congPlusRight (finiteADecomposition g) (st + sp))
        (trans
          (+-assoc A st sp)
          (trans
            (congPlusRight (zeroToPrimeTransport g) sp)
            (trans
              (sym (+-assoc G Et sp))
              (trans
                (congPlusLeft (+-comm Et sp) G)
                (trans
                  (+-assoc G sp Et)
                  (trans
                    (congPlusRight (primeTraceUpper g) Et)
                    (trans
                      (congPlusRight (criticalMainMatchesPrimeMain g |> symEq) (Ep + Et))
                      (trans
                        (sym (+-assoc C Ep Et))
                        (congPlusLeft (+-comm Ep Et) C))))))))))
    where
    symEq : {x y : Nat} → x ≡ y → y ≡ x
    symEq refl = refl

------------------------------------------------------------------------
-- Cleaner source-facing factorization.  The upstream companion already owns:
--
-- * Gz=Gp from H-EF / explicit-formula bridge,
-- * G=A+E by definition,
-- * prop:tail bounds on E (operator and trace norm),
-- * generic Frobenius perturbation lemmas in Assembly.lean,
-- * thm:traces `tr2`: raw G Frobenius square = mainTr2 + O(E_T mainTr2).
--
-- The genuinely new G3 statement is therefore concentrated in identifying the
-- CRITICAL-compatible A baseline and proving that the retained Hermitian defect
-- from G1/G2 enters the finite A Frobenius square with the required sign/scale.
------------------------------------------------------------------------

record G3SourceOwnedTransport : Set₁ where
  field
    ExplicitFormulaGzEqualsGp : Set
    ZeroSideSplitGEqualsAPlusE : Set
    TailMatrixControl : Set
    FrobeniusPerturbationControl : Set
    PrimeSecondTraceBound : Set

    explicitFormulaGzEqualsGp : ExplicitFormulaGzEqualsGp
    zeroSideSplitGEqualsAPlusE : ZeroSideSplitGEqualsAPlusE
    tailMatrixControl : TailMatrixControl
    frobeniusPerturbationControl : FrobeniusPerturbationControl
    primeSecondTraceBound : PrimeSecondTraceBound

record G3RemainingAlignment (owned : G3SourceOwnedTransport) : Set₁ where
  field
    CriticalFiniteABaseline : Set
    RetainedDefectInsideAFrobenius : Set
    CriticalBaselineEqualsPrimeMain : Set

    criticalFiniteABaseline : CriticalFiniteABaseline
    retainedDefectInsideAFrobenius : RetainedDefectInsideAFrobenius
    criticalBaselineEqualsPrimeMain : CriticalBaselineEqualsPrimeMain
