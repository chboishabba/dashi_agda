module DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONCRETE-B CONTRIBUTION
--
-- Execute one genuinely active literal odd-(P/Q) transport coefficient before
-- attempting the uniform same/adjacent Schur estimates.
--
-- Use the repository's official nonlinear shell index
--
--   j(k) = ceil(log_2 ||k||_infinity)
--
-- and the resonant modes
--
--   p = (1,0,0),
--   q = (1,1,0),
--   k = (2,1,0) = p+q.
--
-- Then j(q)=0 while j(k)=1.  At projector cutoff zero, q is low and k is
-- high, so the literal odd P/Q coefficient takes the QTP branch and is -T.
-- For the transverse advector coefficient a_p=(0,1,0),
--
--   q . a_p = 1,
--   T(k,q) = i,
--   [P,T]Q + [Q,T]P = -i
--
-- on this entry.
--
-- The calculation is carrier-correct: it works over ANY repository RealField
-- whose integer embedding sends +1 to the field unit.  No rational or Bishop
-- real is substituted for the literal Fourier scalar.  The selector-only model
-- below gives the exact canonical low/high bits; its derivative/curl fields are
-- deliberately dummy because the Round57 odd-PQ coefficient never reads them.
-- We do NOT call this dummy model a physical PDE realization.
--
-- Consequently B cannot be closed by a vacuous zero realization: on every
-- nontrivial compatible Fourier field the literal odd-PQ kernel has a concrete
-- nonzero active entry.  The remaining B work is quantitative whole-fibre
-- mass/Schur control of such entries.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportCoefficientSkewRound40Exact as Coeff
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd

natLeBoolRefl : (n : Nat) → Physical.natLeBool n n ≡ true
natLeBoolRefl zero = refl
natLeBoolRefl (suc n) = natLeBoolRefl n

selectorOnlyModel :
  ∀ {r} (F : C3.RealField r) → LP.PeriodicHardShellFourierPDE {r}
selectorOnlyModel F = record
  { realField = F
  ; shellOwner = Shell.shellIndex
  ; shellSelect = λ shell mode →
      Output.natEqual shell (Shell.shellIndex mode)
  ; lowSelect = λ cutoff mode →
      Physical.natLeBool (Shell.shellIndex mode) cutoff
  ; ownerSelected = λ mode →
      Output.natEqualRefl (Shell.shellIndex mode)
  ; ownerIncludedInOwnLowPass = λ mode →
      natLeBoolRefl (Shell.shellIndex mode)
  ; derivativeMultiplier = λ mode → C3.complexZero F
  ; curlMultiplier = λ mode value → value
  }

pMode qMode kMode : Z3.FourierMode
pMode = Z3.mode (+ 1) (+ 0) (+ 0)
qMode = Z3.mode (+ 1) (+ 1) (+ 0)
kMode = Z3.mode (+ 2) (+ 1) (+ 0)

testResonance : Z3.addMode pMode qMode ≡ kMode
testResonance = refl

testEntry : Matrix.PhysicalTransportMatrixEntry qMode kMode
testEntry = Matrix.physical-transport-matrix-entry pMode testResonance

qInfinityNormIsOne : Infinity.infinityNorm qMode ≡ Shell.pow2 zero
qInfinityNormIsOne = refl

kInfinityNormIsTwo : Infinity.infinityNorm kMode ≡ Shell.pow2 (suc zero)
kInfinityNormIsTwo = refl

qShellIndexIsZero : Shell.shellIndex qMode ≡ zero
qShellIndexIsZero =
  trans
    (cong Shell.shellIndexMagnitude qInfinityNormIsOne)
    (Shell.shellIndexPowerOfTwo zero)

kShellIndexIsOne : Shell.shellIndex kMode ≡ suc zero
kShellIndexIsOne =
  trans
    (cong Shell.shellIndexMagnitude kInfinityNormIsTwo)
    (Shell.shellIndexPowerOfTwo (suc zero))

qIsLowAtCutoffZero :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (selectorOnlyModel F) zero qMode ≡ true
qIsLowAtCutoffZero F rewrite qShellIndexIsZero = refl

kIsHighAtCutoffZero :
  ∀ {r} (F : C3.RealField r) →
  LP.lowSelect (selectorOnlyModel F) zero kMode ≡ false
kIsHighAtCutoffZero F rewrite kShellIndexIsOne = refl

oddPQTestEntryIsActive :
  ∀ {r} (F : C3.RealField r) →
  Odd.oddPQActive (selectorOnlyModel F) zero qMode kMode ≡ true
oddPQTestEntryIsActive F
  rewrite kIsHighAtCutoffZero F
        | qIsLowAtCutoffZero F = refl

record UnitPreservingIntegerEmbedding
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  field
    embedPositiveOne : C3.embedInteger E (+ 1) ≡ C3.one F

open UnitPreservingIntegerEmbedding public

yUnit : ∀ {r} (F : C3.RealField r) → C3.Complex3 F
yUnit F =
  C3.complex3
    (C3.complexZero F)
    (C3.complexOne F)
    (C3.complexZero F)

constantYAdvector :
  ∀ {r} (F : C3.RealField r) →
  Z3.FourierMode → C3.Complex3 F
constantYAdvector F mode = yUnit F

embeddedPositiveOneIsComplexOne :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  UnitPreservingIntegerEmbedding F E →
  C3.realEmbed F (C3.embedInteger E (+ 1)) ≡ C3.complexOne F
embeddedPositiveOneIsComplexOne {F = F} unit =
  cong (C3.realEmbed F) (embedPositiveOne unit)

embeddedZeroIsComplexZero :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  C3.realEmbed F (C3.embedInteger E (+ 0)) ≡ C3.complexZero F
embeddedZeroIsComplexZero {F = F} E =
  cong (C3.realEmbed F) (C3.embedZero E)

qDotYUnitIsOne :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : UnitPreservingIntegerEmbedding F E) →
  Coeff.modeDot E qMode (yUnit F) ≡ C3.complexOne F
qDotYUnitIsOne {F = F} {E = E} unit
  rewrite embeddedPositiveOneIsComplexOne unit
        | embeddedZeroIsComplexZero E
        | Hermitian.complexMultiplyZeroRight (C3.complexOne F)
        | Hermitian.complexMultiplyOneLeft (C3.complexOne F)
        | Hermitian.complexMultiplyZeroLeft (C3.complexZero F)
        | Algebra.complexAddZeroLeft (C3.complexOne F)
        | Algebra.complexAddZeroRight (C3.complexOne F) = refl

testTransportCoefficientIsI :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : UnitPreservingIntegerEmbedding F E) →
  Matrix.transportEntryCoefficient E (constantYAdvector F) testEntry
  ≡ C3.complexI F
testTransportCoefficientIsI {F = F} {E = E} unit
  rewrite qDotYUnitIsOne unit
        | Hermitian.complexMultiplyOneRight (C3.complexI F) = refl

literalOddPQTestCoefficientIsNegativeI :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : UnitPreservingIntegerEmbedding F E) →
  Odd.literalOddPQEntryCoefficient
    (selectorOnlyModel F) zero E (constantYAdvector F) testEntry
  ≡ C3.complexNegate (C3.complexI F)
literalOddPQTestCoefficientIsNegativeI {F = F} {E = E} unit
  rewrite kIsHighAtCutoffZero F
        | qIsLowAtCutoffZero F
        | testTransportCoefficientIsI unit = refl

record NontrivialRealField {r : Level} (F : C3.RealField r) : Set r where
  field
    oneNotZero : C3.one F ≢ C3.zero F

open NontrivialRealField public

negativeImaginaryUnitNonzero :
  ∀ {r} {F : C3.RealField r} →
  NontrivialRealField F →
  C3.complexNegate (C3.complexI F) ≢ C3.complexZero F
negativeImaginaryUnitNonzero {F = F} nontrivial equality =
  oneNotZero nontrivial
    (trans
      (sym (C3.negateInvolutive F (C3.one F)))
      (trans
        (cong (C3.negate F) (cong C3.imaginary equality))
        (C3.negateZero F)))

literalOddPQTestCoefficientNonzero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  (unit : UnitPreservingIntegerEmbedding F E) →
  (nontrivial : NontrivialRealField F) →
  Odd.literalOddPQEntryCoefficient
    (selectorOnlyModel F) zero E (constantYAdvector F) testEntry
  ≢ C3.complexZero F
literalOddPQTestCoefficientNonzero unit nontrivial equality =
  negativeImaginaryUnitNonzero nontrivial
    (trans (sym (literalOddPQTestCoefficientIsNegativeI unit)) equality)

canonicalSelectorConcreteOddPQEntryConstructed : Bool
canonicalSelectorConcreteOddPQEntryConstructed = true

canonicalSelectorConcreteOddPQEntryIsActive : Bool
canonicalSelectorConcreteOddPQEntryIsActive = true

canonicalSelectorConcreteOddPQEntryIsNonzeroOnNontrivialField : Bool
canonicalSelectorConcreteOddPQEntryIsNonzeroOnNontrivialField = true

canonicalSelectorConcreteOddPQEntryConstructedIsTrue :
  canonicalSelectorConcreteOddPQEntryConstructed ≡ true
canonicalSelectorConcreteOddPQEntryConstructedIsTrue = refl

canonicalSelectorConcreteOddPQEntryIsActiveIsTrue :
  canonicalSelectorConcreteOddPQEntryIsActive ≡ true
canonicalSelectorConcreteOddPQEntryIsActiveIsTrue = refl

canonicalSelectorConcreteOddPQEntryIsNonzeroOnNontrivialFieldIsTrue :
  canonicalSelectorConcreteOddPQEntryIsNonzeroOnNontrivialField ≡ true
canonicalSelectorConcreteOddPQEntryIsNonzeroOnNontrivialFieldIsTrue = refl
