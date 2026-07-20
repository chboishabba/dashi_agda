module DASHI.Physics.Closure.TriadicSpectralCompletionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (0ℤ; 1ℤ)

import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicFiniteArithmeticLaws as ArithmeticLaws
import DASHI.Algebra.TriadicDepthTwoCyclotomicDFT as DFT9
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Geometry.TriadicSpectralGenusOneCurve as SpectralCurve
import DASHI.Geometry.TriadicEllipticModuliGate as Elliptic
import DASHI.Physics.Closure.TriadicConcreteAnalyticInstances as Analytic
import DASHI.Physics.Closure.TriadicKraftMDLConsistency as KraftMDL
import DASHI.Physics.Closure.TriadicSpectralCompletionAssembly as Assembly

------------------------------------------------------------------------
-- Arbitrary-depth arithmetic receipt.

arbitraryDepthReceipt :
  (n : Nat) → Arithmetic.TriadicArithmeticLawReceipt n
arbitraryDepthReceipt = ArithmeticLaws.allDepthArithmeticLaws

------------------------------------------------------------------------
-- Genuine depth-two DFT witnesses.

zeroSignal9 : DFT9.Signal9
zeroSignal9 =
  DFT9.signal9
    DFT9.zeroC9 DFT9.zeroC9 DFT9.zeroC9
    DFT9.zeroC9 DFT9.zeroC9 DFT9.zeroC9
    DFT9.zeroC9 DFT9.zeroC9 DFT9.zeroC9

zeroDFTRoundTripAtFour :
  DFT9.atSignal
    (DFT9.synthesize9 (DFT9.analyze9 zeroSignal9))
    DFT9.i4
  ≡ DFT9.atSignal zeroSignal9 DFT9.i4
zeroDFTRoundTripAtFour =
  DFT9.reconstructAnalyze9 zeroSignal9 DFT9.i4

nontrivialCharacterSumVanishes :
  DFT9.characterSum DFT9.i3 DFT9.zeroC9
  ≡ DFT9.orthogonalityTarget DFT9.i3 DFT9.zeroC9
nontrivialCharacterSumVanishes =
  DFT9.characterOrthogonality9 DFT9.i3 DFT9.zeroC9

zeroParseval :
  DFT9.signalEnergy (DFT9.analyze9 zeroSignal9)
  ≡ DFT9.nineQ * DFT9.signalEnergy zeroSignal9
zeroParseval = DFT9.parseval9 zeroSignal9

------------------------------------------------------------------------
-- SL₂(Z) lattice reindexing witness.

identitySL2Z : Eisenstein.SL2Z
identitySL2Z = Eisenstein.sl2z 1ℤ 0ℤ 0ℤ 1ℤ refl

sampleLatticePoint : Eisenstein.LatticePoint
sampleLatticePoint = Eisenstein.lattice-point 1ℤ 1ℤ

identityLatticeRoundTrip :
  Eisenstein.inverseIndex identitySL2Z
    (Eisenstein.forwardIndex identitySL2Z sampleLatticePoint)
  ≡ sampleLatticePoint
identityLatticeRoundTrip =
  Eisenstein.inverseForward identitySL2Z sampleLatticePoint

------------------------------------------------------------------------
-- Smooth spectral curve and j witness.

spectralDiscriminantRegression :
  Elliptic.discriminantTerm
    SpectralCurve.f5CoefficientRing
    SpectralCurve.spectralCurve
  ≡ SpectralCurve.f1
spectralDiscriminantRegression =
  SpectralCurve.spectralDiscriminantExact

spectralJRegression :
  Elliptic.jCoordinate SpectralCurve.spectralJCertificate
  ≡ SpectralCurve.f2
spectralJRegression = refl

------------------------------------------------------------------------
-- Concrete analytic and MDL witnesses.

quarterTailRegression :
  Analytic.quarterPower Q.two
  + Analytic.quarterTailRadius (Agda.Builtin.Nat.suc Q.two)
  ≡ Analytic.quarterTailRadius Q.two
quarterTailRegression = Analytic.nextTailBudgetIdentity Q.two

kraftRegression : KraftMDL.kraftSum ≡ 1ℚ
kraftRegression = KraftMDL.kraftEquality

completionStatusRegression :
  Assembly.higherDepthCyclotomicDFTProved Assembly.currentCompletionStatus
  ≡ Agda.Builtin.Bool.true
completionStatusRegression = refl
