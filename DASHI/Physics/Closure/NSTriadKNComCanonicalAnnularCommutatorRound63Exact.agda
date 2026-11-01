module DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularCommutatorRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 / B0 COEFFICIENT-LEVEL ANNULARIZATION
--
-- Round62 identified the literal odd-P/Q coefficient with the centered
-- low-projector commutator.  Round63 now constructs the required hatted pieces
-- rather than asking for their support abstractly.
--
-- For one literal transport entry T(out,in), define
--
--   C_s = (chi_{<=s}(out) - chi_{<=s}(in)) T,
--   A_s = (delta_s(out)    - delta_s(in))    T.
--
-- The exact canonical shell identities imply
--
--   C_0 = A_0,
--   C_{s+1} - C_s = A_{s+1}.
--
-- Hence the raw nested commutator is literally decomposed into annular
-- commutator coefficients.  This removes the first half of B0.  What remains
-- is the physical output-fibre lift plus the same/adjacent common-hat theorem
-- for these A_s pieces.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQCommutatorIdentityRound62Exact as Comm
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularProjectorRound63Exact as Annular

centeredGradeCoefficient :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
centeredGradeCoefficient outputGrade inputGrade transport =
  C3.complexMultiply
    (C3.complexSubtract outputGrade inputGrade)
    transport

canonicalLowCommutatorCoefficient :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex F
canonicalLowCommutatorCoefficient F cutoff E velocity
    {input} {output} entry =
  centeredGradeCoefficient
    (Annular.lowGrade F cutoff (Shell.shellIndex output))
    (Annular.lowGrade F cutoff (Shell.shellIndex input))
    (Matrix.transportEntryCoefficient E velocity entry)

canonicalAnnularCommutatorCoefficient :
  ∀ {r} (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex F
canonicalAnnularCommutatorCoefficient F shell E velocity
    {input} {output} entry =
  centeredGradeCoefficient
    (Annular.annularGrade F shell (Shell.shellIndex output))
    (Annular.annularGrade F shell (Shell.shellIndex input))
    (Matrix.transportEntryCoefficient E velocity entry)

baseLowCommutatorIsBaseAnnulus :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  canonicalLowCommutatorCoefficient F zero E velocity entry
  ≡ canonicalAnnularCommutatorCoefficient F zero E velocity entry
baseLowCommutatorIsBaseAnnulus F E velocity {input} {output} entry
  rewrite Annular.baseLowPassIsZeroAnnulus F (Shell.shellIndex output)
        | Annular.baseLowPassIsZeroAnnulus F (Shell.shellIndex input) = refl

successiveLowCommutatorDifferenceIsAnnular :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  C3.complexSubtract
    (canonicalLowCommutatorCoefficient F (suc cutoff) E velocity entry)
    (canonicalLowCommutatorCoefficient F cutoff E velocity entry)
  ≡ canonicalAnnularCommutatorCoefficient F (suc cutoff) E velocity entry
successiveLowCommutatorDifferenceIsAnnular
    F cutoff E velocity {input} {output} entry =
  trans polynomialRearrangement annularRewrite
  where
  outNext = Annular.lowGrade F (suc cutoff) (Shell.shellIndex output)
  outPrev = Annular.lowGrade F cutoff (Shell.shellIndex output)
  inNext = Annular.lowGrade F (suc cutoff) (Shell.shellIndex input)
  inPrev = Annular.lowGrade F cutoff (Shell.shellIndex input)
  transport = Matrix.transportEntryCoefficient E velocity entry

  polynomialRearrangement :
    C3.complexSubtract
      (centeredGradeCoefficient outNext inNext transport)
      (centeredGradeCoefficient outPrev inPrev transport)
    ≡ centeredGradeCoefficient
        (C3.complexSubtract outNext outPrev)
        (C3.complexSubtract inNext inPrev)
        transport
  polynomialRearrangement =
    R.solve 5
      (λ outNext outPrev inNext inPrev transport →
        (((outNext R.⊖ inNext) R.⊗ transport)
          R.⊖ ((outPrev R.⊖ inPrev) R.⊗ transport))
        R.⊜
        (((outNext R.⊖ outPrev) R.⊖ (inNext R.⊖ inPrev))
          R.⊗ transport))
      refl outNext outPrev inNext inPrev transport
    where module R = Ring.Solver F

  annularRewrite :
    centeredGradeCoefficient
      (C3.complexSubtract outNext outPrev)
      (C3.complexSubtract inNext inPrev)
      transport
    ≡ canonicalAnnularCommutatorCoefficient F (suc cutoff) E velocity entry
  annularRewrite
    rewrite Annular.successiveLowPassDifferenceIsAnnulus
      F (Shell.shellIndex output) cutoff
          | Annular.successiveLowPassDifferenceIsAnnulus
      F (Shell.shellIndex input) cutoff = refl

round63LiteralCenteredCommutatorAnnularizedCoefficientwise : Bool
round63LiteralCenteredCommutatorAnnularizedCoefficientwise = true

round63LiteralCenteredCommutatorAnnularizedCoefficientwiseIsTrue :
  round63LiteralCenteredCommutatorAnnularizedCoefficientwise ≡ true
round63LiteralCenteredCommutatorAnnularizedCoefficientwiseIsTrue = refl
