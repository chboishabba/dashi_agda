module DASHI.Physics.Closure.NSTriadKNC4cDissipationWeightProjectorResidualRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND88 / C4c WEIGHT DECOMPOSITION
--
-- Round87 reduced the advective contribution to a commutator [W,T].  For the
-- literal compact-transfer denominator the diagonal observation weight is
--
--     W_K(k) = |k|^2 chi_K(k).
--
-- The mature Com lane controls projector commutators.  The exact bridge is to
-- choose any reference shell weight a_K and write
--
--     W_K = a_K chi_K + R_K,
--     R_K(k) = W_K(k) - a_K chi_K(k).
--
-- Entrywise, for every transport matrix coefficient T_{out,in},
--
--   (W(out)-W(in)) T
--     = a_K (chi(out)-chi(in)) T
--       + (R(out)-R(in)) T.
--
-- Thus C4c has one principal projector-commutator channel and one explicit
-- spectral-spread commutator.  This is exact algebra on the SAME literal
-- dissipation weights and transport coefficient; no estimate or replacement
-- carrier is used.
--
-- IMPORTANT BOUNDARY
-- The current PeriodicHardShellFourierPDE interface does not assert that its
-- `shellSelect K` is definitionally a difference of the `lowSelect` projectors
-- used by the existing odd-P/Q Com theorem.  Therefore this module does NOT
-- silently identify the principal shell commutator with the Round62 odd-P/Q
-- coefficient.  A canonical-model shell/low-pass identity, or a direct shell
-- Com estimate, is still required for that final weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Matrix
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift

------------------------------------------------------------------------
-- Generic exact complex-ring identity.
------------------------------------------------------------------------

residualWeight :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
residualWeight weight reference grade =
  C3.complexSubtract weight (C3.complexMultiply reference grade)

weightedCommutatorCoefficient :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
weightedCommutatorCoefficient outWeight inWeight transport =
  C3.complexMultiply
    (C3.complexSubtract outWeight inWeight)
    transport

projectorCommutatorCoefficient :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F
projectorCommutatorCoefficient reference outGrade inGrade transport =
  C3.complexMultiply reference
    (C3.complexMultiply
      (C3.complexSubtract outGrade inGrade)
      transport)

residualCommutatorCoefficient :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F →
  C3.Complex F → C3.Complex F → C3.Complex F
residualCommutatorCoefficient reference outWeight inWeight outGrade inGrade transport =
  weightedCommutatorCoefficient
    (residualWeight outWeight reference outGrade)
    (residualWeight inWeight reference inGrade)
    transport

weightCommutatorSplitsProjectorAndResidual :
  ∀ {r} {F : C3.RealField r}
    (reference outWeight inWeight outGrade inGrade transport : C3.Complex F) →
  weightedCommutatorCoefficient outWeight inWeight transport
  ≡ C3.complexAdd
      (projectorCommutatorCoefficient reference outGrade inGrade transport)
      (residualCommutatorCoefficient
        reference outWeight inWeight outGrade inGrade transport)
weightCommutatorSplitsProjectorAndResidual {F = F}
    reference outWeight inWeight outGrade inGrade transport =
  C.solve 6
    (λ a wo wi go gi t →
      ((wo C.⊕ C.⊝ wi) C.⊗ t)
      C.⊜
      ((a C.⊗ ((go C.⊕ C.⊝ gi) C.⊗ t))
        C.⊕
        ((((wo C.⊕ C.⊝ (a C.⊗ go))
          C.⊕ C.⊝ (wi C.⊕ C.⊝ (a C.⊗ gi))) C.⊗ t))))
    refl reference outWeight inWeight outGrade inGrade transport
  where module C = Ring.Solver F

------------------------------------------------------------------------
-- Literal shell-weight instantiation.
------------------------------------------------------------------------

shellGrade :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r}) →
  Nat → Z3.FourierMode → C3.Complex (LP.realField model)
shellGrade model shell mode with LP.shellSelect model shell mode
... | true = C3.complexOne (LP.realField model)
... | false = C3.complexZero (LP.realField model)

literalDissipationWeight :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  Drift.LiteralPhysicalCompactTransferDatum model →
  Z3.FourierMode → C3.Complex (LP.realField model)
literalDissipationWeight datum = Drift.modeDissipationWeight datum

literalShellResidualWeight :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  C3.Complex (LP.realField model) →
  Z3.FourierMode → C3.Complex (LP.realField model)
literalShellResidualWeight {model = model} datum reference mode =
  residualWeight
    (literalDissipationWeight datum mode)
    reference
    (shellGrade model (Drift.shell datum) mode)

literalWeightedTransportCommutatorEntry :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    {E : C3.IntegerEmbedding (LP.realField model)} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalWeightedTransportCommutatorEntry datum velocity {input} {output} entry =
  weightedCommutatorCoefficient
    (literalDissipationWeight datum output)
    (literalDissipationWeight datum input)
    (Matrix.transportEntryCoefficient _ velocity entry)

literalShellProjectorPrincipalEntry :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    {E : C3.IntegerEmbedding (LP.realField model)} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  C3.Complex (LP.realField model) →
  (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalShellProjectorPrincipalEntry {model = model}
    datum reference velocity {input} {output} entry =
  projectorCommutatorCoefficient
    reference
    (shellGrade model (Drift.shell datum) output)
    (shellGrade model (Drift.shell datum) input)
    (Matrix.transportEntryCoefficient _ velocity entry)

literalShellSpreadResidualEntry :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    {E : C3.IntegerEmbedding (LP.realField model)} →
  (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  C3.Complex (LP.realField model) →
  (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output} →
  Matrix.PhysicalTransportMatrixEntry input output →
  C3.Complex (LP.realField model)
literalShellSpreadResidualEntry {model = model}
    datum reference velocity {input} {output} entry =
  residualCommutatorCoefficient
    reference
    (literalDissipationWeight datum output)
    (literalDissipationWeight datum input)
    (shellGrade model (Drift.shell datum) output)
    (shellGrade model (Drift.shell datum) input)
    (Matrix.transportEntryCoefficient _ velocity entry)

literalWeightedTransportEntrySplitsExactly :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    {E : C3.IntegerEmbedding (LP.realField model)}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model)
    (reference : C3.Complex (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  ∀ {input output}
    (entry : Matrix.PhysicalTransportMatrixEntry input output) →
  literalWeightedTransportCommutatorEntry datum velocity entry
  ≡ C3.complexAdd
      (literalShellProjectorPrincipalEntry datum reference velocity entry)
      (literalShellSpreadResidualEntry datum reference velocity entry)
literalWeightedTransportEntrySplitsExactly {model = model}
    datum reference velocity {input} {output} entry =
  weightCommutatorSplitsProjectorAndResidual
    reference
    (literalDissipationWeight datum output)
    (literalDissipationWeight datum input)
    (shellGrade model (Drift.shell datum) output)
    (shellGrade model (Drift.shell datum) input)
    (Matrix.transportEntryCoefficient _ velocity entry)

round88C4cWeightedTransportSplitsProjectorAndSpread : Bool
round88C4cWeightedTransportSplitsProjectorAndSpread = true

round88PrincipalShellCommutatorDefinitionallyEqualsLowPassOddPQ : Bool
round88PrincipalShellCommutatorDefinitionallyEqualsLowPassOddPQ = false

round88C4cWeightedTransportSplitsProjectorAndSpreadIsTrue :
  round88C4cWeightedTransportSplitsProjectorAndSpread ≡ true
round88C4cWeightedTransportSplitsProjectorAndSpreadIsTrue = refl

round88PrincipalShellCommutatorDefinitionallyEqualsLowPassOddPQIsFalse :
  round88PrincipalShellCommutatorDefinitionallyEqualsLowPassOddPQ ≡ false
round88PrincipalShellCommutatorDefinitionallyEqualsLowPassOddPQIsFalse = refl
