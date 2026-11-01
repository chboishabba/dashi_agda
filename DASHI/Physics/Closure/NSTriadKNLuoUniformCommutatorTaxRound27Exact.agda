module DASHI.Physics.Closure.NSTriadKNLuoUniformCommutatorTaxRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 26 proved the exact finite-kernel commutator identity and the first
-- moment scaling law separately.  This file joins the two scale factors in the
-- actual critical tax.  The kernel first moment contributes 2^{-q}, while the
-- differentiated high-frequency factor contributes 2^q.  Their product is
-- proved exactly equal to one, so every finite cell and every finite cell list
-- has a cutoff-independent mother-kernel coefficient.
--
-- This is a literal finite coefficient theorem.  The continuum L2/Linfinity
-- operator estimate and the physical shell evolution remain separate analytic
-- producers.
-------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Data.RationalExact using (ℚ; oneQ; _*_)

record DyadicCommutatorTaxCell : Set where
  field
    inverseScale : ℚ
    directScale : ℚ
    inverseDirectExact : inverseScale * directScale ≡ oneQ

    motherFirstMoment : ℚ
    lowGradientMagnitude : ℚ
    motherHighGradientMagnitude : ℚ

open DyadicCommutatorTaxCell public

shellFirstMoment : DyadicCommutatorTaxCell → ℚ
shellFirstMoment cell =
  inverseScale cell * motherFirstMoment cell

shellHighGradientMagnitude : DyadicCommutatorTaxCell → ℚ
shellHighGradientMagnitude cell =
  directScale cell * motherHighGradientMagnitude cell

shellCommutatorTax : DyadicCommutatorTaxCell → ℚ
shellCommutatorTax cell =
  shellFirstMoment cell
  * lowGradientMagnitude cell
  * shellHighGradientMagnitude cell
  * testedShellMagnitude cell

motherCommutatorTax : DyadicCommutatorTaxCell → ℚ
motherCommutatorTax cell =
  motherFirstMoment cell
  * lowGradientMagnitude cell
  * motherHighGradientMagnitude cell
  * testedShellMagnitude cell

cutoffIndependentCommutatorCellCoefficient :
  (cell : DyadicCommutatorTaxCell) →
  shellCommutatorTax cell ≡ motherCommutatorTax cell
cutoffIndependentCommutatorCellCoefficient cell =
  trans
    (solve
      ( inverseScale cell
      ∷ directScale cell
      ∷ motherFirstMoment cell
      ∷ lowGradientMagnitude cell
      ∷ motherHighGradientMagnitude cell
      ∷ testedShellMagnitude cell
      ∷ []))
    (trans
      (cong
        (λ scaleProduct →
          scaleProduct
          * (motherFirstMoment cell
            * lowGradientMagnitude cell
            * motherHighGradientMagnitude cell
            * testedShellMagnitude cell))
        (inverseDirectExact cell))
      (solve
        ( motherFirstMoment cell
        ∷ lowGradientMagnitude cell
        ∷ motherHighGradientMagnitude cell
        ∷ testedShellMagnitude cell
        ∷ [])))

sumShellCommutatorTax : List DyadicCommutatorTaxCell → ℚ
sumShellCommutatorTax [] = zeroQ
sumShellCommutatorTax (cell ∷ rest) =
  shellCommutatorTax cell + sumShellCommutatorTax rest

sumMotherCommutatorTax : List DyadicCommutatorTaxCell → ℚ
sumMotherCommutatorTax [] = zeroQ
sumMotherCommutatorTax (cell ∷ rest) =
  motherCommutatorTax cell + sumMotherCommutatorTax rest

finiteCutoffIndependentCommutatorTax :
  (cells : List DyadicCommutatorTaxCell) →
  sumShellCommutatorTax cells ≡ sumMotherCommutatorTax cells
finiteCutoffIndependentCommutatorTax [] = refl
finiteCutoffIndependentCommutatorTax (cell ∷ rest)
  rewrite cutoffIndependentCommutatorCellCoefficient cell
        | finiteCutoffIndependentCommutatorTax rest = refl

record DyadicScalePair : Set where
  constructor dyadic-scale-pair
  field
    inversePower directPower : ℚ
    inverseLaw : inversePower * directPower ≡ oneQ

open DyadicScalePair public

unitScalePair : DyadicScalePair
unitScalePair = dyadic-scale-pair oneQ oneQ refl

halfDoubleScalePair : DyadicScalePair
halfDoubleScalePair =
  dyadic-scale-pair (Int.+ 1 / 2) (Int.+ 2 / 1) (solve [])

quarterFourScalePair : DyadicScalePair
quarterFourScalePair =
  dyadic-scale-pair (Int.+ 1 / 4) (Int.+ 4 / 1) (solve [])

cellAtScale :
  DyadicScalePair → ℚ → ℚ → ℚ → ℚ → DyadicCommutatorTaxCell
cellAtScale scale moment low high tested =
  dyadic-commutator-tax-cell
    (inversePower scale)
    (directPower scale)
    (inverseLaw scale)
    moment low high tested

halfDoubleTaxIsMotherTax :
  (moment low high tested : ℚ) →
  shellCommutatorTax
    (cellAtScale halfDoubleScalePair moment low high tested)
  ≡ moment * low * high * tested
halfDoubleTaxIsMotherTax moment low high tested =
  cutoffIndependentCommutatorCellCoefficient
    (cellAtScale halfDoubleScalePair moment low high tested)

quarterFourTaxIsMotherTax :
  (moment low high tested : ℚ) →
  shellCommutatorTax
    (cellAtScale quarterFourScalePair moment low high tested)
  ≡ moment * low * high * tested
quarterFourTaxIsMotherTax moment low high tested =
  cutoffIndependentCommutatorCellCoefficient
    (cellAtScale quarterFourScalePair moment low high tested)
