module DASHI.Physics.Closure.NSTriadKNLuoFiniteDirectionalHHBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations aux
-- derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Shin-ichi Inage,
-- "Conditional Regularity of the Three-Dimensional Navier-Stokes Equations
-- via High-High Triadic Absorption".
-- DOI: 10.20944/preprints202603.1591.v1.
-- Status: non-peer-reviewed preprint.
--
-- DASHI CONTRIBUTION
--
-- A finite high-high shell is represented by literal kernel cells.  Each cell
-- carries a nonnegative kernel weight and the exact unit-radial triple product
-- from the directional-kernel module.  The checked pointwise inequality
--
--   triple^2 <= a^2 b^2 Theta
--
-- is multiplied by the kernel weight and summed recursively.  Therefore the
-- finite squared high-high transfer is controlled by the literal weighted
-- directional-defect envelope, with constant one at this algebraic stage.
--
-- This is a genuine P4 finite producer.  The continuum annular kernel,
-- principal-value limit, physical normalization and conversion from the
-- squared shell envelope to a strict viscosity coefficient remain separate
-- analytic tasks.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalKernelTripleProductExact as Triple

record DirectionalHHCell : Set where
  constructor directionalHHCell
  field
    geometry : Triple.UnitRadialPhysicalPair
    kernelWeight : ℚ
    kernelWeightNonnegative : 0ℚ ≤ kernelWeight

open DirectionalHHCell public

cellTransferSquared : DirectionalHHCell → ℚ
cellTransferSquared cell =
  kernelWeight cell
  * L2.square (Triple.physicalTriple (geometry cell))

cellDirectionalEnvelope : DirectionalHHCell → ℚ
cellDirectionalEnvelope cell =
  let pair = Triple.vorticityPair (geometry cell)
  in
  kernelWeight cell
  *
  ( L2.square (Physical.leftAmplitude pair)
    * L2.square (Physical.rightAmplitude pair)
    * Gram.directionalDefect (Physical.directions pair)
  )

cellTransferBelowDirectionalEnvelope :
  ∀ cell →
  cellTransferSquared cell ≤ cellDirectionalEnvelope cell
cellTransferBelowDirectionalEnvelope cell =
  let
    pair = Triple.vorticityPair (geometry cell)
    transfer = L2.square (Triple.physicalTriple (geometry cell))
    envelope =
      L2.square (Physical.leftAmplitude pair)
      * L2.square (Physical.rightAmplitude pair)
      * Gram.directionalDefect (Physical.directions pair)

    base : transfer ≤ envelope
    base = Triple.physicalDirectionalTripleBound (geometry cell)

    transferNonnegative : 0ℚ ≤ transfer
    transferNonnegative =
      L2.squareNonnegative (Triple.physicalTriple (geometry cell))

    envelopeNonnegative : 0ℚ ≤ envelope
    envelopeNonnegative =
      let
        leftSquare = L2.square (Physical.leftAmplitude pair)
        rightSquare = L2.square (Physical.rightAmplitude pair)
        defect = Gram.directionalDefect (Physical.directions pair)

        instance
          leftNN = nonNegative (L2.squareNonnegative (Physical.leftAmplitude pair))
          rightNN = nonNegative (L2.squareNonnegative (Physical.rightAmplitude pair))
          firstProductNN = ℚₚ.nonNeg*nonNeg⇒nonNeg leftSquare rightSquare
          defectNN = nonNegative (Gram.directionalDefectNonnegative (Physical.directions pair))
          secondProductNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (leftSquare * rightSquare) defect
      in
      ℚₚ.nonNegative⁻¹ envelope
  in
  L2.nonnegativeProductMonotone
    (kernelWeightNonnegative cell)
    transferNonnegative
    (kernelWeightNonnegative cell)
    envelopeNonnegative
    ℚₚ.≤-refl
    base

finiteHHTransferSquared : List DirectionalHHCell → ℚ
finiteHHTransferSquared [] = 0ℚ
finiteHHTransferSquared (cell ∷ cells) =
  cellTransferSquared cell + finiteHHTransferSquared cells

finiteDirectionalEnvelope : List DirectionalHHCell → ℚ
finiteDirectionalEnvelope [] = 0ℚ
finiteDirectionalEnvelope (cell ∷ cells) =
  cellDirectionalEnvelope cell + finiteDirectionalEnvelope cells

finiteDirectionalHHSquaredBridge :
  ∀ cells →
  finiteHHTransferSquared cells ≤ finiteDirectionalEnvelope cells
finiteDirectionalHHSquaredBridge [] = ℚₚ.≤-refl
finiteDirectionalHHSquaredBridge (cell ∷ cells) =
  ℚₚ.+-mono-≤
    (cellTransferBelowDirectionalEnvelope cell)
    (finiteDirectionalHHSquaredBridge cells)

record FiniteDirectionalAbsorptionInput : Set where
  constructor finiteDirectionalAbsorptionInput
  field
    cells : List DirectionalHHCell
    eta viscosity residual : ℚ
    envelopeAbsorption :
      finiteDirectionalEnvelope cells ≤ eta * viscosity + residual

open FiniteDirectionalAbsorptionInput public

finiteDirectionalHHAbsorption :
  ∀ input →
  finiteHHTransferSquared (cells input)
  ≤ eta input * viscosity input + residual input
finiteDirectionalHHAbsorption input =
  ℚₚ.≤-trans
    (finiteDirectionalHHSquaredBridge (cells input))
    (envelopeAbsorption input)

record FiniteDirectionalHHBoundary : Set where
  constructor finiteDirectionalHHBoundary
  field
    pointwiseDirectionalFactorProved : Set
    finiteKernelCellSummationProved : Set
    physicalContinuumKernelProducerProved : Set
    strictViscosityCoefficientProduced : Set

canonicalFiniteDirectionalHHBoundary : FiniteDirectionalHHBoundary
canonicalFiniteDirectionalHHBoundary =
  finiteDirectionalHHBoundary ⊤ ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
