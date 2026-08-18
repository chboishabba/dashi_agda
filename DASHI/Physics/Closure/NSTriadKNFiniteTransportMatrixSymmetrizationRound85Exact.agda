module DASHI.Physics.Closure.NSTriadKNFiniteTransportMatrixSymmetrizationRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND85 / FINITE MATRIX ASSEMBLY OF T* + T = D
--
-- Round40 and the pressure Round85 lane both reach the same entrywise object:
--
--   conjugate(T_qk) + T_kq = D_kq.
--
-- This module supplies the missing finite matrix assembly.  For any finite
-- list of Fourier modes and vector amplitudes u_k,
--
--   sum_{k,q} Re <u_k,D_kq u_q>
--     = 2 sum_{k,q} Re <u_k,T_kq u_q>.
--
-- The proof does not choose unordered representatives.  It proves a generic
-- finite double-sum transpose identity and sums the exact pairwise energy
-- defect over all ordered pairs.  Therefore:
--
--   * D=0 closes finite matrix skew-adjoint transport from entrywise skew;
--   * pressure D=-h gives the exact half-Poisson quadratic form once the
--     concrete pressure transport coefficients are instantiated.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNTransportPairEnergyDefectRound85Exact as Pair

sumModes :
  ∀ {r} (F : C3.RealField r) →
  List Z3.FourierMode →
  (Z3.FourierMode → C3.Carrier F) →
  C3.Carrier F
sumModes F [] value = C3.zero F
sumModes F (mode ∷ modes) value =
  C3.add F (value mode) (sumModes F modes value)

sumModesAdd :
  ∀ {r} (F : C3.RealField r)
    (modes : List Z3.FourierMode)
    (left right : Z3.FourierMode → C3.Carrier F) →
  sumModes F modes (λ mode → C3.add F (left mode) (right mode))
  ≡ C3.add F (sumModes F modes left) (sumModes F modes right)
sumModesAdd F [] left right =
  sym (C3.addZeroLeft F (C3.zero F))
sumModesAdd {r} F (mode ∷ modes) left right =
  trans
    (cong
      (C3.add F (C3.add F (left mode) (right mode)))
      (sumModesAdd F modes left right))
    (P.R.solve 4
      (λ a b c d →
        ((a P.R.⊕ b) P.R.⊕ (c P.R.⊕ d))
        P.R.⊜ ((a P.R.⊕ c) P.R.⊕ (b P.R.⊕ d)))
      refl
      (left mode) (right mode)
      (sumModes F modes left) (sumModes F modes right))
  where
  module P = Field.Polynomial F

rowSum :
  ∀ {r} (F : C3.RealField r) →
  List Z3.FourierMode →
  (Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  Z3.FourierMode → C3.Carrier F
rowSum F modes value row =
  sumModes F modes (value row)

doubleSum :
  ∀ {r} (F : C3.RealField r) →
  List Z3.FourierMode →
  (Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  C3.Carrier F
doubleSum F modes value =
  sumModes F modes (rowSum F modes value)

transpose :
  ∀ {r} {F : C3.RealField r} →
  (Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  Z3.FourierMode → Z3.FourierMode → C3.Carrier F
transpose value left right = value right left

sumRowsWithNewColumn :
  ∀ {r} (F : C3.RealField r)
    (head : Z3.FourierMode)
    (modes : List Z3.FourierMode)
    (value : Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  sumModes F modes
    (λ row → C3.add F (value row head) (rowSum F modes value row))
  ≡ C3.add F
      (sumModes F modes (λ row → value row head))
      (doubleSum F modes value)
sumRowsWithNewColumn F head modes value =
  sumModesAdd F modes
    (λ row → value row head)
    (rowSum F modes value)

doubleSumConsExpansion :
  ∀ {r} (F : C3.RealField r)
    (head : Z3.FourierMode)
    (modes : List Z3.FourierMode)
    (value : Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  doubleSum F (head ∷ modes) value
  ≡ C3.add F
      (C3.add F
        (value head head)
        (sumModes F modes (λ col → value head col)))
      (C3.add F
        (sumModes F modes (λ row → value row head))
        (doubleSum F modes value))
doubleSumConsExpansion F head modes value =
  cong
    (C3.add F
      (C3.add F
        (value head head)
        (sumModes F modes (λ col → value head col))))
    (sumRowsWithNewColumn F head modes value)

doubleSumTranspose :
  ∀ {r} (F : C3.RealField r)
    (modes : List Z3.FourierMode)
    (value : Z3.FourierMode → Z3.FourierMode → C3.Carrier F) →
  doubleSum F modes (transpose value) ≡ doubleSum F modes value
doubleSumTranspose F [] value = refl
doubleSumTranspose {r} F (head ∷ modes) value =
  trans
    (doubleSumConsExpansion F head modes (transpose value))
    (trans
      (cong
        (λ tail →
          C3.add F
            (C3.add F
              (value head head)
              (sumModes F modes (λ row → value row head)))
            (C3.add F
              (sumModes F modes (λ col → value head col))
              tail))
        (doubleSumTranspose F modes value))
      (trans
        (P.R.solve 4
          (λ diagonal column row tail →
            ((diagonal P.R.⊕ column) P.R.⊕ (row P.R.⊕ tail))
            P.R.⊜ ((diagonal P.R.⊕ row) P.R.⊕ (column P.R.⊕ tail)))
          refl
          (value head head)
          (sumModes F modes (λ row → value row head))
          (sumModes F modes (λ col → value head col))
          (doubleSum F modes value))
        (sym (doubleSumConsExpansion F head modes value))))
  where
  module P = Field.Polynomial F

------------------------------------------------------------------------
-- Finite transport matrix energy assembly.
------------------------------------------------------------------------

record FiniteTransportAdjointDatum {r : Level} (F : C3.RealField r) : Set (Level.suc r) where
  field
    modes : List Z3.FourierMode
    velocity : Z3.FourierMode → C3.Complex3 F
    transport defect : Z3.FourierMode → Z3.FourierMode → C3.Complex F

    entryAdjointDefect : ∀ output input →
      C3.complexAdd
        (C3.complexConjugate (transport input output))
        (transport output input)
      ≡ defect output input

open FiniteTransportAdjointDatum public

energyEntry :
  ∀ {r} {F : C3.RealField r} →
  FiniteTransportAdjointDatum F →
  Z3.FourierMode → Z3.FourierMode → C3.Carrier F
energyEntry datum output input =
  C3.real
    (Pair.forwardEnergy
      (transport datum output input)
      (velocity datum output)
      (velocity datum input))

defectEntry :
  ∀ {r} {F : C3.RealField r} →
  FiniteTransportAdjointDatum F →
  Z3.FourierMode → Z3.FourierMode → C3.Carrier F
defectEntry datum output input =
  C3.real
    (Pair.defectEnergy
      (defect datum output input)
      (velocity datum output)
      (velocity datum input))

entryEnergyPairEqualsDefect :
  ∀ {r} {F : C3.RealField r}
    (datum : FiniteTransportAdjointDatum F)
    output input →
  C3.add F
    (energyEntry datum output input)
    (energyEntry datum input output)
  ≡ defectEntry datum output input
entryEnergyPairEqualsDefect {F = F} datum output input =
  trans
    refl
    (Pair.pairEnergyDefectExact
      (transport datum output input)
      (transport datum input output)
      (defect datum output input)
      (velocity datum output)
      (velocity datum input)
      (entryAdjointDefect datum output input))

finiteTransportDefectEqualsTwiceEnergy :
  ∀ {r} {F : C3.RealField r}
    (datum : FiniteTransportAdjointDatum F) →
  doubleSum F (modes datum) (defectEntry datum)
  ≡ C3.add F
      (doubleSum F (modes datum) (energyEntry datum))
      (doubleSum F (modes datum) (energyEntry datum))
finiteTransportDefectEqualsTwiceEnergy {F = F} datum =
  let
    modes₀ = modes datum
    energy = energyEntry datum
    defect₀ = defectEntry datum

    pointwise : ∀ output input →
      C3.add F (energy output input) (transpose energy output input)
      ≡ defect₀ output input
    pointwise output input = entryEnergyPairEqualsDefect datum output input

    sumPointwiseRows : ∀ output →
      sumModes F modes₀
        (λ input → C3.add F (energy output input) (transpose energy output input))
      ≡ sumModes F modes₀ (defect₀ output)
    sumPointwiseRows output =
      sumCong modes₀
        (λ input → C3.add F (energy output input) (transpose energy output input))
        (defect₀ output)
        (pointwise output)
      where
      sumCong :
        (xs : List Z3.FourierMode) →
        (left right : Z3.FourierMode → C3.Carrier F) →
        (∀ mode → left mode ≡ right mode) →
        sumModes F xs left ≡ sumModes F xs right
      sumCong [] left right agree = refl
      sumCong (mode ∷ rest) left right agree =
        cong₂ (C3.add F) (agree mode) (sumCong rest left right agree)

    allPointwise :
      doubleSum F modes₀
        (λ output input → C3.add F (energy output input) (transpose energy output input))
      ≡ doubleSum F modes₀ defect₀
    allPointwise =
      sumCongOuter modes₀ sumPointwiseRows
      where
      sumCongOuter :
        (xs : List Z3.FourierMode) →
        (∀ output →
          sumModes F modes₀
            (λ input → C3.add F (energy output input) (transpose energy output input))
          ≡ sumModes F modes₀ (defect₀ output)) →
        sumModes F xs
          (λ output →
            sumModes F modes₀
              (λ input → C3.add F (energy output input) (transpose energy output input)))
        ≡ sumModes F xs (λ output → sumModes F modes₀ (defect₀ output))
      sumCongOuter [] agree = refl
      sumCongOuter (output ∷ rest) agree =
        cong₂ (C3.add F) (agree output) (sumCongOuter rest agree)

    splitSum :
      doubleSum F modes₀
        (λ output input → C3.add F (energy output input) (transpose energy output input))
      ≡ C3.add F
          (doubleSum F modes₀ energy)
          (doubleSum F modes₀ (transpose energy))
    splitSum =
      trans
        (sumCongOuter modes₀)
        (sumModesAdd F modes₀
          (rowSum F modes₀ energy)
          (rowSum F modes₀ (transpose energy)))
      where
      sumCongOuter :
        sumModes F modes₀
          (λ output →
            sumModes F modes₀
              (λ input → C3.add F (energy output input) (transpose energy output input)))
        ≡ sumModes F modes₀
            (λ output →
              C3.add F
                (rowSum F modes₀ energy output)
                (rowSum F modes₀ (transpose energy) output))
      sumCongOuter =
        sumRows modes₀
        where
        sumRows :
          (xs : List Z3.FourierMode) →
          sumModes F xs
            (λ output →
              sumModes F modes₀
                (λ input → C3.add F (energy output input) (transpose energy output input)))
          ≡ sumModes F xs
              (λ output →
                C3.add F
                  (rowSum F modes₀ energy output)
                  (rowSum F modes₀ (transpose energy) output))
        sumRows [] = refl
        sumRows (output ∷ rest) =
          cong₂ (C3.add F)
            (sumModesAdd F modes₀
              (energy output) ((transpose energy) output))
            (sumRows rest)
  in
  trans
    (sym allPointwise)
    (trans
      splitSum
      (cong
        (C3.add F (doubleSum F modes₀ energy))
        (doubleSumTranspose F modes₀ energy)))

round85FiniteDoubleSumTransposeConstructed : Bool
round85FiniteDoubleSumTransposeConstructed = true

round85FiniteTransportMatrixSymmetrizationConstructed : Bool
round85FiniteTransportMatrixSymmetrizationConstructed = true

round85FiniteTransportMatrixSymmetrizationConstructedIsTrue :
  round85FiniteTransportMatrixSymmetrizationConstructed ≡ true
round85FiniteTransportMatrixSymmetrizationConstructedIsTrue = refl
