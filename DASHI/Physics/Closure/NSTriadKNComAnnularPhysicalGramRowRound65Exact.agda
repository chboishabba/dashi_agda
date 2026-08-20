module DASHI.Physics.Closure.NSTriadKNComAnnularPhysicalGramRowRound65Exact where

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
-- ROUND 65 / CORRECT OPERATOR-INDEX RAW GRAM
--
-- The six-three same/adjacent indices belong to the annular/operator lane, not
-- to raw nested low-pass cutoffs.  Round63 already constructed the literal
-- annular commutator coefficient A_s on the exact physicalOutputFiber.
--
-- Here we build its exact same-carrier Gram masses for shell indices q,r:
--
--   M_q  = sum |A_q(tau)|^2,
--   M_r  = sum |A_r(tau)|^2,
--   C_qr = |sum conj(A_q(tau)) A_r(tau)|^2,
--
-- and derive C_qr <= M_q M_r from the corrected finite Hermitian
-- Cauchy--Schwarz interface.  This is the raw physical annular Gram object that
-- a genuine B1 factorization must consume.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularOutputFibreRound63Exact as Annular
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 as CS

annularComSelfMass :
  ∀ {r} (F : C3.RealField r)
    (shell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  C3.Carrier F
annularComSelfMass F shell N E velocity output =
  L2.finiteComplexL2NormSquared
    (Output.physicalOutputFiber N output)
    (Annular.annularTriadCoefficient F shell E velocity)

annularComCrossMass :
  ∀ {r} (F : C3.RealField r)
    (leftShell rightShell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  C3.Carrier F
annularComCrossMass F q s N E velocity output =
  CS.finiteComplexInnerProductModulusSquared
    (Output.physicalOutputFiber N output)
    (Annular.annularTriadCoefficient F q E velocity)
    (Annular.annularTriadCoefficient F s E velocity)

record AnnularPhysicalComGramSource {r : Level} : Set (lsuc r) where
  field
    realField : C3.RealField r
    integerEmbedding : C3.IntegerEmbedding realField
    velocity : Z3.FourierMode → C3.Complex3 realField
    order : L2.OrderedRealExtension realField

    exactFiniteCauchySchwarz :
      ∀ enumerationCutoff output →
      CS.ExactFiniteComplexCauchySchwarz
        order
        (Output.physicalOutputFiber enumerationCutoff output)

open AnnularPhysicalComGramSource public

selfMass :
  ∀ {r} (source : AnnularPhysicalComGramSource {r}) →
  Nat → Nat → Z3.FourierMode → C3.Carrier (realField source)
selfMass source shell N output =
  annularComSelfMass
    (realField source) shell N
    (integerEmbedding source) (velocity source) output

crossMass :
  ∀ {r} (source : AnnularPhysicalComGramSource {r}) →
  Nat → Nat → Nat → Z3.FourierMode → C3.Carrier (realField source)
crossMass source q s N output =
  annularComCrossMass
    (realField source) q s N
    (integerEmbedding source) (velocity source) output

annularSelfMassNonnegative :
  ∀ {r} (source : AnnularPhysicalComGramSource {r}) shell N output →
  L2._≤_ (order source)
    (C3.zero (realField source))
    (selfMass source shell N output)
annularSelfMassNonnegative source shell N output =
  CS.finiteComplexL2NormSquaredNonnegative
    (order source)
    (Output.physicalOutputFiber N output)
    (Annular.annularTriadCoefficient
      (realField source) shell (integerEmbedding source) (velocity source))

annularCrossMassNonnegative :
  ∀ {r} (source : AnnularPhysicalComGramSource {r}) q s N output →
  L2._≤_ (order source)
    (C3.zero (realField source))
    (crossMass source q s N output)
annularCrossMassNonnegative source q s N output =
  CS.finiteComplexInnerProductMassNonnegative
    (order source)
    (Output.physicalOutputFiber N output)
    (Annular.annularTriadCoefficient
      (realField source) q (integerEmbedding source) (velocity source))
    (Annular.annularTriadCoefficient
      (realField source) s (integerEmbedding source) (velocity source))

annularPhysicalCrossMassBelowSelfMassProduct :
  ∀ {r} (source : AnnularPhysicalComGramSource {r}) q s N output →
  L2._≤_ (order source)
    (crossMass source q s N output)
    (C3.multiply (realField source)
      (selfMass source q N output)
      (selfMass source s N output))
annularPhysicalCrossMassBelowSelfMassProduct source q s N output =
  CS.finiteCauchySchwarz
    (exactFiniteCauchySchwarz source N output)
    (Annular.annularTriadCoefficient
      (realField source) q (integerEmbedding source) (velocity source))
    (Annular.annularTriadCoefficient
      (realField source) s (integerEmbedding source) (velocity source))

round65AnnularPhysicalGramMassesConstructed : Bool
round65AnnularPhysicalGramMassesConstructed = true

round65AnnularPhysicalCauchyBoundConstructed : Bool
round65AnnularPhysicalCauchyBoundConstructed = true

round65AnnularPhysicalGramMassesConstructedIsTrue :
  round65AnnularPhysicalGramMassesConstructed ≡ true
round65AnnularPhysicalGramMassesConstructedIsTrue = refl

round65AnnularPhysicalCauchyBoundConstructedIsTrue :
  round65AnnularPhysicalCauchyBoundConstructed ≡ true
round65AnnularPhysicalCauchyBoundConstructedIsTrue = refl
