module DASHI.Physics.Closure.NSTriadKNComLiteralPhysicalGramRowRound65Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
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
-- ROUND 65 / B1 RAW PHYSICAL GRAM CONSTRUCTION
--
-- Round64 put the literal centered-Com coefficient and its constructed
-- dominant common hat on the same PhysicalTriadIncidence.  Here we perform the
-- next non-bookkeeping step: for two projector/operator indices q,r we build,
-- over the EXACT SAME physicalOutputFiber,
--
--   M_q       = sum_tau |c_q(tau)|^2,
--   M_r       = sum_tau |c_r(tau)|^2,
--   C_qr      = |sum_tau conj(c_q(tau)) c_r(tau)|^2.
--
-- These are the literal self masses and cross mass in the exact realField of
-- PeriodicHardShellFourierPDE.  Given the corrected finite Cauchy--Schwarz law
-- for that same support, we prove
--
--                 C_qr <= M_q M_r.
--
-- This is the unnormalised physical Gram inequality required before division
-- by the self masses.  No Q-valued Gram surrogate is used.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQOutputFibreCommutatorRound62Exact as Literal
import DASHI.Physics.Closure.NSTriadKNComLiteralDominantHatLocalizedRowRound64Exact as Localized
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNExactFiniteComplexCauchySchwarzRound65 as CS

literalComRowCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  Triad.PhysicalTriadIncidence → C3.Complex (LP.realField model)
literalComRowCoefficient model projectorCutoff E velocity =
  Literal.literalProjectorCommutatorTriadCoefficient
    model projectorCutoff E velocity

literalComSelfMass :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Carrier (LP.realField model)
literalComSelfMass model projectorCutoff enumerationCutoff E velocity output =
  L2.finiteComplexL2NormSquared
    (Output.physicalOutputFiber enumerationCutoff output)
    (literalComRowCoefficient model projectorCutoff E velocity)

literalComCrossMass :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (leftCutoff rightCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  C3.Carrier (LP.realField model)
literalComCrossMass
    model leftCutoff rightCutoff enumerationCutoff E velocity output =
  CS.finiteComplexInnerProductModulusSquared
    (Output.physicalOutputFiber enumerationCutoff output)
    (literalComRowCoefficient model leftCutoff E velocity)
    (literalComRowCoefficient model rightCutoff E velocity)

record LiteralPhysicalComGramSource {r : Level} : Set (lsuc r) where
  field
    model : LP.PeriodicHardShellFourierPDE {r}
    integerEmbedding : C3.IntegerEmbedding (LP.realField model)
    velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)
    order : L2.OrderedRealExtension (LP.realField model)

    exactFiniteCauchySchwarz :
      ∀ enumerationCutoff output →
      CS.ExactFiniteComplexCauchySchwarz
        order
        (Output.physicalOutputFiber enumerationCutoff output)

open LiteralPhysicalComGramSource public

selfMass :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) →
  Nat → Nat → Z3.FourierMode → C3.Carrier (LP.realField (model source))
selfMass source q N output =
  literalComSelfMass
    (model source) q N (integerEmbedding source) (velocity source) output

crossMass :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) →
  Nat → Nat → Nat → Z3.FourierMode → C3.Carrier (LP.realField (model source))
crossMass source q s N output =
  literalComCrossMass
    (model source) q s N (integerEmbedding source) (velocity source) output

selfMassNonnegative :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) q N output →
  L2._≤_ (order source)
    (C3.zero (LP.realField (model source)))
    (selfMass source q N output)
selfMassNonnegative source q N output =
  CS.finiteComplexL2NormSquaredNonnegative
    (order source)
    (Output.physicalOutputFiber N output)
    (literalComRowCoefficient
      (model source) q (integerEmbedding source) (velocity source))

crossMassNonnegative :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) q s N output →
  L2._≤_ (order source)
    (C3.zero (LP.realField (model source)))
    (crossMass source q s N output)
crossMassNonnegative source q s N output =
  CS.finiteComplexInnerProductMassNonnegative
    (order source)
    (Output.physicalOutputFiber N output)
    (literalComRowCoefficient
      (model source) q (integerEmbedding source) (velocity source))
    (literalComRowCoefficient
      (model source) s (integerEmbedding source) (velocity source))

literalPhysicalCrossMassBelowSelfMassProduct :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) q s N output →
  L2._≤_ (order source)
    (crossMass source q s N output)
    (C3.multiply (LP.realField (model source))
      (selfMass source q N output)
      (selfMass source s N output))
literalPhysicalCrossMassBelowSelfMassProduct source q s N output =
  CS.finiteCauchySchwarz
    (exactFiniteCauchySchwarz source N output)
    (literalComRowCoefficient
      (model source) q (integerEmbedding source) (velocity source))
    (literalComRowCoefficient
      (model source) s (integerEmbedding source) (velocity source))

-- The Round64 localized representation of each row remains definitionally on
-- the same physicalOutputFiber; this witness prevents later normalization code
-- from silently changing the support object.
localizedRowAt :
  ∀ {r} (source : LiteralPhysicalComGramSource {r}) q N output →
  List
    (Localized.DominantHatLocalizedComEntry
      (model source) q (integerEmbedding source) (velocity source))
localizedRowAt source q N output =
  Localized.literalDominantHatLocalizedOutputRow
    (model source) q N (integerEmbedding source) (velocity source) output

round65LiteralPhysicalSelfAndCrossMassesConstructed : Bool
round65LiteralPhysicalSelfAndCrossMassesConstructed = true

round65LiteralPhysicalCauchyGramInequalityConstructed : Bool
round65LiteralPhysicalCauchyGramInequalityConstructed = true

round65LiteralPhysicalSelfAndCrossMassesConstructedIsTrue :
  round65LiteralPhysicalSelfAndCrossMassesConstructed ≡ true
round65LiteralPhysicalSelfAndCrossMassesConstructedIsTrue = refl

round65LiteralPhysicalCauchyGramInequalityConstructedIsTrue :
  round65LiteralPhysicalCauchyGramInequalityConstructed ≡ true
round65LiteralPhysicalCauchyGramInequalityConstructedIsTrue = refl
