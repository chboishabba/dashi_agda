module DASHI.Physics.Plasma.MHDElsasserSkewToInvariantCompilerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDElsasserCouplingExchangeAntisymmetryExact as A
import DASHI.Physics.Plasma.MHDElsasserThreeOutputSkewDecompositionBidiExact as D

------------------------------------------------------------------------
-- SKEW-DECOMPOSITION -> IDEAL-INVARIANT COMPILER SOCKET
--
-- Once plus and minus pseudo-energy variations are each decomposed into
-- pairwise antisymmetric transfers on the same literal triad, total energy and
-- cross helicity are downstream algebraic consumers of those two balances.
------------------------------------------------------------------------

record PseudoEnergyConservationReceipt
    (coupling : A.ElsasserCouplingExchange) : Set₁ where
  constructor pseudo-energy-conservation-receipt
  field
    plusDecomposition : D.ThreeOutputSkewDecomposition coupling
    minusDecomposition : D.ThreeOutputSkewDecomposition coupling
    plusSpeciesReceipt : D.species plusDecomposition ≡ D.plusSpecies
    minusSpeciesReceipt : D.species minusDecomposition ≡ D.minusSpecies
    sameLiteralTriadAcrossSpecies : Set
    plusCyclicVariationZero : Set
    minusCyclicVariationZero : Set
    pseudoEnergyReference : String

open PseudoEnergyConservationReceipt public

record EnergyCrossHelicityCompilerReceipt
    (coupling : A.ElsasserCouplingExchange) : Set₁ where
  constructor energy-cross-helicity-compiler-receipt
  field
    pseudoEnergyReceipt : PseudoEnergyConservationReceipt coupling
    coordinateVariationIdentityReceipt : Set
    totalEnergyCyclicVariationZero : Set
    crossHelicityCyclicVariationZero : Set
    compilerReference : String

open EnergyCrossHelicityCompilerReceipt public

record SkewInvariantCompilerBoundary : Set where
  constructor skew-invariant-compiler-boundary
  field
    plusPseudoEnergyAloneClosesCrossHelicity : Bool
    plusPseudoEnergyAloneClosesCrossHelicityIsFalse :
      plusPseudoEnergyAloneClosesCrossHelicity ≡ false

    plusAndMinusBalancesCanCompileEnergyAndCrossHelicity : Bool
    plusAndMinusBalancesCanCompileEnergyAndCrossHelicityIsTrue :
      plusAndMinusBalancesCanCompileEnergyAndCrossHelicity ≡ true

    thisCompilerClosesMagneticHelicity : Bool
    thisCompilerClosesMagneticHelicityIsFalse :
      thisCompilerClosesMagneticHelicity ≡ false

canonicalSkewInvariantCompilerBoundary : SkewInvariantCompilerBoundary
canonicalSkewInvariantCompilerBoundary =
  skew-invariant-compiler-boundary false refl true refl false refl
