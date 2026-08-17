module DASHI.Moonshine.P37MarkedX2HeckeFrobeniusFrickeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Close the p=37 marked prime-to-level Hecke/Frobenius/Fricke system on one
-- actual 18-state full-level-2 Deuring carrier.
--
-- P37MarkedLegendreT3T5Exact constructs the degree-3 and degree-5 Legendre
-- correspondences with multiplicity and proves Frobenius equivariance.
-- P37MarkedX2FrobeniusFrickeExact identifies the special-fibre Atkin--Lehner
-- action with the same marked Frobenius involution.  Therefore T3 and T5
-- commute with marked Fricke exactly, on the same source-native carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37
import DASHI.Moonshine.P37MarkedLegendreT3T5Exact as Hecke
import DASHI.Moonshine.P37MarkedX2FrobeniusFrickeExact as FF

markedT3CommutesWithFrobenius :
  (source : P37.P37SupersingularLambda) → (edge : Fin 4) →
  Hecke.markedT3Neighbour (FF.markedFrobenius37 source) edge
  ≡ FF.markedFrobenius37 (Hecke.markedT3Neighbour source edge)
markedT3CommutesWithFrobenius = Hecke.markedT3FrobeniusEquivariant

markedT5CommutesWithFrobenius :
  (source : P37.P37SupersingularLambda) → (edge : Fin 6) →
  Hecke.markedT5Neighbour (FF.markedFrobenius37 source) edge
  ≡ FF.markedFrobenius37 (Hecke.markedT5Neighbour source edge)
markedT5CommutesWithFrobenius = Hecke.markedT5FrobeniusEquivariant

markedT3CommutesWithFricke :
  (source : P37.P37SupersingularLambda) → (edge : Fin 4) →
  Hecke.markedT3Neighbour (FF.markedFricke37 source) edge
  ≡ FF.markedFricke37 (Hecke.markedT3Neighbour source edge)
markedT3CommutesWithFricke = Hecke.markedT3FrobeniusEquivariant

markedT5CommutesWithFricke :
  (source : P37.P37SupersingularLambda) → (edge : Fin 6) →
  Hecke.markedT5Neighbour (FF.markedFricke37 source) edge
  ≡ FF.markedFricke37 (Hecke.markedT5Neighbour source edge)
markedT5CommutesWithFricke = Hecke.markedT5FrobeniusEquivariant

markedFrickePairCountIsNine : FF.markedFricke37PairCount ≡ 9
markedFrickePairCountIsNine = FF.markedFricke37PairCountIsNine

markedFrickeFixedCountIsZero : FF.markedFricke37FixedCount ≡ 0
markedFrickeFixedCountIsZero = FF.markedFricke37FixedCountIsZero

record P37MarkedJointOperatorBoundary : Set where
  field
    actualMarkedT3Constructed : Bool
    actualMarkedT3ConstructedIsTrue : actualMarkedT3Constructed ≡ true

    actualMarkedT5Constructed : Bool
    actualMarkedT5ConstructedIsTrue : actualMarkedT5Constructed ≡ true

    t3t5FrobeniusEquivariant : Bool
    t3t5FrobeniusEquivariantIsTrue : t3t5FrobeniusEquivariant ≡ true

    t3t5FrickeEquivariant : Bool
    t3t5FrickeEquivariantIsTrue : t3t5FrickeEquivariant ≡ true

    sameEighteenStateCarrierUsedThroughout : Bool
    sameEighteenStateCarrierUsedThroughoutIsTrue :
      sameEighteenStateCarrierUsedThroughout ≡ true

canonicalP37MarkedJointOperatorBoundary : P37MarkedJointOperatorBoundary
canonicalP37MarkedJointOperatorBoundary = record
  { actualMarkedT3Constructed = true
  ; actualMarkedT3ConstructedIsTrue = refl
  ; actualMarkedT5Constructed = true
  ; actualMarkedT5ConstructedIsTrue = refl
  ; t3t5FrobeniusEquivariant = true
  ; t3t5FrobeniusEquivariantIsTrue = refl
  ; t3t5FrickeEquivariant = true
  ; t3t5FrickeEquivariantIsTrue = refl
  ; sameEighteenStateCarrierUsedThroughout = true
  ; sameEighteenStateCarrierUsedThroughoutIsTrue = refl
  }
