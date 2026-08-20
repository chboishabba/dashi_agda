module DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title/context: finite Cauchy inequality / Schwarz inequality.
-- DOI: not applicable to the classical nineteenth-century results.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- ROUND 71 / FINITE CAUCHY CONCENTRATION BRIDGE
--
-- For the triadic physicalAtom values a_i in the ONE Round62 structured PDE
-- list, set S=sum a_i, M=sum a_i^2 and m=sum 1.  Exact finite squared Cauchy-
-- Schwarz on pairs (a_i,1) gives S^2 <= M*m.  Hence if 0<=mu<=R and the
-- SAME-OBJECT localized identity proves R=S, then mu^2 <= M*m.
--
-- No ambient Xi<=K bound, Carleman estimate, compactness theorem or positivity
-- of individual signed atoms is used.  Non-triadic terms must be separated or
-- estimated by the physical localized identity; they are not silently called
-- concentration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNLocalizedPDETriadicConcentrationMassRound69Exact as Mass
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

triadicSignedSum : List Structured.LocalizedPDEAtom → ℚ
triadicSignedSum [] = 0ℚ
triadicSignedSum
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) = value + triadicSignedSum rest
triadicSignedSum
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = triadicSignedSum rest
triadicSignedSum (Structured.tailAtom value ∷ rest) = triadicSignedSum rest
triadicSignedSum (Structured.duplicateKernelAtom value ∷ rest) = triadicSignedSum rest
triadicSignedSum
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = triadicSignedSum rest
triadicSignedSum (Structured.independentKernelAtom value ∷ rest) = triadicSignedSum rest
triadicSignedSum (Structured.lowerBoundaryAtom reason value ∷ rest) = triadicSignedSum rest
triadicSignedSum (Structured.upperBoundaryAtom reason value ∷ rest) = triadicSignedSum rest

triadicCount : List Structured.LocalizedPDEAtom → ℚ
triadicCount [] = 0ℚ
triadicCount
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) = 1ℚ + triadicCount rest
triadicCount
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = triadicCount rest
triadicCount (Structured.tailAtom value ∷ rest) = triadicCount rest
triadicCount (Structured.duplicateKernelAtom value ∷ rest) = triadicCount rest
triadicCount
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = triadicCount rest
triadicCount (Structured.independentKernelAtom value ∷ rest) = triadicCount rest
triadicCount (Structured.lowerBoundaryAtom reason value ∷ rest) = triadicCount rest
triadicCount (Structured.upperBoundaryAtom reason value ∷ rest) = triadicCount rest

triadicUnitPairs : List Structured.LocalizedPDEAtom → List L2.Pair
triadicUnitPairs [] = []
triadicUnitPairs
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest) = (value , 1ℚ) ∷ triadicUnitPairs rest
triadicUnitPairs
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = triadicUnitPairs rest
triadicUnitPairs (Structured.tailAtom value ∷ rest) = triadicUnitPairs rest
triadicUnitPairs (Structured.duplicateKernelAtom value ∷ rest) = triadicUnitPairs rest
triadicUnitPairs
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = triadicUnitPairs rest
triadicUnitPairs (Structured.independentKernelAtom value ∷ rest) = triadicUnitPairs rest
triadicUnitPairs (Structured.lowerBoundaryAtom reason value ∷ rest) = triadicUnitPairs rest
triadicUnitPairs (Structured.upperBoundaryAtom reason value ∷ rest) = triadicUnitPairs rest

pairDotIsTriadicSignedSum : ∀ atoms →
  L2.pairDot (triadicUnitPairs atoms) ≡ triadicSignedSum atoms
pairDotIsTriadicSignedSum [] = refl
pairDotIsTriadicSignedSum
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest)
  rewrite pairDotIsTriadicSignedSum rest = solve (value ∷ triadicSignedSum rest ∷ [])
pairDotIsTriadicSignedSum
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum (Structured.tailAtom value ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum (Structured.duplicateKernelAtom value ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum (Structured.independentKernelAtom value ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum (Structured.lowerBoundaryAtom reason value ∷ rest) = pairDotIsTriadicSignedSum rest
pairDotIsTriadicSignedSum (Structured.upperBoundaryAtom reason value ∷ rest) = pairDotIsTriadicSignedSum rest

leftNormIsTriadicMass : ∀ atoms →
  L2.leftNormSquared (triadicUnitPairs atoms) ≡ Mass.triadicConcentrationMass atoms
leftNormIsTriadicMass [] = refl
leftNormIsTriadicMass
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest)
  rewrite leftNormIsTriadicMass rest = refl
leftNormIsTriadicMass
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass (Structured.tailAtom value ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass (Structured.duplicateKernelAtom value ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass (Structured.independentKernelAtom value ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass (Structured.lowerBoundaryAtom reason value ∷ rest) = leftNormIsTriadicMass rest
leftNormIsTriadicMass (Structured.upperBoundaryAtom reason value ∷ rest) = leftNormIsTriadicMass rest

rightNormIsTriadicCount : ∀ atoms →
  L2.rightNormSquared (triadicUnitPairs atoms) ≡ triadicCount atoms
rightNormIsTriadicCount [] = refl
rightNormIsTriadicCount
    (Structured.physicalAtom (Support.triadicSource classified)
      selected compatible value ∷ rest)
  rewrite rightNormIsTriadicCount rest = solve (triadicCount rest ∷ [])
rightNormIsTriadicCount
    (Structured.physicalAtom (Support.differentiatedCommutator output)
      selected compatible value ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount (Structured.tailAtom value ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount (Structured.duplicateKernelAtom value ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount
    (Structured.cancellingKernelPair left right cancellation ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount (Structured.independentKernelAtom value ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount (Structured.lowerBoundaryAtom reason value ∷ rest) = rightNormIsTriadicCount rest
rightNormIsTriadicCount (Structured.upperBoundaryAtom reason value ∷ rest) = rightNormIsTriadicCount rest

triadicFiniteCauchy : ∀ atoms →
  L2.square (triadicSignedSum atoms)
  ≤ Mass.triadicConcentrationMass atoms * triadicCount atoms
triadicFiniteCauchy atoms =
  let
    base :
      L2.square (L2.pairDot (triadicUnitPairs atoms))
      ≤ L2.leftNormSquared (triadicUnitPairs atoms)
        * L2.rightNormSquared (triadicUnitPairs atoms)
    base = L2.finiteCauchySchwarzSquared (triadicUnitPairs atoms)

    dotStep :
      L2.square (triadicSignedSum atoms)
      ≤ L2.leftNormSquared (triadicUnitPairs atoms)
        * L2.rightNormSquared (triadicUnitPairs atoms)
    dotStep = subst
      (λ dot → L2.square dot
        ≤ L2.leftNormSquared (triadicUnitPairs atoms)
          * L2.rightNormSquared (triadicUnitPairs atoms))
      (pairDotIsTriadicSignedSum atoms)
      base

    leftStep :
      L2.square (triadicSignedSum atoms)
      ≤ Mass.triadicConcentrationMass atoms
        * L2.rightNormSquared (triadicUnitPairs atoms)
    leftStep = subst
      (λ leftMass → L2.square (triadicSignedSum atoms)
        ≤ leftMass * L2.rightNormSquared (triadicUnitPairs atoms))
      (leftNormIsTriadicMass atoms)
      dotStep
  in
  subst
    (λ rightMass → L2.square (triadicSignedSum atoms)
      ≤ Mass.triadicConcentrationMass atoms * rightMass)
    (rightNormIsTriadicCount atoms)
    leftStep

squareMonotoneNonnegative : ∀ {a b} →
  0ℚ ≤ a → 0ℚ ≤ b → a ≤ b → L2.square a ≤ L2.square b
squareMonotoneNonnegative {a} {b} aNN bNN a≤b =
  L2.nonnegativeProductMonotone aNN aNN bNN bNN a≤b a≤b

criticalRemainderForcesTriadicMassTimesCount :
  ∀ atoms remainder mu →
  0ℚ ≤ mu →
  mu ≤ remainder →
  remainder ≡ triadicSignedSum atoms →
  L2.square mu
    ≤ Mass.triadicConcentrationMass atoms * triadicCount atoms
criticalRemainderForcesTriadicMassTimesCount atoms remainder mu muNN forced sameObject =
  let
    sumNN : 0ℚ ≤ triadicSignedSum atoms
    sumNN = subst (0ℚ ≤_) sameObject (ℚP.≤-trans muNN forced)

    muBelowSum : mu ≤ triadicSignedSum atoms
    muBelowSum = subst (mu ≤_) sameObject forced
  in
  ℚP.≤-trans
    (squareMonotoneNonnegative muNN sumNN muBelowSum)
    (triadicFiniteCauchy atoms)

round71FiniteCauchyRemainderToTriadicMassConstructed : Bool
round71FiniteCauchyRemainderToTriadicMassConstructed = true

round71SameObjectAmplificationRemainderEqualsTriadicSignedSum : Bool
round71SameObjectAmplificationRemainderEqualsTriadicSignedSum = false

round71FiniteCauchyRemainderToTriadicMassConstructedIsTrue :
  round71FiniteCauchyRemainderToTriadicMassConstructed ≡ true
round71FiniteCauchyRemainderToTriadicMassConstructedIsTrue = refl

round71SameObjectAmplificationRemainderEqualsTriadicSignedSumIsFalse :
  round71SameObjectAmplificationRemainderEqualsTriadicSignedSum ≡ false
round71SameObjectAmplificationRemainderEqualsTriadicSignedSumIsFalse = refl
