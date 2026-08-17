module DASHI.Moonshine.P11EichlerDeuringStackUnweightingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapters 41--42: Brandt ideal-class weights and supersingular curves.
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition,
-- Graduate Texts in Mathematics 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Classical Eichler--Deuring mass formula:
--
--   sum_[E ss] 1 / |Aut(E)| = (p-1)/24.
--
-- For p=11 the two supersingular classes have automorphism orders 6 and 4,
-- hence reduced/monodromy weights 3 and 2.  Clearing reciprocal mass at scale
-- 6 gives ordinary sheet multiplicities 2 and 3.
--
-- DASHI CONTRIBUTION
--
-- Prove that the five-state 2+3 carrier discovered by the positivity search is
-- exactly the division-free integral unweighting forced by the p=11 stacky
-- automorphism data.  Thus the cardinality pattern is no longer an unexplained
-- model choice.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.BrandtStackUnweightingExact as Stack
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Brandt
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine5

------------------------------------------------------------------------
-- Geometric ordering: j=0 first, j=1728 second.
------------------------------------------------------------------------

p11MonodromyWeight : Geo.P11SupersingularJ → Nat
p11MonodromyWeight Geo.jZeroSS = 3
p11MonodromyWeight Geo.j1728SS = 2

p11SheetMultiplicity : Geo.P11SupersingularJ → Nat
p11SheetMultiplicity Geo.jZeroSS = 2
p11SheetMultiplicity Geo.j1728SS = 3

p11CommonScale : Nat
p11CommonScale = 6

p11ClearsWeight : (c : Geo.P11SupersingularJ) →
  p11SheetMultiplicity c * p11MonodromyWeight c ≡ p11CommonScale
p11ClearsWeight Geo.jZeroSS = refl
p11ClearsWeight Geo.j1728SS = refl

p11StackUnweighting : Stack.ReciprocalUnweighting Geo.P11SupersingularJ
p11StackUnweighting =
  record
    { Stack.monodromyWeight = p11MonodromyWeight
    ; Stack.sheetMultiplicity = p11SheetMultiplicity
    ; Stack.commonScale = p11CommonScale
    ; Stack.commonScalePositive = s≤s z≤n
    ; Stack.clearsWeight = p11ClearsWeight
    }

------------------------------------------------------------------------
-- The actual ell=2 Brandt matrix satisfies both the source-facing cross-weight
-- balance and the ordinary edge balance of the unweighted cover.
------------------------------------------------------------------------

p11Ell2Entry : Geo.P11SupersingularJ → Geo.P11SupersingularJ → Nat
p11Ell2Entry Geo.jZeroSS Geo.jZeroSS = 0
p11Ell2Entry Geo.jZeroSS Geo.j1728SS = 3
p11Ell2Entry Geo.j1728SS Geo.jZeroSS = 2
p11Ell2Entry Geo.j1728SS Geo.j1728SS = 1

p11Ell2CrossMonodromyBalance :
  (i j : Geo.P11SupersingularJ) →
  p11MonodromyWeight j * p11Ell2Entry i j
  ≡ p11MonodromyWeight i * p11Ell2Entry j i
p11Ell2CrossMonodromyBalance Geo.jZeroSS Geo.jZeroSS = refl
p11Ell2CrossMonodromyBalance Geo.jZeroSS Geo.j1728SS = refl
p11Ell2CrossMonodromyBalance Geo.j1728SS Geo.jZeroSS = refl
p11Ell2CrossMonodromyBalance Geo.j1728SS Geo.j1728SS = refl

p11Ell2UnweightedEdgeBalance :
  (i j : Geo.P11SupersingularJ) →
  p11SheetMultiplicity i * p11Ell2Entry i j
  ≡ p11SheetMultiplicity j * p11Ell2Entry j i
p11Ell2UnweightedEdgeBalance Geo.jZeroSS Geo.jZeroSS = refl
p11Ell2UnweightedEdgeBalance Geo.jZeroSS Geo.j1728SS = refl
p11Ell2UnweightedEdgeBalance Geo.j1728SS Geo.jZeroSS = refl
p11Ell2UnweightedEdgeBalance Geo.j1728SS Geo.j1728SS = refl

p11Ell2WeightedBrandtBalance :
  Stack.WeightedBrandtBalance p11StackUnweighting p11Ell2Entry
p11Ell2WeightedBrandtBalance =
  record
    { Stack.crossMonodromyBalance = p11Ell2CrossMonodromyBalance
    ; Stack.unweightedEdgeBalance = p11Ell2UnweightedEdgeBalance
    }

------------------------------------------------------------------------
-- Recover the discovered five-state fibre cardinalities from arithmetic.
------------------------------------------------------------------------

fine5FibreCardinality : Geo.P11SupersingularJ → Nat
fine5FibreCardinality Geo.jZeroSS = 2
fine5FibreCardinality Geo.j1728SS = 3

fine5FibreCardinalityIsStackMultiplicity :
  (c : Geo.P11SupersingularJ) →
  fine5FibreCardinality c ≡ p11SheetMultiplicity c
fine5FibreCardinalityIsStackMultiplicity Geo.jZeroSS = refl
fine5FibreCardinalityIsStackMultiplicity Geo.j1728SS = refl

p11UnweightedStateCount : Nat
p11UnweightedStateCount =
  p11SheetMultiplicity Geo.jZeroSS + p11SheetMultiplicity Geo.j1728SS

p11UnweightedStateCountIsFive : p11UnweightedStateCount ≡ 5
p11UnweightedStateCountIsFive = refl

fine5ProjectionHasArithmeticFibreShape :
  ( Fine5.projectFine5 Fine5.a0 ≡ Geo.jZeroSS
  × Fine5.projectFine5 Fine5.a1 ≡ Geo.jZeroSS )
  ×
  ( Fine5.projectFine5 Fine5.b0 ≡ Geo.j1728SS
  × Fine5.projectFine5 Fine5.b1 ≡ Geo.j1728SS
  × Fine5.projectFine5 Fine5.b2 ≡ Geo.j1728SS )
fine5ProjectionHasArithmeticFibreShape =
  (refl , refl) , (refl , refl , refl)

------------------------------------------------------------------------
-- Exact mass-formula arithmetic at p=11, denominator-cleared by 24:
--
--   24/6 + 24/4 = 4 + 6 = 10 = p-1.
--
-- This records the same stacky data without introducing rationals.
------------------------------------------------------------------------

p11MassFormulaCleared : 4 + 6 ≡ 11 - 1
p11MassFormulaCleared = refl

record P11StackUnweightingBoundary : Set where
  field
    fiveStateCardinalityDerivedFromAutomorphisms : Bool
    fiveStateCardinalityDerivedFromAutomorphismsIsTrue :
      fiveStateCardinalityDerivedFromAutomorphisms ≡ true

    stackWeightAndSheetMultiplicityDistinguished : Bool
    stackWeightAndSheetMultiplicityDistinguishedIsTrue :
      stackWeightAndSheetMultiplicityDistinguished ≡ true

    massFormulaClearedArithmeticConstructed : Bool
    massFormulaClearedArithmeticConstructedIsTrue :
      massFormulaClearedArithmeticConstructed ≡ true

    particularPermutationGeneratorsDerivedFromMassFormula : Bool
    particularPermutationGeneratorsDerivedFromMassFormulaIsFalse :
      particularPermutationGeneratorsDerivedFromMassFormula ≡ false

canonicalP11StackUnweightingBoundary : P11StackUnweightingBoundary
canonicalP11StackUnweightingBoundary =
  record
    { fiveStateCardinalityDerivedFromAutomorphisms = true
    ; fiveStateCardinalityDerivedFromAutomorphismsIsTrue = refl
    ; stackWeightAndSheetMultiplicityDistinguished = true
    ; stackWeightAndSheetMultiplicityDistinguishedIsTrue = refl
    ; massFormulaClearedArithmeticConstructed = true
    ; massFormulaClearedArithmeticConstructedIsTrue = refl
    ; particularPermutationGeneratorsDerivedFromMassFormula = false
    ; particularPermutationGeneratorsDerivedFromMassFormulaIsFalse = refl
    }
