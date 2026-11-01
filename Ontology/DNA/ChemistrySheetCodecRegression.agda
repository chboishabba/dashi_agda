module Ontology.DNA.ChemistrySheetCodecRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import Ontology.DNA.ChemistrySheetTowerBoundary using
  (CarrierGrowthLaw; fixedFourWayNesting; MultiscaleSheetTower)
open import Ontology.DNA.FiniteChemistrySheetTower using
  (finiteChemistrySheetTower; finiteTowerIsNotTetrationalByDeclaration)
open import Ontology.DNA.ChemistryTernaryQuantizer using
  (Trit; minus; neutral; plus; reconstructSigned; quantizeSigned;
   exactSignedTernaryReceipt; ExactSignedTernaryReceipt)
open import Ontology.DNA.ChemistryPhaseTetrationBoundary using
  (flipSigned; neutral-fixed; physicalDNAGrowthLaw)
open import Ontology.DNA.ChemistrySheetHamiltonian using (Signed; neg; zer; pos)
open import Ontology.DNA.ChemistryEmpiricalAndCodecSurface using
  (encodeTritBase; decodeTritBase; trit-roundtrip)

finite-growth-regression :
  MultiscaleSheetTower.growthLaw finiteChemistrySheetTower ≡ fixedFourWayNesting
finite-growth-regression = finiteTowerIsNotTetrationalByDeclaration

negative-ternary-roundtrip : reconstructSigned (quantizeSigned neg) ≡ neg
negative-ternary-roundtrip = refl

neutral-ternary-roundtrip : reconstructSigned (quantizeSigned zer) ≡ zer
neutral-ternary-roundtrip = refl

positive-ternary-roundtrip : reconstructSigned (quantizeSigned pos) ≡ pos
positive-ternary-roundtrip = refl

neutral-phase-fixed : flipSigned zer ≡ zer
neutral-phase-fixed = neutral-fixed

minus-codec-roundtrip : decodeTritBase (encodeTritBase minus) ≡ minus
minus-codec-roundtrip = trit-roundtrip minus

physical-growth-regression : physicalDNAGrowthLaw ≡ fixedFourWayNesting
physical-growth-regression = refl
