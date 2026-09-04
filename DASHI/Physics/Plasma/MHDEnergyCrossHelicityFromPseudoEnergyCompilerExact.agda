module DASHI.Physics.Plasma.MHDEnergyCrossHelicityFromPseudoEnergyCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.MHDElsasserPseudoEnergyCyclicBidiExact as Pseudo

------------------------------------------------------------------------
-- COMPILER: E+ / E- BALANCES -> ENERGY / CROSS HELICITY
--
-- Once the literal same-object plus and minus pseudo-energy cyclic balances
-- are available, total energy and cross-helicity conservation are downstream
-- algebraic consumers of the already-owned Elsasser coordinate identities.
------------------------------------------------------------------------

record EnergyCrossHelicityCompilerInput : Set₁ where
  constructor energy-cross-helicity-compiler-input
  field
    pseudoEnergyBalance : Pseudo.ElsasserPseudoEnergyBalance
    energyCoordinateIdentityReceipt : Set
    crossHelicityCoordinateIdentityReceipt : Set
    directionalVariationIdentityReceipt : Set
    sameObjectNormalizationReceipt : Set
    inputReference : String

open EnergyCrossHelicityCompilerInput public

record EnergyCrossHelicityCompilerOutput : Set₁ where
  constructor energy-cross-helicity-compiler-output
  field
    totalEnergyCyclicCancellation : Set
    crossHelicityCyclicCancellation : Set
    noNewPDEEstimateRequired : Set
    outputReference : String

open EnergyCrossHelicityCompilerOutput public

record EnergyCrossHelicityCompiler : Set₁ where
  constructor energy-cross-helicity-compiler
  field
    compile : EnergyCrossHelicityCompilerInput → EnergyCrossHelicityCompilerOutput
    compilerReference : String

open EnergyCrossHelicityCompiler public

record CompilerBoundary : Set where
  constructor compiler-boundary
  field
    energyNeedsIndependentPDEProofAfterBothPseudoEnergiesClose : Bool
    energyNeedsIndependentPDEProofAfterBothPseudoEnergiesCloseIsFalse :
      energyNeedsIndependentPDEProofAfterBothPseudoEnergiesClose ≡ false

    crossHelicityNeedsIndependentPDEProofAfterBothPseudoEnergiesClose : Bool
    crossHelicityNeedsIndependentPDEProofAfterBothPseudoEnergiesCloseIsFalse :
      crossHelicityNeedsIndependentPDEProofAfterBothPseudoEnergiesClose ≡ false

    magneticHelicityIsCompilerOutputOfSameTwoBalances : Bool
    magneticHelicityIsCompilerOutputOfSameTwoBalancesIsFalse :
      magneticHelicityIsCompilerOutputOfSameTwoBalances ≡ false

canonicalCompilerBoundary : CompilerBoundary
canonicalCompilerBoundary =
  compiler-boundary false refl false refl false refl
