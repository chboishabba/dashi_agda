module DASHI.Physics.QuantumVacuum.CasimirCMP119H2R457CompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirCMP119H2R457CompilerExact as M

h2BuildsLiteralConstructionRegression :
  M.cmp119H2LiteralConstructionCompilerOwned
    M.canonicalCMP119H2R457Boundary ≡ true
h2BuildsLiteralConstructionRegression = refl

h2BuildsMinimalContinuumRegression :
  M.cmp119H2ContinuumAttachmentCompilerOwned
    M.canonicalCMP119H2R457Boundary ≡ true
h2BuildsMinimalContinuumRegression = refl

pinnedConstructionRetiredRegression :
  M.pinnedYangMillsConstructionRequiredForCasimirR457
    M.canonicalCMP119H2R457Boundary ≡ false
pinnedConstructionRetiredRegression = refl

literalConstructionIndependentPaymentRetiredRegression :
  M.independentLiteralConstructionPaymentRequiredAfterH2Fields
    M.canonicalCMP119H2R457Boundary ≡ false
literalConstructionIndependentPaymentRetiredRegression = refl

h2PhysicalInstantiationStillOpenRegression :
  M.cmp119H2PhysicalInstantiationStillRequired
    M.canonicalCMP119H2R457Boundary ≡ true
h2PhysicalInstantiationStillOpenRegression = refl

r581SourceStillOpenRegression :
  M.r581PreferredFiniteOSMomentSourceStillRequiredInsideH2
    M.canonicalCMP119H2R457Boundary ≡ true
r581SourceStillOpenRegression = refl
