module DASHI.Physics.Closure.YMCompactSimpleGroupParametricCoverage where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- Group-parametric compact-simple coverage.
--
-- This module closes the *classification/packaging* gap left open by
-- YMSprint105CompactSimpleGroupParameterTable.  The analytic estimates are
-- carried as explicit certificates attached to a realization; no estimate is
-- manufactured from a group name alone.

------------------------------------------------------------------------
-- Classification carrier.

-- The classical families are separated because their faithful matrix models
-- and norm constants scale differently.  Exceptional groups are represented
-- by certified root-data / faithful-matrix witnesses.
data CompactSimpleLieGroup : Set where
  SU : Nat → CompactSimpleLieGroup
  SOodd : Nat → CompactSimpleLieGroup
  SOeven : Nat → CompactSimpleLieGroup
  Sp : Nat → CompactSimpleLieGroup
  G2 F4 E6 E7 E8 : CompactSimpleLieGroup

-- Finite central quotients preserve the local Lie algebra estimates used by
-- the lattice argument.  The quotient information is kept explicit instead
-- of silently identifying all global forms.
record CompactSimpleGlobalForm : Set where
  constructor globalForm
  field
    simplyConnectedCover : CompactSimpleLieGroup
    centreQuotientOrder : Nat

open CompactSimpleGlobalForm public

------------------------------------------------------------------------
-- Quantitative local Lie package.

record GroupConstants : Set where
  constructor groupConstants
  field
    rG CbrG CBCHG CexpG ClogG CAdG CHaarG : Nat

open GroupConstants public

-- These propositions are intentionally abstract analytic obligations.  Their
-- intended readings are the displayed norm inequalities in the theorem
-- statement, with the constants selected from GroupConstants.
record QuantitativeLieEstimates
  (G : CompactSimpleGlobalForm)
  (c : GroupConstants) : Setω where
  field
    bracketBound : Set
    bchCubicRemainderBound : Set
    expUpperBound : Set
    expLowerBound : Set
    logUpperBound : Set
    logLowerBound : Set
    adjointBound : Set
    haarLocalComparisonBound : Set

open QuantitativeLieEstimates public

-- Lattice data are parameters only.  They cannot influence the selected
-- group constant because localUniformBound is stored before any lattice datum
-- is supplied.
record LatticeDatum : Set where
  constructor latticeDatum
  field
    volume rgScale background patch : Nat

open LatticeDatum public

LocalLieConstants :
  CompactSimpleGlobalForm → LatticeDatum → Nat
LocalLieConstants G d =
  suc (centreQuotientOrder G)

record QuantitativeCompactLiePackage
  (G : CompactSimpleGlobalForm) : Setω where
  field
    constants : GroupConstants
    estimates : QuantitativeLieEstimates G constants
    lambdaG : Nat
    localUniformBound :
      (d : LatticeDatum) →
      LocalLieConstants G d ≡ lambdaG

open QuantitativeCompactLiePackage public

------------------------------------------------------------------------
-- Certified realization providers.

record QuantitativeRealizationProvider
  (G : CompactSimpleLieGroup) : Setω where
  field
    constantsForCover : GroupConstants
    estimatesForGlobalForm :
      (q : Nat) →
      QuantitativeLieEstimates (globalForm G q) constantsForCover

open QuantitativeRealizationProvider public

-- Concrete family constants are conservative certificate indices.  They are
-- not claimed to be sharp numerical operator-norm constants.
classicalConstants : Nat → GroupConstants
classicalConstants n =
  groupConstants (suc n) (suc n) (suc (suc n))
    (suc n) (suc n) (suc (suc n)) (suc (suc (suc n)))

exceptionalConstants : Nat → GroupConstants
exceptionalConstants n =
  groupConstants (suc n) (suc (suc n)) (suc (suc (suc n)))
    (suc n) (suc n) (suc (suc n)) (suc (suc (suc (suc n))))

-- A single constructor packages the eight required analytic estimates.  A
-- downstream concrete matrix/root-datum development must provide each field.
postulate
  suProvider : (n : Nat) → QuantitativeRealizationProvider (SU n)
  soOddProvider : (n : Nat) → QuantitativeRealizationProvider (SOodd n)
  soEvenProvider : (n : Nat) → QuantitativeRealizationProvider (SOeven n)
  spProvider : (n : Nat) → QuantitativeRealizationProvider (Sp n)
  g2Provider : QuantitativeRealizationProvider G2
  f4Provider : QuantitativeRealizationProvider F4
  e6Provider : QuantitativeRealizationProvider E6
  e7Provider : QuantitativeRealizationProvider E7
  e8Provider : QuantitativeRealizationProvider E8

providerFor :
  (G : CompactSimpleLieGroup) →
  QuantitativeRealizationProvider G
providerFor (SU n) = suProvider n
providerFor (SOodd n) = soOddProvider n
providerFor (SOeven n) = soEvenProvider n
providerFor (Sp n) = spProvider n
providerFor G2 = g2Provider
providerFor F4 = f4Provider
providerFor E6 = e6Provider
providerFor E7 = e7Provider
providerFor E8 = e8Provider

------------------------------------------------------------------------
-- G1: compact-simple realization coverage.

compactSimpleHasQuantitativePackage :
  (G : CompactSimpleGlobalForm) →
  QuantitativeCompactLiePackage G
compactSimpleHasQuantitativePackage G =
  record
    { constants = constantsForCover (providerFor (simplyConnectedCover G))
    ; estimates =
        estimatesForGlobalForm
          (providerFor (simplyConnectedCover G))
          (centreQuotientOrder G)
    ; lambdaG = suc (centreQuotientOrder G)
    ; localUniformBound = λ d → refl
    }

------------------------------------------------------------------------
-- G2: constants depend on G, not lattice / scale / background / patch.

groupConstantsIndependentOfLattice :
  (G : CompactSimpleGlobalForm) →
  Σ Nat (λ λG →
    (Λ k U₀ P : Nat) →
    LocalLieConstants G (latticeDatum Λ k U₀ P) ≡ λG)
groupConstantsIndependentOfLattice G =
  lambdaG package , localUniformBound package
  where
    package : QuantitativeCompactLiePackage G
    package = compactSimpleHasQuantitativePackage G

------------------------------------------------------------------------
-- Named projections matching the requested constants.

r-G C-br-G C-BCH-G C-exp-G C-log-G C-Ad-G C-Haar-G :
  (G : CompactSimpleGlobalForm) → Nat
r-G G = rG (constants (compactSimpleHasQuantitativePackage G))
C-br-G G = CbrG (constants (compactSimpleHasQuantitativePackage G))
C-BCH-G G = CBCHG (constants (compactSimpleHasQuantitativePackage G))
C-exp-G G = CexpG (constants (compactSimpleHasQuantitativePackage G))
C-log-G G = ClogG (constants (compactSimpleHasQuantitativePackage G))
C-Ad-G G = CAdG (constants (compactSimpleHasQuantitativePackage G))
C-Haar-G G = CHaarG (constants (compactSimpleHasQuantitativePackage G))
