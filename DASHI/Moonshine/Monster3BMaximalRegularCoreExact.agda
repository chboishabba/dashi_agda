module DASHI.Moonshine.Monster3BMaximalRegularCoreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society 11
-- (1979), 308--339. DOI: 10.1112/blms/11.3.308.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Prove, rather than merely name, that 65610 is the maximal uniform C3 core
-- of the certified multiplicity vector (65663,65610,65610).  A candidate is a
-- common core together with explicit natural residuals in all three sectors.
-- The zeta-sector decomposition immediately bounds every candidate by 65610.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier
import DASHI.Moonshine.Monster3BCentredProbeCoreSelectorExact as Core

record UniformCoreDecomposition : Set where
  constructor uniformCoreDecomposition
  field
    core : Nat
    invariantResidual : Nat
    zetaResidual : Nat
    zetaSquaredResidual : Nat
    reconstructInvariant :
      core + invariantResidual ≡ Fourier.invariant Fourier.monsterW3B
    reconstructZeta :
      core + zetaResidual ≡ Fourier.zeta Fourier.monsterW3B
    reconstructZetaSquared :
      core + zetaSquaredResidual ≡ Fourier.zetaSquared Fourier.monsterW3B

open UniformCoreDecomposition public

canonicalMaximalCoreDecomposition : UniformCoreDecomposition
canonicalMaximalCoreDecomposition =
  uniformCoreDecomposition 65610 53 0 0 refl refl refl

candidateCoreBelowZetaMultiplicity :
  (candidate : UniformCoreDecomposition) →
  core candidate ≤ Fourier.zeta Fourier.monsterW3B
candidateCoreBelowZetaMultiplicity candidate =
  subst
    (λ upper → core candidate ≤ upper)
    (reconstructZeta candidate)
    (m≤m+n (core candidate) (zetaResidual candidate))

maximalRegularCoreDominatesEveryUniformCore :
  (candidate : UniformCoreDecomposition) →
  core candidate ≤ Core.maximalRegularCore
maximalRegularCoreDominatesEveryUniformCore =
  candidateCoreBelowZetaMultiplicity

canonicalCoreIsMaximal :
  core canonicalMaximalCoreDecomposition ≡ Core.maximalRegularCore
canonicalCoreIsMaximal = refl

canonicalInvariantResidualIs53 :
  invariantResidual canonicalMaximalCoreDecomposition ≡ 53
canonicalInvariantResidualIs53 = refl

canonicalNontrivialResidualsVanish :
  zetaResidual canonicalMaximalCoreDecomposition
  + zetaSquaredResidual canonicalMaximalCoreDecomposition
  ≡ 0
canonicalNontrivialResidualsVanish = refl
