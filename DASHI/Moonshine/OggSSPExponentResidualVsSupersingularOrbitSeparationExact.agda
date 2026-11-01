module DASHI.Moonshine.OggSSPExponentResidualVsSupersingularOrbitSeparationExact where

------------------------------------------------------------------------
-- MONSTROUS-EXPONENT RESIDUAL != SUPERSINGULAR FROBENIUS ORBIT COUNT
--
-- ATTRIBUTION / CLAIM BOUNDARY
--
-- External arithmetic:
--   * Ogg / Duncan--Ono supply the supersingular-prime context;
--   * Duncan--Swisher supply the monstrous-exponent arithmetic upstream.
--
-- Repository reconstruction:
--   SupersingularFrobeniusOrbitSpectrumExact builds a finite normal-form
--   involution spectrum from the modular counts, while explicitly NOT
--   constructing the geometric supersingular carrier.
--
-- DASHI extension here:
--   compare that orbit-spectrum invariant with the monstrous-exponent
--   multiplicity/residual invariants and prove they are not the same generic
--   quantity.  No external author is credited with this comparison.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Interop.SourceAttributionShapePolicyExact as AttributionPolicy
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Frobenius
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Exponent
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Residual
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Source
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Provenance is internal proof lineage over already-attributed owners.
------------------------------------------------------------------------

claimOrigin : Source.ClaimOrigin
claimOrigin = Source.repositoryCrossModuleInference

attributionShape :
  AttributionPolicy.RequiredAttributionShape
attributionShape =
  AttributionPolicy.requiredAttributionShape
    AttributionPolicy.internalDerivedTheorem

attributionUsesProofLineage :
  attributionShape ≡ AttributionPolicy.proofLineageNoNewExternalCitation
attributionUsesProofLineage = refl

------------------------------------------------------------------------
-- 2. Connected-component count of the finite involution normal form.
--
-- A spectrum with f fixed singleton orbits and q two-cycles has f+q
-- connected C2-orbits.  This is intentionally different from its carrier
-- cardinality f+2q.
------------------------------------------------------------------------

supersingularPi0Count :
  Matrix.OddPrimeCandidateUnder72 → Nat
supersingularPi0Count prime =
  Frobenius.rationalSupersingularCount prime
  + Frobenius.frobeniusTwoOrbitCount prime

supersingularCarrierCount :
  Matrix.OddPrimeCandidateUnder72 → Nat
supersingularCarrierCount = Frobenius.totalSupersingularCount

------------------------------------------------------------------------
-- 3. p=3 is the decisive separation.
--
-- The normalized supersingular Frobenius spectrum is one fixed slot:
--
--   pi0 = 1, carrier = 1.
--
-- The Duncan--Swisher exceptional monstrous-exponent residual is:
--
--   R_3 = 2.
--
-- Hence the already-owned supersingular Frobenius normal form CANNOT itself
-- be the missing exponent-residual groupoid under a pi0-preserving
-- recognition.
------------------------------------------------------------------------

p3SupersingularPi0IsOne :
  supersingularPi0Count Matrix.prime3 ≡ 1
p3SupersingularPi0IsOne = refl

p3SupersingularCarrierIsOne :
  supersingularCarrierCount Matrix.prime3 ≡ 1
p3SupersingularCarrierIsOne = refl

p3ExponentResidualIsTwo :
  Residual.p3ExceptionalResidual ≡ 2
p3ExponentResidualIsTwo = refl

p3SupersingularPi0IsNotExponentResidual :
  supersingularPi0Count Matrix.prime3
  ≡ Residual.p3ExceptionalResidual → ⊥
p3SupersingularPi0IsNotExponentResidual ()

p3SupersingularCarrierIsNotExponentResidual :
  supersingularCarrierCount Matrix.prime3
  ≡ Residual.p3ExceptionalResidual → ⊥
p3SupersingularCarrierIsNotExponentResidual ()

------------------------------------------------------------------------
-- 4. Ordinary Ogg lanes also show that Monster multiplicity is not simply
--    the number of supersingular Frobenius components.
------------------------------------------------------------------------

p5SupersingularPi0IsOne :
  supersingularPi0Count Matrix.prime5 ≡ 1
p5SupersingularPi0IsOne = refl

p5MonsterExponentIsNine :
  Exponent.monsterOrderExponent Lane.p5 ≡ 9
p5MonsterExponentIsNine = refl

p5SupersingularPi0IsNotMonsterExponent :
  supersingularPi0Count Matrix.prime5
  ≡ Exponent.monsterOrderExponent Lane.p5 → ⊥
p5SupersingularPi0IsNotMonsterExponent ()

p7SupersingularPi0IsOne :
  supersingularPi0Count Matrix.prime7 ≡ 1
p7SupersingularPi0IsOne = refl

p7MonsterExponentIsSix :
  Exponent.monsterOrderExponent Lane.p7 ≡ 6
p7MonsterExponentIsSix = refl

p7SupersingularPi0IsNotMonsterExponent :
  supersingularPi0Count Matrix.prime7
  ≡ Exponent.monsterOrderExponent Lane.p7 → ⊥
p7SupersingularPi0IsNotMonsterExponent ()

------------------------------------------------------------------------
-- 5. p=11 gives an instructive equality of counts, but the repository's
--    same-object discipline forbids promoting it to groupoid recognition.
------------------------------------------------------------------------

p11SupersingularPi0IsTwo :
  supersingularPi0Count Matrix.prime11 ≡ 2
p11SupersingularPi0IsTwo = refl

p11MonsterExponentIsTwo :
  Exponent.monsterOrderExponent Lane.p11 ≡ 2
p11MonsterExponentIsTwo = refl

p11CountsCoincide :
  supersingularPi0Count Matrix.prime11
  ≡ Exponent.monsterOrderExponent Lane.p11
p11CountsCoincide = refl

data P11EqualCountCreatesExponentOrbitSameObject : Set where

p11EqualCountDoesNotCreateExponentOrbitSameObject :
  P11EqualCountCreatesExponentOrbitSameObject → ⊥
p11EqualCountDoesNotCreateExponentOrbitSameObject ()

------------------------------------------------------------------------
-- 6. Consequence for the recognition programme.
------------------------------------------------------------------------

data ExponentResidualSourceKind : Set where
  supersingularFrobeniusOrbitSpectrum : ExponentResidualSourceKind
  distinctExponentResidualGroupoidRequired : ExponentResidualSourceKind

p3RequiredSourceKind : ExponentResidualSourceKind
p3RequiredSourceKind = distinctExponentResidualGroupoidRequired

data SupersingularSpectrumAutomaticallySuppliesExponentResidualSource : Set where

supersingularSpectrumDoesNotAutomaticallySupplyExponentResidualSource :
  SupersingularSpectrumAutomaticallySuppliesExponentResidualSource → ⊥
supersingularSpectrumDoesNotAutomaticallySupplyExponentResidualSource ()

record ExponentResidualSupersingularSeparationBoundary : Set where
  constructor exponent-residual-supersingular-separation-boundary
  field
    supersingularPi0InvariantDefined : Bool
    p3SupersingularPi0IsOne : Bool
    p3ExponentResidualIsTwo : Bool
    p3TwoInvariantsSeparated : Bool
    p5Pi0SeparatedFromMonsterExponent : Bool
    p7Pi0SeparatedFromMonsterExponent : Bool
    p11CountCoincidenceRecorded : Bool
    p11CountCoincidencePromotedToSameObject : Bool
    exponentResidualNeedsDistinctSourceGroupoid : Bool

canonicalExponentResidualSupersingularSeparationBoundary :
  ExponentResidualSupersingularSeparationBoundary
canonicalExponentResidualSupersingularSeparationBoundary =
  exponent-residual-supersingular-separation-boundary
    true true true true true true true false true
