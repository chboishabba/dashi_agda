module DASHI.Physics.Closure.NSTriadKNComShellBlockMajorantRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column test for integral and matrix operators; no DOI is
-- assigned to the historical theorem used here.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- DASHI CONTRIBUTION
--
-- The repository's `physicalPairProduct` is currently an abstract scalar Gram
-- quantity; the older exact files explicitly say that literal T_q^* T_r / shell
-- operator realization remains physical work.  Therefore 133/256 cannot yet be
-- promoted automatically to a literal shell-Hilbert operator coefficient.
--
-- Round 51 makes the dangerous multiplicity seam explicit.  A physical theorem
-- must identify each existing pair majorant as an upper bound for the WHOLE
-- shell-block operator norm, not merely one Fourier incidence.  Once that
-- identification is supplied, the same d=0 and d=1 constants transfer to the
-- block norm without a hidden counting factor.
--
-- A second record quantifies the fallback if only
--
--   blockNorm <= multiplicity * pairProduct
--
-- is available.  Then every active constant inherits that same multiplicity.
-- Thus any hidden mode-counting loss is visible before 133/256 is used as a
-- literal L2 coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active

record PhysicalShellBlockOperatorMajorant
    (skeleton : Active.PhysicalOddPQSupportSkeleton) : Set where
  field
    shellBlockOperatorNorm : Nat → Nat → ℚ
    shellBlockOperatorNormNonnegative : ∀ q r →
      0ℚ ≤ shellBlockOperatorNorm q r

    physicalPairProductMajorizesWholeShellBlock : ∀ q r →
      shellBlockOperatorNorm q r
      ≤ Active.physicalPairProduct skeleton q r

open PhysicalShellBlockOperatorMajorant public

shellBlockSameShellBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockOperatorMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q q ≡ true →
  shellBlockOperatorNorm majorant q q ≤ Active.sameShellTarget
shellBlockSameShellBound majorant bounds q active =
  ℚP.≤-trans
    (physicalPairProductMajorizesWholeShellBlock majorant q q)
    (Active.physicalComSameShellActiveBound bounds q active)

shellBlockForwardAdjacentBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockOperatorMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q (suc q) ≡ true →
  shellBlockOperatorNorm majorant q (suc q)
  ≤ Active.adjacentShellTarget
shellBlockForwardAdjacentBound majorant bounds q active =
  ℚP.≤-trans
    (physicalPairProductMajorizesWholeShellBlock majorant q (suc q))
    (Active.physicalComAdjacentShellActiveBound bounds q active)

shellBlockReverseAdjacentBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockOperatorMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton (suc q) q ≡ true →
  shellBlockOperatorNorm majorant (suc q) q
  ≤ Active.adjacentShellTarget
shellBlockReverseAdjacentBound majorant bounds q active =
  ℚP.≤-trans
    (physicalPairProductMajorizesWholeShellBlock majorant (suc q) q)
    (Active.physicalComReverseAdjacentShellActiveBound bounds q active)

record PhysicalShellBlockMultiplicityMajorant
    (skeleton : Active.PhysicalOddPQSupportSkeleton) : Set where
  field
    shellBlockNorm : Nat → Nat → ℚ
    shellBlockNormNonnegative : ∀ q r → 0ℚ ≤ shellBlockNorm q r
    multiplicity : ℚ
    multiplicityNonnegative : 0ℚ ≤ multiplicity

    blockBelowMultiplicityTimesPair : ∀ q r →
      shellBlockNorm q r
      ≤ multiplicity * Active.physicalPairProduct skeleton q r

open PhysicalShellBlockMultiplicityMajorant public

multiplicitySameShellBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockMultiplicityMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q q ≡ true →
  shellBlockNorm majorant q q
  ≤ multiplicity majorant * Active.sameShellTarget
multiplicitySameShellBound majorant bounds q active =
  let
    scaledPair :
      multiplicity majorant * Active.physicalPairProduct skeleton q q
      ≤ multiplicity majorant * Active.sameShellTarget
    scaledPair =
      let instance multiplicityNNI = nonNegative (multiplicityNonnegative majorant)
      in ℚP.*-monoˡ-≤-nonNeg
        (multiplicity majorant)
        (Active.physicalComSameShellActiveBound bounds q active)
  in
  ℚP.≤-trans
    (blockBelowMultiplicityTimesPair majorant q q)
    scaledPair

multiplicityForwardAdjacentBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockMultiplicityMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q (suc q) ≡ true →
  shellBlockNorm majorant q (suc q)
  ≤ multiplicity majorant * Active.adjacentShellTarget
multiplicityForwardAdjacentBound majorant bounds q active =
  let
    scaledPair :
      multiplicity majorant * Active.physicalPairProduct skeleton q (suc q)
      ≤ multiplicity majorant * Active.adjacentShellTarget
    scaledPair =
      let instance multiplicityNNI = nonNegative (multiplicityNonnegative majorant)
      in ℚP.*-monoˡ-≤-nonNeg
        (multiplicity majorant)
        (Active.physicalComAdjacentShellActiveBound bounds q active)
  in
  ℚP.≤-trans
    (blockBelowMultiplicityTimesPair majorant q (suc q))
    scaledPair

multiplicityReverseAdjacentBound :
  ∀ {skeleton identification}
    (majorant : PhysicalShellBlockMultiplicityMajorant skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton (suc q) q ≡ true →
  shellBlockNorm majorant (suc q) q
  ≤ multiplicity majorant * Active.adjacentShellTarget
multiplicityReverseAdjacentBound majorant bounds q active =
  let
    scaledPair :
      multiplicity majorant * Active.physicalPairProduct skeleton (suc q) q
      ≤ multiplicity majorant * Active.adjacentShellTarget
    scaledPair =
      let instance multiplicityNNI = nonNegative (multiplicityNonnegative majorant)
      in ℚP.*-monoˡ-≤-nonNeg
        (multiplicity majorant)
        (Active.physicalComReverseAdjacentShellActiveBound bounds q active)
  in
  ℚP.≤-trans
    (blockBelowMultiplicityTimesPair majorant (suc q) q)
    scaledPair

record PerIncidenceOnlyMajorant
    (skeleton : Active.PhysicalOddPQSupportSkeleton) : Set where
  field
    incidenceMajorant : Nat → Nat → ℚ
    incidenceMajorantNonnegative : ∀ q r → 0ℚ ≤ incidenceMajorant q r
    incidenceMajorantBelowPairProduct : ∀ q r →
      incidenceMajorant q r ≤ Active.physicalPairProduct skeleton q r

open PerIncidenceOnlyMajorant public

physicalPairProductAlreadyKnownToBeWholeBlockNormMajorant : Bool
physicalPairProductAlreadyKnownToBeWholeBlockNormMajorant = false

comMultiplicityTrapMadeExplicit : Bool
comMultiplicityTrapMadeExplicit = true

physicalPairProductAlreadyKnownToBeWholeBlockNormMajorantIsFalse :
  physicalPairProductAlreadyKnownToBeWholeBlockNormMajorant ≡ false
physicalPairProductAlreadyKnownToBeWholeBlockNormMajorantIsFalse = refl

comMultiplicityTrapMadeExplicitIsTrue :
  comMultiplicityTrapMadeExplicit ≡ true
comMultiplicityTrapMadeExplicitIsTrue = refl
