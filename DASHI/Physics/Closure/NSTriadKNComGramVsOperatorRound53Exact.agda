module DASHI.Physics.Closure.NSTriadKNComGramVsOperatorRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Audit the exact repository type before attaching physical names to the
-- constants 17/64 and 65/512.  In Round 47 they bound `physicalPairProduct`,
-- a scalar pair/Gram quantity.  They are NOT yet typed as literal shell
-- operator norms.  Therefore this file supplies two disjoint same-object
-- identifications.  A physical proof may identify pairProduct with a Gram block
-- and obtain Gram bounds, or identify it directly with a whole operator-block
-- majorant and obtain operator bounds.  No square-root conversion is smuggled
-- between the two theorem surfaces.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Active
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth

-- Requested paper-facing name for the already-sharp support theorem.  This is
-- not an extra assumption: the Round-47 common-hat identification plus the
-- Round-46 exact dyadic-hat width theorem literally imply |q-r| <= 1.
physicalOddPQCommonHatSupport :
  ∀ {skeleton}
    (identification : Active.PhysicalOddPQHatIdentification skeleton)
    q r →
  Active.supportActive skeleton q r ≡ true →
  HatWidth.WithinOne q r
physicalOddPQCommonHatSupport = Active.activePairWithinOne

record PhysicalComGramBlockIdentification
    (skeleton : Active.PhysicalOddPQSupportSkeleton) : Set where
  field
    gramBlockNorm : Nat → Nat → ℚ
    pairProductIsGramBlock : ∀ q r →
      Active.physicalPairProduct skeleton q r ≡ gramBlockNorm q r

open PhysicalComGramBlockIdentification public

physicalComSameShellGramBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComGramBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q q ≡ true →
  gramBlockNorm sameObject q q ≤ Active.sameShellTarget
physicalComSameShellGramBlockBound sameObject bounds q active =
  subst
    (_≤ Active.sameShellTarget)
    (pairProductIsGramBlock sameObject q q)
    (Active.physicalComSameShellActiveBound bounds q active)

physicalComAdjacentShellGramBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComGramBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q (suc q) ≡ true →
  gramBlockNorm sameObject q (suc q) ≤ Active.adjacentShellTarget
physicalComAdjacentShellGramBlockBound sameObject bounds q active =
  subst
    (_≤ Active.adjacentShellTarget)
    (pairProductIsGramBlock sameObject q (suc q))
    (Active.physicalComAdjacentShellActiveBound bounds q active)

physicalComReverseAdjacentShellGramBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComGramBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton (suc q) q ≡ true →
  gramBlockNorm sameObject (suc q) q ≤ Active.adjacentShellTarget
physicalComReverseAdjacentShellGramBlockBound sameObject bounds q active =
  subst
    (_≤ Active.adjacentShellTarget)
    (pairProductIsGramBlock sameObject (suc q) q)
    (Active.physicalComReverseAdjacentShellActiveBound bounds q active)

record PhysicalComOperatorBlockIdentification
    (skeleton : Active.PhysicalOddPQSupportSkeleton) : Set where
  field
    operatorBlockNorm : Nat → Nat → ℚ
    pairProductMajorizesOperatorBlock : ∀ q r →
      operatorBlockNorm q r ≤ Active.physicalPairProduct skeleton q r

open PhysicalComOperatorBlockIdentification public

physicalComSameShellOperatorBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComOperatorBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q q ≡ true →
  operatorBlockNorm sameObject q q ≤ Active.sameShellTarget
physicalComSameShellOperatorBlockBound sameObject bounds q active =
  ℚP.≤-trans
    (pairProductMajorizesOperatorBlock sameObject q q)
    (Active.physicalComSameShellActiveBound bounds q active)

physicalComAdjacentShellOperatorBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComOperatorBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton q (suc q) ≡ true →
  operatorBlockNorm sameObject q (suc q) ≤ Active.adjacentShellTarget
physicalComAdjacentShellOperatorBlockBound sameObject bounds q active =
  ℚP.≤-trans
    (pairProductMajorizesOperatorBlock sameObject q (suc q))
    (Active.physicalComAdjacentShellActiveBound bounds q active)

physicalComReverseAdjacentShellOperatorBlockBound :
  ∀ {skeleton identification}
    (sameObject : PhysicalComOperatorBlockIdentification skeleton)
    (bounds : Active.SameAdjacentPhysicalComBounds skeleton identification)
    q →
  Active.supportActive skeleton (suc q) q ≡ true →
  operatorBlockNorm sameObject (suc q) q ≤ Active.adjacentShellTarget
physicalComReverseAdjacentShellOperatorBlockBound sameObject bounds q active =
  ℚP.≤-trans
    (pairProductMajorizesOperatorBlock sameObject (suc q) q)
    (Active.physicalComReverseAdjacentShellActiveBound bounds q active)

round47ConstantsCurrentlyTypeAsPairGramScalars : Bool
round47ConstantsCurrentlyTypeAsPairGramScalars = true

operatorNormIdentificationAlreadyConstructed : Bool
operatorNormIdentificationAlreadyConstructed = false

round47ConstantsCurrentlyTypeAsPairGramScalarsIsTrue :
  round47ConstantsCurrentlyTypeAsPairGramScalars ≡ true
round47ConstantsCurrentlyTypeAsPairGramScalarsIsTrue = refl

operatorNormIdentificationAlreadyConstructedIsFalse :
  operatorNormIdentificationAlreadyConstructed ≡ false
operatorNormIdentificationAlreadyConstructedIsFalse = refl
