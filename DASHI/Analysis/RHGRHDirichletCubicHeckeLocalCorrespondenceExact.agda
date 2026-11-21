module DASHI.Analysis.RHGRHDirichletCubicHeckeLocalCorrespondenceExact where

-- Reconcile source-typed finite/local Dirichlet ↔ cubic Jacobi ↔ CM
-- rather than equating a quadratic Dirichlet character with cubic ψ.
--
-- Source receipts are observations of Lean #69, not imported proofs.
-- Exact split/inert arithmetic was separately executed in Python;
-- this file does not manufacture an analytic Hecke/Grössencharacter.
-- SOURCE WRITTEN, Agda kernel pending.

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Physics.QFT.ConductorVsDiscriminantReceipt as D
import DASHI.Mathematics.CrossPollination.EisensteinLeanSplitPrimeLocalClosureReceiptExact as New
import DASHI.Mathematics.CrossPollination.EisensteinLeanInertPrimeLocalFactorReceiptExact as Old
import DASHI.Unified.TOEArithmeticCMRealizationExact as TOE

-- Original primitive QUADRATIC conductor for K=Q(sqrt(-3)).
quadraticDirichletConductorIsThree :
  D.dirichletCharacterConductor D.dMinus3Row ≡ 3
quadraticDirichletConductorIsThree =
  D.dirichletCharacterConductorMatchesPrimitive D.dMinus3Row

-- Note: order conductor f=1 is NOT this quadratic-character modulus.
cmOrderConductorIsOne :
  D.orderConductor D.dMinus3Row ≡ 1
cmOrderConductorIsOne =
  D.orderConductorMatchesOrder D.dMinus3Row

-- Source revision: original Lean PR #69 later added actual finite
-- canonical cube-fibre/Jacobi/split-local owners. Early receipts
-- are historical snapshots and must not override the later one.
laterLeanCanonicalCubeFibreObserved :
  New.canonicalCubeFibreCertificateObserved ≡ true
laterLeanCanonicalCubeFibreObserved = refl

laterLeanSplitJacobiPrimeNormObserved :
  New.splitJacobiNormPrimeObserved ≡ true
laterLeanSplitJacobiPrimeNormObserved = refl

laterLeanAllGoodPrimeLocalObserved :
  New.allGoodPrimeLocalClassificationObserved ≡ true
laterLeanAllGoodPrimeLocalObserved = refl

earlyLeanCubeFibreSnapshotWasOpen :
  Old.canonicalCubeFibreCharacterCertificateObserved ≡ false
earlyLeanCubeFibreSnapshotWasOpen = refl

-- Important: paid *local* Euler polynomials from a same-curve p>3
-- source do not construct a global analytic Hecke character.
globalGroessencharacterNotYetObserved :
  New.groessencharacterObserved ≡ false
globalGroessencharacterNotYetObserved = refl

globalEllipticLSeriesNotYetObserved :
  New.globalEllipticLSeriesAgreementObserved ≡ false
globalEllipticLSeriesNotYetObserved = refl

-- The existing TOE/CM owner remains fail-closed even though its
-- literal local-status snapshot predates the later Lean source.
sameCurveHeckeStillUnpaid :
  TOE.ArithmeticCMPayment.sameCurveHeckeGroessencharacterPaid
    TOE.currentArithmeticCMPayment ≡ false
sameCurveHeckeStillUnpaid = refl

-- For true Dirichlet↔Hecke comparison one must specify separately:
-- (1) pullback of χ_{-3} along a suitable norm/idelic map;
-- (2) the genuinely *different* infinity type and conductor of
-- the elliptic CM Grössencharacter;
-- (3) equality of local Euler factors at every appropriate prime;
-- (4) bad primes, archimedean gamma factors, and global L-functions.
-- No automatic character equality or analytic GRH transfer exists.
