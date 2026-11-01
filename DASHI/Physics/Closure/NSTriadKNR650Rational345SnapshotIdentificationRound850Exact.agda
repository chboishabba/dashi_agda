{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345SnapshotIdentificationRound850Exact where

------------------------------------------------------------------------
-- R850 / CLOSE R829-VECTOR: ACTUAL REPOSITORY SNAPSHOT IDENTIFICATION
--
-- The live chain now supplies all three ACTUAL repository scalars on the
-- radius-four 3-4-5 snapshot:
--
--   R849: literal global R692 coherent commutator work;
--   R847: literal critical production fold;
--   R847: literal critical dissipation fold.
--
-- R829 already kernel-checks the finite component table and R815
-- normalization.  Therefore no scalar/interface assumption remains at t=0:
-- instantiate Repository345SnapshotIdentification directly and obtain
--
--   canonical signed rate = -28273644/125 < 0.
--
-- This closes the instantaneous R829-vector decision leaf.  It does NOT
-- construct a real-time R408 trajectory or the short-time integrated
-- counterexample; that is the remaining R830-real-ODE leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345ComponentScalarRound829Exact as Table
import DASHI.Physics.Closure.NSTriadKNR650Rational345SnapshotNormalizationRound829Exact as R829
import DASHI.Physics.Closure.NSTriadKNR650Rational345CriticalFoldsRound847Exact as R847
import DASHI.Physics.Closure.NSTriadKNR650Rational345GlobalR692Round849Exact as R849

F : C3.RealField _
F = Rational.rationalRealField

module Identify
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  system = Direct.directAuditSystem E I
  physical = Direct.directPhysicalSystem E I

  module Global =
    R692.Expansion physical Active.selected345HelicalScalars
  module Critical = R847.Evaluate unit I
  module Work849 = R849.Evaluate unit I

  repositoryCoherentWork : ℚ
  repositoryCoherentWork = Global.nonzeroGlobalCommutatorWork

  repositoryCriticalProduction : ℚ
  repositoryCriticalProduction = Fold.criticalProductionRate system

  repositoryCriticalDissipation : ℚ
  repositoryCriticalDissipation = Fold.criticalDissipationRate system

  coherentSame :
    repositoryCoherentWork ≡ Table.totalWork
  coherentSame =
    trans
      Work849.globalCoherentWorkExact
      (sym Table.totalWorkExact)

  productionSame :
    repositoryCriticalProduction ≡ Table.totalProduction
  productionSame =
    trans
      Critical.criticalProductionExact
      (sym Table.totalProductionExact)

  dissipationSame :
    repositoryCriticalDissipation ≡ Table.totalDissipation
  dissipationSame =
    trans
      Critical.criticalDissipationExact
      (sym Table.totalDissipationExact)

  snapshotIdentification :
    R829.Repository345SnapshotIdentification
      repositoryCoherentWork
      repositoryCriticalProduction
      repositoryCriticalDissipation
  snapshotIdentification = record
    { R829.coherentWorkSameObject = coherentSame
    ; R829.criticalProductionSameObject = productionSame
    ; R829.criticalDissipationSameObject = dissipationSame
    }

  actualCanonicalRateExact :
    R829.canonicalSignedRate
      repositoryCoherentWork
      repositoryCriticalProduction
      repositoryCriticalDissipation
    ≡ R829.expectedRate345
  actualCanonicalRateExact =
    R829.identifiedCanonicalRateExact
      repositoryCoherentWork
      repositoryCriticalProduction
      repositoryCriticalDissipation
      snapshotIdentification

  actualCanonicalRateNegative :
    R829.canonicalSignedRate
      repositoryCoherentWork
      repositoryCriticalProduction
      repositoryCriticalDissipation
    < 0
  actualCanonicalRateNegative =
    R829.identifiedCanonicalRateNegative
      repositoryCoherentWork
      repositoryCriticalProduction
      repositoryCriticalDissipation
      snapshotIdentification

round850ActualR692SameObjectConsumed : Bool
round850ActualR692SameObjectConsumed = true

round850ActualCriticalProductionSameObjectConsumed : Bool
round850ActualCriticalProductionSameObjectConsumed = true

round850ActualCriticalDissipationSameObjectConsumed : Bool
round850ActualCriticalDissipationSameObjectConsumed = true

round850R829VectorClosed : Bool
round850R829VectorClosed = true

round850InstantaneousActualRepositoryRateStrictlyNegative : Bool
round850InstantaneousActualRepositoryRateStrictlyNegative = true

round850RealFiniteODETransportClosed : Bool
round850RealFiniteODETransportClosed = false

round850UniversalR823IntegratedReserveRefuted : Bool
round850UniversalR823IntegratedReserveRefuted = false

round850ClayPromotion : Bool
round850ClayPromotion = false

round850R829VectorClosedIsTrue :
  round850R829VectorClosed ≡ true
round850R829VectorClosedIsTrue = refl

round850InstantaneousActualRepositoryRateStrictlyNegativeIsTrue :
  round850InstantaneousActualRepositoryRateStrictlyNegative ≡ true
round850InstantaneousActualRepositoryRateStrictlyNegativeIsTrue = refl
