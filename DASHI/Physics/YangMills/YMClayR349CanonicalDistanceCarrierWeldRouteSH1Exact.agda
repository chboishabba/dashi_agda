{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayR349CanonicalDistanceCarrierWeldRouteSH1Exact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Eliminates the R349 carrier weld when the R304 direct shell is the canonical
-- R398 shell built from the same R318 selected carrier.  Source owners:
-- DASHI/Physics/YangMills/BalabanSelectedDistanceCarrierWeldRound349Exact.agda:40-87
-- DASHI/Physics/YangMills/BalabanR318CanonicalDirectShellRound398Exact.agda:39-89
-- DASHI/Physics/YangMills/YMClayRouteSH1ModeSelectedContinuumUpperExact.agda:72-97
-- This is an interface compiler only; physical H1/decay/closure inputs remain
-- conditional and no Clay promotion is made.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact as R304
import DASHI.Physics.YangMills.BalabanR318CanonicalDirectShellRound398Exact as R398
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1
import DASHI.Physics.YangMills.BalabanSelectedDistanceCarrierWeldRound349Exact as R349
import DASHI.Physics.YangMills.YMClayRouteSH1ModeSelectedContinuumUpperExact as RouteSH1

asR349SelectedDistanceCarrierWeld :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  (inputs : RouteSH1.RouteSH1ModeSelectedInputs
    base tests quantitative family decomposition) →
  R349.SelectedDistanceCarrierWeld
    base tests quantitative family decomposition
    (RouteSH1.asR304ModeSelectedPayment {base = base} inputs)
asR349SelectedDistanceCarrierWeld {base = base} {tests = tests}
    {decomposition = decomposition} inputs =
  record
    { R349.SelectedDistanceCarrierWeld.r318DistanceIsR284Distance =
        λ observable time →
          let index = R300.indexFor decomposition observable time in
          sym
            (R398.canonicalDirectShellDistanceIsR318
              base
              (H1.directSelectedDecay (RouteSH1.h1 inputs))
              (R278.left tests index)
              (R278.right tests index))
    }

canonicalR349WeldCompilerLevel : ProofLevel
canonicalR349WeldCompilerLevel = machineChecked
