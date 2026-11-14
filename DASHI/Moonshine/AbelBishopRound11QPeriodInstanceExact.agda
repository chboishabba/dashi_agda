module DASHI.Moonshine.AbelBishopRound11QPeriodInstanceExact where

------------------------------------------------------------------------
-- SAME-SOURCE ORIGINAL ROUND11 q(τ) = exp_C(2π_M i τ).
--
-- Unlike an arbitrary qAt field, the selected q is the actual native
-- Bishop complex exponential from the Round11/Machin owner.  T is
-- addition of the original Bishop complex one, not a synthetic rotation.
--
-- Two genuinely analytic inputs remain explicit:
--   * original q(Tτ) ≈C q(τ), awaiting exp-add and 2π period;
--   * original q radius/unit disk, awaiting trig Pythagorean and norm laws.
-- Neither is fabricated by this constructor.
------------------------------------------------------------------------

import Real as Bishop
import DASHI.Analysis.BishopSetoidComplexExact as Exp
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.AbelBishopOriginalQParameterExact as Q
import DASHI.Moonshine.AbelBishopQSeriesSetoidPeriodTransportExact as Period
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset

originalBishopModularT :
  Series.BishopComplex → Series.BishopComplex
originalBishopModularT tau =
  Weld.toSeries
    (Exp._+C_ (Weld.toExponential tau) Exp.oneC)

originalRound11Q :
  (inputs : Cutset.Round11BishopCutset) →
  Series.BishopComplex → Series.BishopComplex
originalRound11Q = Q.originalRound11MachinQAtForSeries

originalRound11QPeriodSource :
  (inputs : Cutset.Round11BishopCutset) →
  (radius : Series.BishopComplex → Bishop.ℝ) →
  (diskEvidence : ∀ tau →
    Disk.BishopUnitDiskQ (originalRound11Q inputs tau) (radius tau)) →
  (periodEvidence : ∀ tau →
    Series._≈C_
      (originalRound11Q inputs (originalBishopModularT tau))
      (originalRound11Q inputs tau)) →
  Period.OriginalBishopQPeriodSource
originalRound11QPeriodSource inputs radius diskEvidence periodEvidence =
  record
    { Period.Height = Series.BishopComplex
    ; Period.translate = originalBishopModularT
    ; Period.qAt = originalRound11Q inputs
    ; Period.radius = radius
    ; Period.unitDisk = diskEvidence
    ; Period.actualQPeriod = periodEvidence
    }

originalRound11E4TPeriod :
  (inputs : Cutset.Round11BishopCutset) →
  (radius : Series.BishopComplex → Bishop.ℝ) →
  (diskEvidence : ∀ tau →
    Disk.BishopUnitDiskQ (originalRound11Q inputs tau) (radius tau)) →
  (periodEvidence : ∀ tau →
    Series._≈C_
      (originalRound11Q inputs (originalBishopModularT tau))
      (originalRound11Q inputs tau)) →
  (tau : Series.BishopComplex) →
  Series._≈C_
    (E.e4BishopLimit
      (originalRound11Q inputs (originalBishopModularT tau))
      (Disk.unitInterval (diskEvidence (originalBishopModularT tau)))
      (Disk.powerEnvelope (diskEvidence (originalBishopModularT tau))))
    (E.e4BishopLimit
      (originalRound11Q inputs tau)
      (Disk.unitInterval (diskEvidence tau))
      (Disk.powerEnvelope (diskEvidence tau)))
originalRound11E4TPeriod inputs radius diskEvidence periodEvidence tau =
  Period.originalBishopQSeriesTPeriodE4
    (originalRound11QPeriodSource
      inputs radius diskEvidence periodEvidence)
    tau

originalRound11E6TPeriod :
  (inputs : Cutset.Round11BishopCutset) →
  (radius : Series.BishopComplex → Bishop.ℝ) →
  (diskEvidence : ∀ tau →
    Disk.BishopUnitDiskQ (originalRound11Q inputs tau) (radius tau)) →
  (periodEvidence : ∀ tau →
    Series._≈C_
      (originalRound11Q inputs (originalBishopModularT tau))
      (originalRound11Q inputs tau)) →
  (tau : Series.BishopComplex) →
  Series._≈C_
    (E.e6BishopLimit
      (originalRound11Q inputs (originalBishopModularT tau))
      (Disk.unitInterval (diskEvidence (originalBishopModularT tau)))
      (Disk.powerEnvelope (diskEvidence (originalBishopModularT tau))))
    (E.e6BishopLimit
      (originalRound11Q inputs tau)
      (Disk.unitInterval (diskEvidence tau))
      (Disk.powerEnvelope (diskEvidence tau)))
originalRound11E6TPeriod inputs radius diskEvidence periodEvidence tau =
  Period.originalBishopQSeriesTPeriodE6
    (originalRound11QPeriodSource
      inputs radius diskEvidence periodEvidence)
    tau
