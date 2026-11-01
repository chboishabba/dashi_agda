module DASHI.Education.DigitalESDPhilosophySeededAcquisitionProbeRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDPhilosophySeededAcquisitionProbeExact as Probe

probeNotEvidence : Probe.PhilosophyProbeCreatesEmpiricalEvidence → ⊥
probeNotEvidence = Probe.philosophyProbeDoesNotCreateEmpiricalEvidence

probeNotAuthority : Probe.PhilosophyProbeCreatesAuthority → ⊥
probeNotAuthority = Probe.philosophyProbeDoesNotCreateAuthority

probeNotMandatoryAxis : Probe.PhilosophyProbeCreatesMandatoryAuditAxis → ⊥
probeNotMandatoryAxis = Probe.philosophyProbeDoesNotCreateMandatoryAuditAxis
