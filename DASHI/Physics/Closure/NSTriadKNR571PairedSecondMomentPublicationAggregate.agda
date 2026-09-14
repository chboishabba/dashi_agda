module DASHI.Physics.Closure.NSTriadKNR571PairedSecondMomentPublicationAggregate where

-- Single focused check surface for PR #920.
--
-- Canonical publication path:
--   R571 radial same-object weld
--   -> literal +y/-y Round27 pair
--   -> existing Aug-5 centered/second-order identity
--   -> canonical absolute-magnitude PairedSecondMomentSample
--   -> family-scoped second-moment envelope compiler.
--
-- Historical interface note:
-- the Aug-5 PairedSecondMomentBudget stores a finite sample list but quantifies
-- its envelope hypotheses over every possible sample.  The scoped owner below
-- preserves that theorem unchanged and proves the exact finite summation with
-- hypotheses only on members of the declared physical family.
--
-- The generic two-state pair owner remains imported as a reusable adapter, but
-- the one-state opposite-shift path is the preferred physical specialization.
-- No cutoff-uniform physical envelope, fibre-summed, R568 or Clay authority is
-- added here.

import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact
import DASHI.Physics.Closure.NSTriadKNR571OppositeRound27PairedTaylorExact
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorExact
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftSecondMomentRealizationExact
import DASHI.Physics.Closure.NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact
import DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetExact
import DASHI.Physics.Closure.NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterExact

import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationRegression
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationValidation
import DASHI.Physics.Closure.NSTriadKNR571SecondOrderAbsoluteMagnitudeRegression
import DASHI.Physics.Closure.NSTriadKNLuoScopedPairedSecondMomentBudgetRegression
import DASHI.Physics.Closure.NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterRegression
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorRegression
import DASHI.Physics.Closure.NSTriadKNR571OppositeShiftSecondMomentRealizationRegression
