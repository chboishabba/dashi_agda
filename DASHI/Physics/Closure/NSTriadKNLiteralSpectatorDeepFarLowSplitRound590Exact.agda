module DASHI.Physics.Closure.NSTriadKNLiteralSpectatorDeepFarLowSplitRound590Exact where

-- Repository-native extension of R545 (literal one-weight spectator rows),
-- R186 (outer Bony classification), and R589 (physical shell mask/fold split).
-- Baseline provenance: dashi_agda commit 6cd63dcd7cda24cddb641ee7326143cf33ed01dd.
-- This does not replace the spectator by a weighted aggregate as in R440.
-- Only the forcing half is split. No estimate or historical region identity
-- is asserted, and the complementary region still needs signed control.
-- Draft source; Agda execution deferred by user instruction.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Bool.Base using (not)
open import Data.Rational.Base using (_+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNLiveOuterSignedCrossDecompositionRound589Exact as R589

deepOuterFarLow590 : Physical.PhysicalTriadIncidence → Bool
deepOuterFarLow590 tau with R186.partnerBonyClass tau
... | R186.farLowClass = R589.deepFarLow589 tau
... | R186.highHighClass = false
... | R186.comparableClass = false

module SpectatorSplit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R589.F)
    (S : Helical.HelicalModeScalars R589.F) where

  module Row = R545.Row physicalSystem S

  module At (beta : Physical.PhysicalTriadIncidence)
      (items : List Physical.PhysicalTriadIncidence) where

    value = Row.Weighted.Force.weightedDouble beta
    deep = R224.foldVector (R589.masked589 deepOuterFarLow590 value) items
    remainder = R224.foldVector
      (R589.masked589 (λ tau → not (deepOuterFarLow590 tau)) value) items

    literalForcingHalfDeepSplit590 :
      Row.forcingHalf beta items
      ≡ R179.realHermitianCross deep (Row.doubleCell beta)
        + R179.realHermitianCross remainder (Row.doubleCell beta)
    literalForcingHalfDeepSplit590 = trans (Row.forcingHalfFactors beta items)
      (trans
        (cong (λ vector → R179.realHermitianCross vector (Row.doubleCell beta))
          (R589.splitFold589 deepOuterFarLow590 value items))
        (R291.realCrossAddLeft deep remainder (Row.doubleCell beta)))
