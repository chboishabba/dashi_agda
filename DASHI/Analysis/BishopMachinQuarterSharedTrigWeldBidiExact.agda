module DASHI.Analysis.BishopMachinQuarterSharedTrigWeldBidiExact where

------------------------------------------------------------------------
-- K05: REUSE THE ORIGINAL SHARED ROUND11 CLASSICAL/BISHOP TRIG WELD.
--
-- Actual original owners:
--   DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact
--   DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact
--   DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact
--   DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact
--
-- Under ONE source-owned and EXPLICIT same-object weld, the Round11
-- Pythagorean theorem supplies the corresponding quarter-angle unit
-- phase. We then reuse the existing polynomial quadruplication and
-- setoid transport to the original Bishop Machin real.
--
-- No new source truth, generic pi, trigonometry identity, unbounded
-- classical/Bishop equality, or existence of the weld is assumed.
-- Source: NIST DLMF 4.21.12 (Pythagorean); Machin 1706;
-- Bishop & Bridges (1985), DOI 10.1007/978-3-642-61667-9;
-- Murray (2022), arXiv:2205.08354. Original repo proof
-- reconstruction and source/weld authors remain independently owned.
--
-- Status: source-written Agda, not kernel verified. K05 still owes
-- (1) actual Machin quarter sin=cos, (2) native fourfold sine/cosine
-- addition, (3) independently characterised geometric pi uniqueness.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_)

import Real as Bishop
import RealProperties as RP

import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Round11
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as Weld
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Phase
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin

module AtExistingRound11Weld
  (P : Round11.Round11FactorInterchangeProblem)
  (W : Weld.Round11ClassicalTrigObjectWeld P)
  where

  inputs = Round11.round11 P

  -- Same literal Round11 elementary-series dataSet by definition:
  -- Phase.quarterSin/quarterCos use the canonical Machin route-B
  -- instance, whose dataSet is Round11.elementarySeries inputs.
  quarterSin : Bishop.ℝ
  quarterSin = Phase.quarterSin inputs

  quarterCos : Bishop.ℝ
  quarterCos = Phase.quarterCos inputs

  -- The existing weld, not a new theorem authority or postulate,
  -- provides sin²+cos²=1 at the true Bishop Machin quarter.
  -- Only commutativity is needed to match Phase's cos²+sin² order.
  quarterUnitFromOriginalSharedWeld :
    Bishop._≃_
      (Bishop._+_
        (Bishop._*_ quarterCos quarterCos)
        (Bishop._*_ quarterSin quarterSin))
      Bishop.1ℝ
  quarterUnitFromOriginalSharedWeld =
    RP.≃-trans
      (RP.+-comm
        (Bishop._*_ quarterCos quarterCos)
        (Bishop._*_ quarterSin quarterSin))
      (Weld.compileRound11Pythagorean P W
        Quarter.machinQuarterAngle)

  -- There is no extra unit-phase hypothesis here. The two remaining
  -- analytic K05 premises are at exactly the ORIGINAL Bishop series.
  quarterWeldedTrigEndpoint :
    Bishop._≃_ quarterCos quarterSin →
    Bishop._≃_
      (Phase.round11Sine inputs Phase.fourTimesQuarter)
      (Phase.sinFourfoldPolynomial quarterCos quarterSin) →
    Bishop._≃_
      (Phase.round11Cos inputs Phase.fourTimesQuarter)
      (Phase.cosFourfoldPolynomial quarterCos quarterSin) →
    (Bishop._≃_
      (Phase.round11Sine inputs Machin.bishopMachinPi)
      Bishop.0ℝ)
    ×
    (Bishop._≃_
      (Phase.round11Cos inputs Machin.bishopMachinPi)
      (Bishop.-_ Bishop.1ℝ))
  quarterWeldedTrigEndpoint quarterEqual sinQuad cosQuad =
    Phase.quarterSemanticBridgeToActualMachinPi
      inputs
      quarterEqual
      quarterUnitFromOriginalSharedWeld
      sinQuad
      cosQuad
