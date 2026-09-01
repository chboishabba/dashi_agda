module DASHI.Finance.MarketBraidCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.PNFBraidTransportField as PNF
import DASHI.Finance.TemporalMarketFibreExact as Market
import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb

------------------------------------------------------------------------
-- Cross-pollination boundary.
--
-- The finance lane reuses the braid doctrine (partial temporal transport,
-- residual retention, explicit receipts, no authority creation) but does not
-- identify market fibres with PNF semantic fibres.  Same transport geometry
-- does not imply same semantic object.
------------------------------------------------------------------------

record MarketPNFBraidDoctrine : Set where
  constructor marketPNFBraidDoctrine
  field
    temporalTransportIsPartial : Bool
    temporalTransportIsPartialIsTrue : temporalTransportIsPartial ≡ true

    residualsSurviveProjection : Bool
    residualsSurviveProjectionIsTrue : residualsSurviveProjection ≡ true

    transportCreatesAuthority : Bool
    transportCreatesAuthorityIsFalse : transportCreatesAuthority ≡ false

    sameGeometryImpliesSameSemanticCarrier : Bool
    sameGeometryImpliesSameSemanticCarrierIsFalse :
      sameGeometryImpliesSameSemanticCarrier ≡ false

open MarketPNFBraidDoctrine public

canonicalMarketPNFBraidDoctrine : MarketPNFBraidDoctrine
canonicalMarketPNFBraidDoctrine =
  marketPNFBraidDoctrine true refl true refl false refl false refl

record StructuralCrossPollinationReceipt : Set where
  constructor structuralCrossPollinationReceipt
  field
    pnfResidualGate : PNF.ResidualTransportGate
    financeAuthorityBoundary : Market.FibreAuthorityBoundary
    financeSharpeBoundary : StatArb.SharpeAuthorityBoundary
    receiptLabel : String
    assertsCarrierIdentity : Bool
    assertsCarrierIdentityIsFalse : assertsCarrierIdentity ≡ false

open StructuralCrossPollinationReceipt public

canonicalStructuralCrossPollinationReceipt : StructuralCrossPollinationReceipt
canonicalStructuralCrossPollinationReceipt =
  structuralCrossPollinationReceipt
    PNF.residualMayContinue
    Market.canonicalFibreAuthorityBoundary
    StatArb.canonicalSharpeAuthorityBoundary
    "PNF braid doctrine structurally cross-pollinated into finance: partial transport, residual retention, receipt-bearing navigation, no authority creation"
    false refl

crossPollinationBoundaryStatement : String
crossPollinationBoundaryStatement =
  "The market lane and PNF lane share transport doctrine, not carrier identity: equal braid geometry does not identify their semantic fibres or transfer authority between them."
