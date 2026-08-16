module DASHI.Physics.Closure.NSTriadKNABCComLegacyEnvelopeAdapterRound60Exact where

------------------------------------------------------------------------
-- COMPILER / COMPATIBILITY BOUNDARY
--
-- The canonical Round60 ABC source boundary now depends only on the
-- lightweight normalized odd-(P/Q) source and its 133/256 squared endpoint.
-- This module contains the optional historical Round47/42 Com envelope
-- transport for consumers that genuinely need it.
--
-- No mathematical hypothesis is added: the adapter is definitionally fed by
-- the same `comSource` field of `LiteralABCSourceWitnesses`.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNABCInhabitationRound58Exact as ABC
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceAdapterRound58 as BAdapter
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support

literalComEnvelope :
  (source : ABC.LiteralABCSourceWitnesses) →
  Support.PhysicalComSupportOverlapEnvelope
literalComEnvelope source =
  BAdapter.legacyEnvelope (ABC.comSource source)
