{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaGoldenEverything where

------------------------------------------------------------------------
-- GOLDEN E20/N21 elementary gamma and zigzag source-only root.
-- Transitive-safe dependency cut: all modules below use only the
-- Agda stdlib and DASHI.FiniteWordSizeExact, which is now --safe.
--
-- Independent acceptance target:
--   agda -i . DASHI/Mathematics/Complexity/Karp21GammaGoldenEverything.agda
--
-- Includes the literal gamma(n+1) binary numerator encoding,
-- structural leading-one/payload-width lemmas, strict signed
-- PARTITION gamma decoding and both zigzag inverse directions.
-- The full numeric gamma encoder/decoder and signed PARTITION source
-- decoder/encoder roundtrips are source-written in this Golden root.
-- Weighted-graph binary transport and polynomial machine clocks remain open.
-- Attribution: Elias gamma code; signed zigzag; Karp 1972;
-- Agda stdlib binary numeral implementation and DASHI codec owners.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.FiniteWordSizeExact
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryPayloadValueExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact

import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact
