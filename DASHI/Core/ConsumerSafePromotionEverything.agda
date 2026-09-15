module DASHI.Core.ConsumerSafePromotionEverything where

-- Focused aggregate for static consumer-safe refinement and future-safe
-- provenance-aware promotion.  Application lanes should import this aggregate
-- rather than duplicating the selection/safety weld.

import DASHI.Core.ConsumerSafeRefinementPromotionExact
import DASHI.Core.ConsumerSafeFuturePromotionExact
