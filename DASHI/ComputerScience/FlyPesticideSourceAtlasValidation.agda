module DASHI.ComputerScience.FlyPesticideSourceAtlasValidation where

import DASHI.ComputerScience.FlyPesticideSourceAtlasExact as Atlas

-- Focused source/attribution contract. The production owner is required to
-- expose literature roles spanning neural/cognitive, reproductive,
-- genotoxic, mixture/environmental, and resistance/behaviour observations,
-- while retaining publication and organism identities separately.

sourceAtlas : Atlas.FlyPesticideSourceAtlas
sourceAtlas = Atlas.canonicalFlyPesticideSourceAtlas

organismIdentityPaid : Bool
organismIdentityPaid = Atlas.organismIdentityPaid sourceAtlas

publicationIdentitiesRetained : Bool
publicationIdentitiesRetained = Atlas.publicationIdentitiesRetained sourceAtlas

articleQidsMayRemainUnresolved : Bool
articleQidsMayRemainUnresolved = Atlas.articleQidsMayRemainUnresolved sourceAtlas

citationCreatesToxicologyAuthority : Bool
citationCreatesToxicologyAuthority = Atlas.citationCreatesToxicologyAuthority sourceAtlas

samePesticideCreatesSameEndpoint : Bool
samePesticideCreatesSameEndpoint = Atlas.samePesticideCreatesSameEndpoint sourceAtlas
