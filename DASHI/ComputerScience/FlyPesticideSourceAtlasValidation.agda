module DASHI.ComputerScience.FlyPesticideSourceAtlasValidation where

import DASHI.ComputerScience.FlyPesticideSourceAtlasExact as Atlas

-- Focused source/attribution contract for the shared source atlas. Longitudinal
-- chlorpyrifos acquisition is validated by its own owner so its generation/time
-- role cannot be flattened into a generic endpoint-family flag.

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
