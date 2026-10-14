module DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Atlas

nov7LocatorKnown :
  Atlas.locatorKnown Atlas.nov7SpokesLocator ≡ true
nov7LocatorKnown = refl

nov9LocatorKnown :
  Atlas.locatorKnown Atlas.nov9SpokesLocator ≡ true
nov9LocatorKnown = refl

nov14LocatorKnown :
  Atlas.locatorKnown Atlas.nov14SpokesLocator ≡ true
nov14LocatorKnown = refl

nov11PathStillPartial :
  Atlas.exactPagePathKnown Atlas.nov11SpokesLocator ≡ false
nov11PathStillPartial = refl

primaryContentStillUnacquired :
  Atlas.primaryContentMaterialised Atlas.canonicalSpokesPrimaryLocatorBoundary ≡ false
primaryContentStillUnacquired = refl

secondaryBibliographyNotPrimaryMinutes :
  Atlas.bibliographicLocatorEqualsPrimaryMinuteContent Atlas.canonicalSpokesPrimaryLocatorBoundary ≡ false
secondaryBibliographyNotPrimaryMinutes = refl
