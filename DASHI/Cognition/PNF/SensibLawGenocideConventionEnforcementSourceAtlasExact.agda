module DASHI.Cognition.PNF.SensibLawGenocideConventionEnforcementSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Attributed source atlas for genocide-classification and enforcement topology.
-- Metadata identifies sources but does not import legal authority or truth.
------------------------------------------------------------------------

genocideConventionSource : Source.AttributedSource
genocideConventionSource = Source.mkNoDOISource
  "United Nations General Assembly"
  "Convention on the Prevention and Punishment of the Crime of Genocide"
  "United Nations Treaty Series / UN Genocide Prevention official text"
  "1948"
  "https://www.un.org/en/genocide-prevention/1948-convention"
  Source.institutionalSource
  "Articles I-IX: definition, punishment, domestic legislation, tribunals, UN-organ action and ICJ interstate dispute route"
  Source.publicAttribution

unCharterArticle94Source : Source.AttributedSource
unCharterArticle94Source = Source.mkNoDOISource
  "United Nations"
  "Charter of the United Nations, Article 94"
  "United Nations Charter / Office of Legal Affairs"
  "1945"
  "https://legal.un.org/repertory/art94.shtml"
  Source.institutionalSource
  "ICJ judgment compliance obligation and Security Council recourse after non-performance"
  Source.publicAttribution

unCharterArticle27Source : Source.AttributedSource
unCharterArticle27Source = Source.mkNoDOISource
  "United Nations"
  "Charter of the United Nations, Article 27"
  "United Nations Charter, Chapter V: Security Council voting"
  "1945"
  "https://www.un.org/en/about-us/un-charter/chapter-5"
  Source.institutionalSource
  "Security Council substantive voting structure, including permanent-member concurring-vote/veto condition"
  Source.publicAttribution

laGrandSource : Source.AttributedSource
laGrandSource = Source.mkNoDOISource
  "International Court of Justice"
  "LaGrand (Germany v. United States of America), Judgment of 27 June 2001"
  "International Court of Justice Reports 2001"
  "2001"
  "https://www.icj-cij.org/node/103171"
  Source.institutionalSource
  "ICJ holding that Article 41 provisional measures are binding"
  Source.publicAttribution

genocideEnforcementAtlas : Source.AttributedSourceAtlas
genocideEnforcementAtlas = Source.mkSourceAtlas
  "Genocide Convention classification and enforcement source atlas"
  "SensibLawGenocideConventionEnforcementSourceAtlasExact"
  (genocideConventionSource
    ∷ unCharterArticle94Source
    ∷ unCharterArticle27Source
    ∷ laGrandSource
    ∷ [])
  "source identity for Convention elements and enforcement mechanisms; citations do not create applicability, jurisdiction, violation, remedy or enforcement authority"

sourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority genocideEnforcementAtlas ≡ false
sourceAtlasDoesNotCreateAuthority = refl
