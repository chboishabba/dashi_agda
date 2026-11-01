module DASHI.Culture.MissingDeceasedTechnicalExternalisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TechnicalExternalisationDepthBidiExact as X

------------------------------------------------------------------------
-- TECHNICAL EXTERNALISATION DEPTH FIXTURE
------------------------------------------------------------------------

loureiroViriatoExternalisation : X.TechnicalExternalisationProfile
loureiroViriatoExternalisation = X.technical-externalisation-profile
  "Nuno F. G. Loureiro / Viriato"
  ( X.problemStatement
  ∷ X.physicalOrTechnicalModel
  ∷ X.algorithmOrDesignMethod
  ∷ X.implementationArchitecture
  ∷ X.benchmarkOrValidation
  ∷ X.publicInterpretation
  ∷ [] )
  "Loureiro et al., CPC 206 (2016), DOI 10.1016/j.cpc.2016.05.004; MIT PSFC profile; APS DPP abstract"
  "Public sources expose the scientific problem, reduced-gyrokinetic model, numerical algorithms, implementation architecture and benchmark programme. Source-code release is not inferred."

loureiroViriatoDeepExternalisation : X.DeepExternalisation loureiroViriatoExternalisation
loureiroViriatoDeepExternalisation = X.deep-externalisation
  (X.there X.here)
  (X.there (X.there X.here))
  (X.there (X.there (X.there (X.there X.here))))
  "Viriato is a concrete deep-externalisation witness at model/method/validation level."

leblancFspExternalisation : X.TechnicalExternalisationProfile
leblancFspExternalisation = X.technical-externalisation-profile
  "Joshua Kyle LeBlanc / NASA FSP I&C Technology Development Path"
  ( X.problemStatement
  ∷ X.algorithmOrDesignMethod
  ∷ X.publicInterpretation
  ∷ [] )
  "NASA NTRS 20250008475"
  "The public webinar material externalises programme goals and a technology-development path, but the current receipt does not establish deep model+method+validation externalisation or prior restriction."

rezaPatentExternalisation : X.TechnicalExternalisationProfile
rezaPatentExternalisation = X.technical-externalisation-profile
  "Monica Jacinto / Monica Reza / burn-resistant high-strength alloy patent"
  ( X.problemStatement
  ∷ X.physicalOrTechnicalModel
  ∷ X.algorithmOrDesignMethod
  ∷ X.publicInterpretation
  ∷ [] )
  "US20040208777A1 / US10/769,195"
  "The patent externalises the engineering problem, claimed material design/composition and intended technical use; it does not by itself establish manufacturing tacit-knowledge transfer or restricted-to-public release."

maiwaldPublicExternalisation : X.TechnicalExternalisationProfile
maiwaldPublicExternalisation = X.technical-externalisation-profile
  "Frank W. Maiwald / public JPL planetary instrumentation work"
  ( X.problemStatement
  ∷ X.algorithmOrDesignMethod
  ∷ X.publicInterpretation
  ∷ [] )
  "JPL public research/poster and publication record located to date"
  "Public artefacts expose technical aims and some methods, but the current pass does not yet close benchmark/failure/source-artifact depth."

chavezPublicExternalisation : X.TechnicalExternalisationProfile
chavezPublicExternalisation = X.technical-externalisation-profile
  "Anthony Chavez / DARHT-Scorpius public engineering profile"
  ( X.problemStatement
  ∷ X.publicInterpretation
  ∷ [] )
  "LANL National Security Science, Summer 2025 Engineering issue"
  "The public profile explains the engineering role and collaboration at a bounded level; it does not disclose subsystem design authority, detailed implementation or restricted technical content."

rosterExternalisationControls : X.ExternalisationReverseObligation
rosterExternalisationControls = X.externalisation-reverse-obligation
  "declared technical roster"
  X.matchedExternalisationControls
  "pre-register matched peers and score the same problem/model/method/implementation/validation/failure/artifact/public-interpretation stages"
  "whether deep technical externalisation is enriched beyond ordinary publication opportunity"
  "selection, targeting, actor identity or restricted-to-public transfer"
