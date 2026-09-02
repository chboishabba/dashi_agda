module DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- LOPEZ-RIOS MARXIST PSYCHOLOGY SOURCE ATLAS
--
-- Attribution boundary:
--   These entries identify external claims and source calibration only.
--   They do not import proofs and do not attribute DASHI's residual,
--   quotient, dependency, fibre, or dialectic theorems to Lopez-Rios.
--
-- Source 1 supports the bounded source claim that Lopez-Rios explicitly
-- presents four contradictions between Marxism and psychology:
--   anti-dialectical/idealist character; apoliticity; servility; and
--   mystification through psychologisation, together with capitalist
--   overdetermination and a stated role for Lacanian psychoanalysis.
--
-- Source 2 supports the bounded source claim that his later positive-
-- psychology critique uses structural causality and treats psychologisation
-- and depoliticisation/privatisation of distress as effects of neoliberalised
-- psychology.
--
-- Everything below that turns those claims into typed non-descent,
-- same-object observation, contextual-role, or intervention invariance
-- theorems is a repo-native DASHI reconstruction/extension.
------------------------------------------------------------------------

fourContradictionsSource : Source.AttributedSource
fourContradictionsSource =
  Source.mkNoDOISource
    "Luis Pablo López-Ríos"
    "Ser marxista en psicología: cuatro contradicciones"
    "Teoría y Crítica de la Psicología 18"
    "2022"
    "https://www.teocripsi.com/ojs/index.php/TCP/article/view/361"
    Source.academicArticleSource
    "source calibration for the named four contradictions and the author's Marxist critique of psychology; does not state DASHI formal theorems"
    Source.publicAttribution

positivePsychologySource : Source.AttributedSource
positivePsychologySource =
  Source.mkDOISource
    "Luis Pablo López-Ríos"
    "La neoliberalización de la psicología y sus efectos devastadores en el sujeto: el caso de la psicología positiva"
    "Castalia - Revista de Psicología de la Academia 44, 143-161"
    "2025"
    "10.25074/07198051.44.2883"
    "https://doi.org/10.25074/07198051.44.2883"
    Source.academicArticleSource
    "source calibration for structural causality, neoliberalisation of psychology, psychologisation, and depoliticisation/privatisation of distress; DASHI causal-fibre formalisation is an extension"
    Source.publicAttribution

lopezRiosSources : List Source.AttributedSource
lopezRiosSources =
  fourContradictionsSource ∷
  positivePsychologySource ∷
  []

lopezRiosSourceAtlas : Source.AttributedSourceAtlas
lopezRiosSourceAtlas =
  Source.mkSourceAtlas
    "Lopez-Rios Marxist psychology source atlas"
    "DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact"
    lopezRiosSources
    "bounded attribution for Lopez-Rios claims used to motivate a repo-native psychologisation / structural-causality reconstruction; citations do not import proof or authority"

lopezRiosSourceAtlasNonPromoting :
  Source.atlasCreatesAuthority lopezRiosSourceAtlas ≡ false
lopezRiosSourceAtlasNonPromoting = refl
