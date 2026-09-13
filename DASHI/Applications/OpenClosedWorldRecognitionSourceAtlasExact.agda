module DASHI.Applications.OpenClosedWorldRecognitionSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source

scheirerEtAl2013 : Source.AttributedSource
scheirerEtAl2013 =
  Source.mkDOISource
    "Walter J. Scheirer; Anderson de Rezende Rocha; Archana Sapkota; Terrance E. Boult"
    "Toward Open Set Recognition"
    "IEEE Transactions on Pattern Analysis and Machine Intelligence 35(7), 1757-1772"
    "2013"
    "10.1109/TPAMI.2012.256"
    "https://doi.org/10.1109/TPAMI.2012.256"
    Source.academicArticleSource
    "foundational source for the distinction between closed-set recognition, where all test classes are known during training, and open-set recognition, where unknown classes may appear at test time; also source for open-space-risk formalisation"
    Source.publicAttribution

scheirerJainBoult2014 : Source.AttributedSource
scheirerJainBoult2014 =
  Source.mkDOISource
    "Walter J. Scheirer; Lalit P. Jain; Terrance E. Boult"
    "Probability Models for Open Set Recognition"
    "IEEE Transactions on Pattern Analysis and Machine Intelligence 36(11), 2317-2324"
    "2014"
    "10.1109/TPAMI.2014.2321392"
    "https://doi.org/10.1109/TPAMI.2014.2321392"
    Source.academicArticleSource
    "source for compact-abating-probability/open-space-risk treatment of multiclass open-set recognition; not a source for incremental open-world learning"
    Source.publicAttribution

bendaleBoult2015 : Source.AttributedSource
bendaleBoult2015 =
  Source.mkNoDOISource
    "Abhijit Bendale; Terrance Boult"
    "Towards Open World Recognition"
    "Proceedings of the IEEE Conference on Computer Vision and Pattern Recognition, 1893-1902"
    "2015"
    "https://openaccess.thecvf.com/content_cvpr_2015/html/Bendale_Towards_Open_World_2015_CVPR_paper.html"
    Source.academicArticleSource
    "foundational source distinguishing open-set recognition from open-world recognition by adding explicit unknown handling plus incremental incorporation of newly labelled categories"
    Source.publicAttribution

gengHuangChen2021 : Source.AttributedSource
gengHuangChen2021 =
  Source.mkDOISource
    "Chuanxing Geng; Sheng-Jun Huang; Songcan Chen"
    "Recent Advances in Open Set Recognition: A Survey"
    "IEEE Transactions on Pattern Analysis and Machine Intelligence 43(10), 3614-3631"
    "2021"
    "10.1109/TPAMI.2020.2981604"
    "https://doi.org/10.1109/TPAMI.2020.2981604"
    Source.academicArticleSource
    "survey source for open-set recognition definitions, evaluation, related tasks, and the treatment of open-world recognition as an extension rather than a synonym"
    Source.publicAttribution

josephEtAl2021 : Source.AttributedSource
josephEtAl2021 =
  Source.mkDOISource
    "K. J. Joseph; Salman Khan; Fahad Shahbaz Khan; Vineeth N. Balasubramanian"
    "Towards Open World Object Detection"
    "2021 IEEE/CVF Conference on Computer Vision and Pattern Recognition"
    "2021"
    "10.1109/CVPR46437.2021.00577"
    "https://doi.org/10.1109/CVPR46437.2021.00577"
    Source.academicArticleSource
    "source for open-world object detection as unknown-object identification plus localization and incremental class learning without forgetting known classes"
    Source.publicAttribution

wangVazeHan2025 : Source.AttributedSource
wangVazeHan2025 =
  Source.mkDOISource
    "Hongjun Wang; Sagar Vaze; Kai Han"
    "Dissecting Out-of-Distribution Detection and Open-Set Recognition: A Critical Analysis of Methods and Benchmarks"
    "International Journal of Computer Vision 133, 1326-1351"
    "2025"
    "10.1007/s11263-024-02222-4"
    "https://doi.org/10.1007/s11263-024-02222-4"
    Source.academicArticleSource
    "source for keeping out-of-distribution detection and open-set recognition distinct despite overlapping test-time distribution-shift concerns"
    Source.publicAttribution

liEtAl2025 : Source.AttributedSource
liEtAl2025 =
  Source.mkDOISource
    "Yiming Li; Yi Wang; Wenqian Wang; Dan Lin; Bingbing Li; Kim-Hui Yap"
    "Open World Object Detection: A Survey"
    "IEEE Transactions on Circuits and Systems for Video Technology 35(2), 988-1008"
    "2025"
    "10.1109/TCSVT.2024.3480691"
    "https://doi.org/10.1109/TCSVT.2024.3480691"
    Source.academicArticleSource
    "survey source for open-world object detection, its relation to open-set recognition and incremental learning, and benchmark/evaluation distinctions"
    Source.publicAttribution

wangEtAl2025 : Source.AttributedSource
wangEtAl2025 =
  Source.mkDOISource
    "Ke Wang; Zhikang Li; Yang Chen; Wenjie Dong; Junlan Chen"
    "Towards open-world recognition: Critical problems and challenges"
    "Engineering Applications of Artificial Intelligence 143, 110042"
    "2025"
    "10.1016/j.engappai.2025.110042"
    "https://doi.org/10.1016/j.engappai.2025.110042"
    Source.academicArticleSource
    "survey source for dynamic open-world recognition, unknown rejection, incremental learning, changing categories, incomplete annotation, and the distinction between closed-set assumptions and open-world operation"
    Source.publicAttribution

openClosedWorldSources : List Source.AttributedSource
openClosedWorldSources =
  scheirerEtAl2013 ∷
  scheirerJainBoult2014 ∷
  bendaleBoult2015 ∷
  gengHuangChen2021 ∷
  josephEtAl2021 ∷
  wangVazeHan2025 ∷
  liEtAl2025 ∷
  wangEtAl2025 ∷
  []

openClosedWorldSourceAtlas : Source.AttributedSourceAtlas
openClosedWorldSourceAtlas =
  Source.mkSourceAtlas
    "open/closed-set and open-world recognition literature"
    "DASHI.Applications.OpenClosedWorldRecognitionSourceAtlasExact"
    openClosedWorldSources
    "source-bounded distinctions among closed-set recognition, open-set recognition, OOD detection, open-world recognition, and open-world object detection; citations do not import proofs, identify any RF emitter, or validate any vendor implementation"

openClosedWorldSourceAtlasCreatesAuthority : Bool
openClosedWorldSourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority openClosedWorldSourceAtlas

openClosedWorldSourceAtlasCreatesAuthorityIsFalse :
  openClosedWorldSourceAtlasCreatesAuthority ≡ false
openClosedWorldSourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse openClosedWorldSourceAtlas

record OpenClosedWorldAttributionBoundary : Set where
  constructor openClosedWorldAttributionBoundary
  field
    paperIdentityEqualsImportedProof : Bool
    paperIdentityEqualsImportedProofIsFalse :
      paperIdentityEqualsImportedProof ≡ false
    conceptualAnalogyEqualsHistoricalIdentity : Bool
    conceptualAnalogyEqualsHistoricalIdentityIsFalse :
      conceptualAnalogyEqualsHistoricalIdentity ≡ false
    generalOpenWorldPaperValidatesDroneShield : Bool
    generalOpenWorldPaperValidatesDroneShieldIsFalse :
      generalOpenWorldPaperValidatesDroneShield ≡ false

canonicalOpenClosedWorldAttributionBoundary : OpenClosedWorldAttributionBoundary
canonicalOpenClosedWorldAttributionBoundary =
  openClosedWorldAttributionBoundary false refl false refl false refl
