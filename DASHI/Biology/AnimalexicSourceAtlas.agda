module DASHI.Biology.AnimalexicSourceAtlas where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

kellerPointFusion : Source.AttributedSource
kellerPointFusion =
  Source.mkDOISource
    "Maik Keller; Damien Lefloch; Martin Lambers; Shahram Izadi; Tim Weyrich; Andreas Kolb"
    "Real-time 3D Reconstruction in Dynamic Scenes using Point-based Fusion"
    "3DV 2013" "2013" "10.1109/3DV.2013.9"
    "https://doi.org/10.1109/3DV.2013.9"
    Source.academicArticleSource
    "surfel/point fusion vocabulary; citation imports no Animalexic theorem"
    Source.publicAttribution

elasticFusion : Source.AttributedSource
elasticFusion =
  Source.mkDOISource
    "Thomas Whelan; Stefan Leutenegger; Renato F. Salas-Moreno; Ben Glocker; Andrew J. Davison"
    "ElasticFusion: Dense SLAM Without A Pose Graph"
    "Robotics: Science and Systems XI" "2015" "10.15607/RSS.2015.XI.001"
    "https://doi.org/10.15607/RSS.2015.XI.001"
    Source.academicArticleSource
    "active/inactive surfel and incremental map-refinement vocabulary"
    Source.publicAttribution

dynamicFusion : Source.AttributedSource
dynamicFusion =
  Source.mkDOISource
    "Richard A. Newcombe; Dieter Fox; Steven M. Seitz"
    "DynamicFusion: Reconstruction and Tracking of Non-Rigid Scenes in Real-Time"
    "CVPR 2015" "2015" "10.1109/CVPR.2015.7298631"
    "https://doi.org/10.1109/CVPR.2015.7298631"
    Source.academicArticleSource
    "canonical/deformed geometry and non-rigid re-registration vocabulary"
    Source.publicAttribution

voxelHashing : Source.AttributedSource
voxelHashing =
  Source.mkDOISource
    "Matthias Niessner; Michael Zollhoefer; Shahram Izadi; Marc Stamminger"
    "Real-time 3D Reconstruction at Scale using Voxel Hashing"
    "ACM Transactions on Graphics / SIGGRAPH Asia" "2013"
    "10.1145/2508363.2508374"
    "https://doi.org/10.1145/2508363.2508374"
    Source.academicArticleSource
    "spatial-hashing/locality vocabulary; citation does not prove runtime correctness"
    Source.publicAttribution

deepLabCut : Source.AttributedSource
deepLabCut =
  Source.mkDOISource
    "Alexander Mathis; Pranav Mamidanna; Kevin M. Cury; Taiga Abe; Venkatesh N. Murthy; Mackenzie Weygandt Mathis; Matthias Bethge"
    "DeepLabCut: markerless pose estimation of user-defined body parts with deep learning"
    "Nature Neuroscience" "2018" "10.1038/s41593-018-0209-y"
    "https://doi.org/10.1038/s41593-018-0209-y"
    Source.academicArticleSource
    "markerless pose observation adapter; pose output is not communicative meaning"
    Source.publicAttribution

sleap : Source.AttributedSource
sleap =
  Source.mkDOISource
    "Talmo D. Pereira et al."
    "SLEAP: A deep learning system for multi-animal pose tracking"
    "Nature Methods" "2022" "10.1038/s41592-022-01426-1"
    "https://doi.org/10.1038/s41592-022-01426-1"
    Source.academicArticleSource
    "multi-animal pose/identity observation adapter"
    Source.publicAttribution

allenIntervals : Source.AttributedSource
allenIntervals =
  Source.mkDOISource
    "James F. Allen" "Maintaining Knowledge about Temporal Intervals"
    "Communications of the ACM" "1983" "10.1145/182.358434"
    "https://doi.org/10.1145/182.358434"
    Source.academicArticleSource
    "interval-relation vocabulary; transition and causality semantics remain separate"
    Source.publicAttribution

mhtRevisited : Source.AttributedSource
mhtRevisited =
  Source.mkDOISource
    "Chanho Kim; Fuxin Li; Arridhana Ciptadi; James M. Rehg"
    "Multiple Hypothesis Tracking Revisited"
    "ICCV 2015" "2015" "10.1109/ICCV.2015.533"
    "https://doi.org/10.1109/ICCV.2015.533"
    Source.academicArticleSource
    "deferred-association/live-hypothesis vocabulary"
    Source.publicAttribution

keypointMoseq : Source.AttributedSource
keypointMoseq =
  Source.mkDOISource
    "Caleb Weinreb et al."
    "Keypoint-MoSeq: parsing behavior by linking point tracking to pose dynamics"
    "Nature Methods" "2024" "10.1038/s41592-024-02318-2"
    "https://doi.org/10.1038/s41592-024-02318-2"
    Source.academicArticleSource
    "unsupervised pose-dynamics/event-syllable adapter; syllable does not entail meaning"
    Source.publicAttribution

rabbaniRegionGrowing : Source.AttributedSource
rabbaniRegionGrowing =
  Source.mkNoDOISource
    "Tahmineh Rabbani; Frank van den Heuvel; George Vosselman"
    "Segmentation of Point Clouds using Smoothness Constraint"
    "ISPRS Commission V Symposium" "2006"
    "https://www.isprs.org/proceedings/xxxvi/part5/paper/RABB_639.pdf"
    Source.academicArticleSource
    "normal/curvature constrained region-growing vocabulary"
    Source.publicAttribution

dellaertFactorGraphs : Source.AttributedSource
dellaertFactorGraphs =
  Source.mkNoDOISource
    "Frank Dellaert" "Factor Graphs and GTSAM: A Hands-on Introduction"
    "Georgia Institute of Technology technical tutorial" "2012"
    "https://gtsam.org/tutorials/intro.html"
    Source.academicArticleSource
    "factor-graph/incremental-state-estimation vocabulary; probabilistic semantics are not forced"
    Source.publicAttribution

equifacs : Source.AttributedSource
equifacs =
  Source.mkDOISource
    "Jennifer Wathan; Anne M. Burrows; Bridget M. Waller; Karen McComb"
    "EquiFACS: The Equine Facial Action Coding System"
    "PLOS ONE" "2015" "10.1371/journal.pone.0131738"
    "https://doi.org/10.1371/journal.pone.0131738"
    Source.academicArticleSource
    "species-grounded facial action vocabulary; action unit does not prove affect or intent"
    Source.publicAttribution

teglasGaze : Source.AttributedSource
teglasGaze =
  Source.mkDOISource
    "Erno Teglas; Anna Gergely; Krisztina Kupan; Adam Miklosi; Jozsef Topal"
    "Dogs' Gaze Following Is Tuned to Human Communicative Signals"
    "Current Biology" "2012" "10.1016/j.cub.2011.12.018"
    "https://doi.org/10.1016/j.cub.2011.12.018"
    Source.academicArticleSource
    "ostensive-cue/gaze evidence; not a universal communication theorem"
    Source.publicAttribution

animalexicSources : List Source.AttributedSource
animalexicSources =
  kellerPointFusion ∷ elasticFusion ∷ dynamicFusion ∷ voxelHashing
  ∷ deepLabCut ∷ sleap ∷ allenIntervals ∷ mhtRevisited ∷ keypointMoseq
  ∷ rabbaniRegionGrowing ∷ dellaertFactorGraphs ∷ equifacs ∷ teglasGaze ∷ []

animalexicSourceAtlas : Source.AttributedSourceAtlas
animalexicSourceAtlas =
  Source.mkSourceAtlas
    "Animalexic embodied communication source atlas"
    "DASHI.Biology.AnimalexicSourceAtlas"
    animalexicSources
    "bounded methodology provenance for reconstruction, pose, temporal events, ambiguity management, and animal communication; source identity imports no theorem, benchmark claim, or semantic authority"

record AnimalexicSourceBoundary : Set where
  constructor animalexicSourceBoundary
  field
    reconstructionSourceDoesNotProveAnimalexicRuntime : Bool
    poseSourceDoesNotProveBehaviourMeaning : Bool
    behaviourSegmentationDoesNotProveCommunication : Bool
    gazeAssociationDoesNotProveIntent : Bool
    citationDoesNotAuthorizeLexiconEntry : Bool

open AnimalexicSourceBoundary public

canonicalAnimalexicSourceBoundary : AnimalexicSourceBoundary
canonicalAnimalexicSourceBoundary =
  animalexicSourceBoundary true true true true true
