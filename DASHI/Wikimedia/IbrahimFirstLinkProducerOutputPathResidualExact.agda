module DASHI.Wikimedia.IbrahimFirstLinkProducerOutputPathResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimFirstLinkNovember06ProducerPathStrengtheningExact as November06

------------------------------------------------------------------------
-- PRODUCER OUTPUT-PATH RESIDUAL
--
-- The public v4 producer/launcher and combiner agree on the 112-way indexed
-- execution shape but disagree on the directory carrying the numbered JSONs:
--
--   create_fln.py : /users/m/s/msibrahi/v4/results/true_flnetwork/{i}.json
--   combine_fln.py: /users/m/s/msibrahi/v4/results/flnetwork/{i}.json
--
-- Downstream v4 analysis consumes flnetwork/fln.json.  No committed move/copy/
-- rename receipt from true_flnetwork to flnetwork has been recovered.  Therefore
-- output-path identity remains a same-object dependency rather than a typo we
-- are allowed to repair historically.
------------------------------------------------------------------------

november06Boundary : November06.November06StrengtheningBoundary
november06Boundary = November06.canonicalNovember06StrengtheningBoundary

createFlnSource : Attribution.AttributedSource
createFlnSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/create_fln.py"
  "marksibrahim/wikipedia_network; blob 595f7f52ffc03e8a9542964b9dd3fffbfae87fca"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/create_fln.py"
  (Attribution.namedSourceKind "producer FLN shard constructor")
  "enumerates the 112 small*.xml input namespace and writes numbered JSON outputs under v4/results/true_flnetwork; source evidence for producer shape, not proof that this exact revision/path was the publication run"
  Attribution.publicAttribution

runFlnSource : Attribution.AttributedSource
runFlnSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/run_fln.py"
  "marksibrahim/wikipedia_network; blob 3dc34cd8d28ac35c6762110fe7619456a083567a"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/run_fln.py"
  (Attribution.namedSourceKind "producer cluster launcher")
  "generates and qsubs 112 indexed PBS jobs invoking create_fln.py; pays the committed 112-job execution topology, not historical successful completion or result identity"
  Attribution.publicAttribution

combineFlnSource : Attribution.AttributedSource
combineFlnSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/combine_fln.py"
  "marksibrahim/wikipedia_network; blob 47cf92622c9f88472149e8115df5da84264ed10d"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/combine_fln.py"
  (Attribution.namedSourceKind "producer FLN shard combiner")
  "loads numbered JSONs 0..111 from v4/results/flnetwork, merges them into one dictionary, and writes flnetwork/fln.json; path conflicts with committed create_fln.py output directory"
  Attribution.publicAttribution

record OutputPathResidualReceipt : Set where
  constructor output-path-residual-receipt
  field
    producerInputCount112 : Bool
    launcherJobCount112 : Bool
    combinerInputCount112 : Bool
    combinerWritesFlnJson : Bool
    producerWritesTrueFlnetwork : Bool
    combinerReadsFlnetwork : Bool
    downstreamUsesFlnetwork : Bool
    committedMoveCopyRenameReceiptRecovered : Bool
    exactExecutedRevisionRecovered : Bool
    numberedShardHashesRecovered : Bool
    combinedFlnHashRecovered : Bool
open OutputPathResidualReceipt public

canonicalOutputPathResidual : OutputPathResidualReceipt
canonicalOutputPathResidual = output-path-residual-receipt
  true true true true true true true false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SimilarDirectoryNameMeansSameObject : Set where
data SameShardCountMeansSameShardBytes : Set where
data SameFlnFilenameMeansPublishedSameObject : Set where
data CommittedCodeMeansExecutedRevision : Set where

similarDirectoryNameDoesNotPaySameObject : SimilarDirectoryNameMeansSameObject → ⊥
similarDirectoryNameDoesNotPaySameObject ()

sameShardCountDoesNotPaySameBytes : SameShardCountMeansSameShardBytes → ⊥
sameShardCountDoesNotPaySameBytes ()

sameFlnFilenameDoesNotPayPublishedSameObject : SameFlnFilenameMeansPublishedSameObject → ⊥
sameFlnFilenameDoesNotPayPublishedSameObject ()

committedCodeDoesNotPayExecutedRevision : CommittedCodeMeansExecutedRevision → ⊥
committedCodeDoesNotPayExecutedRevision ()

remainingOutputPathPayment : String
remainingOutputPathPayment =
  "Recover an execution/custody receipt connecting create_fln.py's true_flnetwork numbered outputs to combine_fln.py's flnetwork numbered inputs, or recover the exact historically executed source revision showing a consistent path. Then obtain shard/result hashes. Until then, the 112-job topology and 112-way combination are source-paid, but the committed producer-to-combiner same-object edge is not."

record ProducerOutputPathBoundary : Set where
  constructor producer-output-path-boundary
  field
    indexed112TopologyPaid : Bool
    producerCombinerDirectoryMismatchRetained : Bool
    directoryMismatchSilentlyRepaired : Bool
    executedRevisionStillRequired : Bool
    shardHashesStillRequired : Bool
    resultHashStillRequired : Bool
open ProducerOutputPathBoundary public

canonicalProducerOutputPathBoundary : ProducerOutputPathBoundary
canonicalProducerOutputPathBoundary = producer-output-path-boundary
  true true false true true true
