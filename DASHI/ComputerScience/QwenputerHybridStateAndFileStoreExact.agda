module DASHI.ComputerScience.QwenputerHybridStateAndFileStoreExact where

-- Attribution: Divyansh Agrawal (2026), Qwenputer v0.1.0.
-- https://github.com/divagr18/qwenputer
-- https://github.com/divagr18/qwenputer/blob/main/docs/q35-store.md
-- https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md
-- The finite ownership and file-store interpreter is a DASHI extension.
-- It is NOT the source's hash-directory, chained-chunk memory layout,
-- tokenizer, exact model checkpoint, or empirical storage benchmark.
-- The restored cache is a mathematical value, not a validated HF cache.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
import DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact as GDN

------------------------------------------------------------------------
-- State ownership: compiled tokens do not mutate the original language
-- state; language tokens do not mutate the compiled RAM state.
------------------------------------------------------------------------

data TokenOwner : Set where
  languageOwns : TokenOwner
  circuitOwns : TokenOwner

record HybridState (LanguageState ChipState : Set) : Set where
  constructor hybridState
  field
    language : LanguageState
    chip : ChipState
open HybridState public

route :
  {L C : Set} → TokenOwner → (L → L) → (C → C) →
  HybridState L C → HybridState L C
route languageOwns languageStep circuitStep s =
  hybridState (languageStep (language s)) (chip s)
route circuitOwns languageStep circuitStep s =
  hybridState (language s) (circuitStep (chip s))

circuitTraceMutesLanguage :
  {L C : Set} (languageStep : L → L) (circuitStep : C → C)
  (s : HybridState L C) →
  language (route circuitOwns languageStep circuitStep s) ≡ language s
circuitTraceMutesLanguage languageStep circuitStep s = refl

languageTracePreservesChip :
  {L C : Set} (languageStep : L → L) (circuitStep : C → C)
  (s : HybridState L C) →
  chip (route languageOwns languageStep circuitStep s) ≡ chip s
languageTracePreservesChip languageStep circuitStep s = refl

-- Same computational claim as source's mute, only at an abstract state
-- boundary. Actual attention, convolution, RMSNorm, bf16 and KV/DeltaNet
-- cache equality are separate source-specific proof debts.

snapshotChip : {L C : Set} → HybridState L C → C
snapshotChip = chip

restoreChip : {L C : Set} → L → C → HybridState L C
restoreChip = hybridState

restoredSnapshotExact :
  {L C : Set} (freshLanguage : L) (old : HybridState L C) →
  chip (restoreChip freshLanguage (snapshotChip old)) ≡ chip old
restoredSnapshotExact freshLanguage old = refl

restoredLanguageIsFresh :
  {L C : Set} (freshLanguage : L) (old : HybridState L C) →
  language (restoreChip freshLanguage (snapshotChip old)) ≡ freshLanguage
restoredLanguageIsFresh freshLanguage old = refl

------------------------------------------------------------------------
-- A small executable named-file API. Names are finite typed addresses.
-- Source Qwenputer's larger store uses hash lookup and chunk chains.
------------------------------------------------------------------------

data FileName : Set where
  fileA fileB fileC : FileName

sameName : FileName → FileName → Bool
sameName fileA fileA = true
sameName fileA fileB = false
sameName fileA fileC = false
sameName fileB fileA = false
sameName fileB fileB = true
sameName fileB fileC = false
sameName fileC fileA = false
sameName fileC fileB = false
sameName fileC fileC = true

sameNameRefl : (name : FileName) → sameName name name ≡ true
sameNameRefl fileA = refl
sameNameRefl fileB = refl
sameNameRefl fileC = refl

FileContents : Set
FileContents = List Bool

FileStore : Set
FileStore = FileName → Maybe FileContents

emptyStore : FileStore
emptyStore name = nothing

get : FileStore → FileName → Maybe FileContents
get store name = store name

replace : FileStore → FileName → Maybe FileContents → FileStore
replace store target value query with sameName target query
... | true = value
... | false = store query

put : FileStore → FileName → FileContents → FileStore
put store name value = replace store name (just value)

delete : FileStore → FileName → FileStore
delete store name = replace store name nothing

appendContents : FileContents → FileContents → FileContents
appendContents [] ys = ys
appendContents (x ∷ xs) ys = x ∷ appendContents xs ys

append : FileStore → FileName → FileContents → FileStore
append store name suffix with get store name
... | nothing = put store name suffix
... | just prefix = put store name (appendContents prefix suffix)

data FileEntry : Set where
  entry : FileName → FileContents → FileEntry

listEntries : FileStore → List FileEntry
listEntries store with get store fileA | get store fileB | get store fileC
... | nothing | nothing | nothing = []
... | just a | nothing | nothing = entry fileA a ∷ []
... | nothing | just b | nothing = entry fileB b ∷ []
... | nothing | nothing | just c = entry fileC c ∷ []
... | just a | just b | nothing = entry fileA a ∷ entry fileB b ∷ []
... | just a | nothing | just c = entry fileA a ∷ entry fileC c ∷ []
... | nothing | just b | just c = entry fileB b ∷ entry fileC c ∷ []
... | just a | just b | just c =
  entry fileA a ∷ entry fileB b ∷ entry fileC c ∷ []

getAfterPut :
  (store : FileStore) (name : FileName) (value : FileContents) →
  get (put store name value) name ≡ just value
getAfterPut store name value rewrite sameNameRefl name = refl

getAfterDelete :
  (store : FileStore) (name : FileName) →
  get (delete store name) name ≡ nothing
getAfterDelete store name rewrite sameNameRefl name = refl

getOtherAfterPut :
  (store : FileStore) (written observed : FileName) (value : FileContents) →
  sameName written observed ≡ false →
  get (put store written value) observed ≡ get store observed
getOtherAfterPut store written observed value different
  rewrite different = refl

getAfterAppendToMissing :
  (name : FileName) (suffix : FileContents) →
  get (append emptyStore name suffix) name ≡ just suffix
getAfterAppendToMissing name suffix = getAfterPut emptyStore name suffix

getAfterAppendToExisting :
  (store : FileStore) (name : FileName)
  (prefix suffix : FileContents) →
  get store name ≡ just prefix →
  get (append store name suffix) name ≡
    just (appendContents prefix suffix)
getAfterAppendToExisting store name prefix suffix hasValue
  rewrite hasValue = getAfterPut store name (appendContents prefix suffix)

-- Concrete regression: put, append, delete, get, list are all executable.
sampleStore : FileStore
sampleStore = append (put emptyStore fileA (true ∷ []))
  fileA (false ∷ true ∷ [])

sampleRead :
  get sampleStore fileA ≡ just (true ∷ false ∷ true ∷ [])
sampleRead = refl

sampleListing :
  listEntries sampleStore ≡
    entry fileA (true ∷ false ∷ true ∷ []) ∷ []
sampleListing = refl

sampleDelete : get (delete sampleStore fileA) fileA ≡ nothing
sampleDelete = refl

------------------------------------------------------------------------
-- Explicit persistence and state separation: no assertion that the source
-- snapshot is a model cache serialisation or that inter-session access is
-- secure, authorised, isolated, or performant.
------------------------------------------------------------------------

record FileSession (L : Set) : Set where
  constructor fileSession
  field
    languageState : L
    files : FileStore
open FileSession public

saveFiles : {L : Set} → FileSession L → FileStore
saveFiles = files

newConversation : {L : Set} → L → FileStore → FileSession L
newConversation = fileSession

filesSurviveNewConversation :
  {L : Set} (s : FileSession L) (freshLanguage : L) (name : FileName) →
  get (files (newConversation freshLanguage (saveFiles s))) name
  ≡ get (files s) name
filesSurviveNewConversation s freshLanguage name = refl

data StoreProofBoundary : Set where
  finitePutGetDeleteAppendListProved : StoreProofBoundary
  qwenputerHashAndChunkSameObjectOpen : StoreProofBoundary
  productionCacheSerializationOpen : StoreProofBoundary

canonicalStoreBoundary : List StoreProofBoundary
canonicalStoreBoundary =
  finitePutGetDeleteAppendListProved
  ∷ qwenputerHashAndChunkSameObjectOpen
  ∷ productionCacheSerializationOpen ∷ []
