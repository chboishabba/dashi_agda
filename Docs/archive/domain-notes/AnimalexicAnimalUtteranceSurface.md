# Animalexic Animal Utterance Surface

`DASHI.Biology.AnimalexicAnimalUtteranceSurface` is a typed observation and
promotion boundary for animal utterances.

The surface does not treat a sound as a word. It stages interpretation as:

1. multimodal observation of an utterance event;
2. candidate latent body and social state construction;
3. admissibility and provenance gates backed by receipts;
4. promoted behavioural meaning.

The promoted object is a behavioural meaning, not a recovered private
experience, human-language translation, or species-universal dictionary entry.

## Rejected Routes

The Agda module names three blocked promotion routes:

- direct sound-to-word semantics;
- direct qualia recovery;
- promotion without receipts.

Only `multimodalLatentReceiptRoute` is admissible. The other routes reduce to
the empty `Never` type through `AdmissibleRoute`.

## Receipt Discipline

`AnimalexicPromotionReceipt` requires:

- a receipt matching the observation and latent candidate;
- a multimodal completeness gate;
- a provenance admissibility gate;
- a provenance trail;
- an explicit route equality to the receipt-backed promotion route.

`promoteWithReceipts` therefore exposes behavioural meaning only after the
candidate latent state and receipt have been supplied.
