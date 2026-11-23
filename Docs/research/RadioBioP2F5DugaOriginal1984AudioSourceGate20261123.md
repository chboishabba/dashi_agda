# P2-F5 — 1984 Woodpecker receiver-audio primary object located

**23 November 2026. Original-audio *object discovered*; original bytes NOT obtained in current runtime.** This replaces the claim that no surviving historical Duga observation is findable, without upgrading an uncalibrated audio recording to calibrated HF I/Q or original transmitter data.

## Direct source and original author

- **Original signal audio:** [Wikimedia Commons original `Woodpecker.ogg`](https://commons.wikimedia.org/wiki/File:Woodpecker.ogg). File attribution **Rolypolyman**, date of reception/recording **2 November 1984**, description: Soviet Woodpecker interference with the **WWVH** shortwave reference station. The Commons upload version is **1 June 2007**; source describes ~**21 seconds**, **Ogg Vorbis**, ~**167 KB**, labelled public domain by uploader. These are metadata asserted by the archive, not independently validated original content or recorder provenance. This is not a raw RF capture.
- **Independent rediscovery:** [Shortwave Radio Audio Archive, 23 October 2026 republication](https://shortwavearchive.com/archive/russian-woodpecker-duga-1-heard-behind-wwvh-november-2-1984), contributor **Andronicus** attributes the sound to the Commons file and the 1984 date. The 2026 article is a **mirror/republication of the same original audio**, not a second independent 1984 receiver measurement or a separate signal trace. It also links a derivative MP3 at archive.org, which should not be substituted for original OGG without a provenance and transcoding flag.
- **Retrieval status:** web reader shows original object and file link but does not ingest `application/ogg`; direct `upload.wikimedia.org` request from the local container failed DNS resolution, so **0 original bytes acquired**, no reliable SHA-256, no direct audio periodicity/quality or original WWVH overlay analysis. The original file URL listed on Commons is `https://upload.wikimedia.org/wikipedia/commons/5/5b/Woodpecker.ogg`. **Do not repeat this blocked network path without a new access route.**
- **Hardware and physics distinction:** the recording is receiver-produced **audible/demodulated** output mixed with WWVH, and Ogg compression affects the waveform. It cannot yield 1984 radar source power, received flux calibrated in W/m², original transmitted HF carrier phase, true ionospheric transfer, original receiver gain/polarization or human exposure. A detected 10-Hz rhythm is a **local signal timing** observation, not a direct 10-Hz propagating field source.

## Original-audio replay path

[New conditional file-based replay](../../scripts/radiobio_p2_duga_archived_audio_replay.py) expects an original `OggS` signature, preserves SHA-256/size/audio rate/duration, produces a 6–25 Hz periodicity peak from the audio Hilbert envelope, and explicitly excludes calibrated physical claims. Without `--original-ogg`, it runs a **separate synthetic** 400-Hz carrier amplitude-modulated at 10 Hz in 2,000 Hz sampled audio for 3 seconds. A local NumPy/SciPy/SymPy equivalent fixture detected **10.0 Hz** and checked the `field→k field, gain→gain/k` non-identifiability. This is **not a local execution of the exact newly committed script**, and not a reproduction of the 1984 source waveform.

The helper can run locally with:

`python scripts/radiobio_p2_duga_archived_audio_replay.py --original-ogg path/to/Woodpecker.ogg`

Only after the original file has been copied by a legitimate available access route should it produce an original-audio receipt. An audio-envelope peak may depend strongly on WWVH overlap, recording bandwidth, nonlinear receiver detection, Ogg codec and exposure to switching/transients; do not equate a peak with Duga transmitter parameters.

## Source-to-receiver physical gate remains open

Existing P2-F3/F4 [source clock](RadioBioP2DugaPrimarySoviet1991AndReceiver1985Weld20261123.md) and [receiver-energy bound](RadioBioP2DugaHFReceiverPowerIdentifiability20261123.md) require **calibrated** HF observation of frequencies, receiver gain, timing, antenna effective area, source-path attenuation, power loading, and original RF I/Q where available. The 1984 audio is a valuable original receiver *qualitative timing artifact*—not a payment for these physical measurements.

**Attribution:** original Rolypolyman observation and Shortwave Radio Audio Archive curator, earlier Monitoring Times and Babakin sources, and existing DASHI owners remain distinct. **No GitHub CI/Actions**, no Agda kernel, no user-facing clinical or national-security inference. The earlier Dryad SCENAR resource stays listed and PAUSED rather than retried.
