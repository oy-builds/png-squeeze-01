[![make.fun · png-squeeze-01-run-20261127](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127?utm_source=github&utm_medium=readme&utm_campaign=png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/oy-builds/png-squeeze-01/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/oy-builds/png-squeeze-01/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

# png-squeeze-01 — Squeeze screenshots into the smallest PNG

One program (`main.ts`, Node 22, built-ins only) that reads each 1280x720 RGBA
screenshot under `/input/<id>/` and writes a lossless recompressed PNG to
`/output/<id>/image.png`.

How it squeezes:

- **Lossless forms** — palette (by count and by luminance), grey, grey+alpha,
  RGB, RGBA, plus a tRNS transparent-colour key where legal; every form is
  weighed by zlib level 6, as the contest's own scale compressor does.
- **Per-row filter re-selection** — each row's filter (None / Sub / Up /
  Average / Paeth) is re-chosen with this program's own deflate cost model
  (Huffman tables from a first lazy parse), which beats zlib level 4's
  per-row trials as a proxy for the final deflate. A re-selection that makes
  the lazy stream far worse is discarded and the screened data is kept.
- **Two deflates, keep the smaller** — a lazy LZ77 parse with long hash
  chains (4096) and a bounded dynamic-programming optimal parse (zopfli-style:
  longest match, longest match per distance band, and the lazy parse's matches
  as candidates, with lengths trimmed by up to 8). Both emit a single zlib
  stream with optimal package-merge Huffman codes, dynamic or fixed blocks
  per block, and block sizes tried at whole / 256 KiB / 64 KiB.

Deterministic: no clock, no randomness, no network, no files outside
`/input`, `/output` and the program itself — two runs on the same set write
byte-identical outputs. The whole set of 8 runs in about 36 seconds on one
CPU, inside the 60-second wall.

Practice set (kit scorer): **729,862 / 1,000,000**, all 8 instances answered
exactly; the house baseline (fixed-paeth) scores 420,399 on the same set.

## Run

```sh
node main.ts
```

Reads `/input/<id>/image.png`, writes `/output/<id>/image.png`. For local
grading, `MAKEFUN_INPUT_DIR` and `MAKEFUN_OUTPUT_DIR` override the paths.

## License

MIT — see `LICENSE`.
