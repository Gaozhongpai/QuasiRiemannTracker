# Affine detector counting with asymmetric source savings

The canonical all-moduli Dirichlet bound **21871/25000 = 0.874840**, excluding the principal pole, is **officially verified and admitted to QuasiRiemannTracker**. [PR #60](https://github.com/GTimG/QuasiRiemannTracker/pull/60) was merged on **15 October 2026**.

Read [the four-page paper](paper.pdf), [TeX source](paper.tex), and the [official tracker certificate](https://gtimg.github.io/QuasiRiemannTracker/certificates/gao-affine-asymmetric-20261015.json).

The official certificate records final source head `3874f3e75de18ff5806dcb9519fc260e034ef0e9`: [complete proof entry](https://github.com/GTimG/QuasiRiemannTracker/blob/3874f3e75de18ff5806dcb9519fc260e034ef0e9/submissions/gao-affine-asymmetric-20261015/src/Candidate/Main.lean). It records verification at `2026-10-15T09:17:19.521444+00:00` by Lean default, NanoDa and con-ron, with [official verification run 38698872054](https://github.com/GTimG/QuasiRiemannTracker/actions/runs/38698872054/attempts/1). PR #60 was merged as `cb1bd454a095a35ea93c63a9d4702e001b706a42`.

The [historical public local-verification receipt](public-receipt.json) remains bound to the earlier source head `74643447f52a2df4d05cbb23f50b9e6f2959beaa`: [historical proof entry](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/74643447f52a2df4d05cbb23f50b9e6f2959beaa/submissions/gao-affine-asymmetric-20261015/src/Candidate/Main.lean). Its metadata SHA256 is `4f9c511cb392b5d41304e1b469b5f7d30946da3a8cb35be1727c2d2ab53bb997`. The maintainer's final source head adds predecessor metadata to that locally verified head.

For that historical local verification, all 897 candidate Lean modules were compiled from source in the parent replay. Its metadata-only follow-up reused an authenticated local compilation cache and ran fresh controls, canonical exports and Comparator/Lean/NanoDa/con-ron verification. The checked target is `QRH.canonical_bound`, with only `Classical.choice`, `Quot.sound` and `propext`. The local receipt binds that earlier head, source and export hashes; its compilation and cache details describe the local replay. The official verification is documented by the separate tracker certificate and run linked above.

The [receipt generator](generate-receipt.py) uses the [pinned historical local-verification binding](expected-verification.json). It verifies actual completed replay artifacts and emits only safe fields and hashes, excluding private profiles, library inventories, tool paths and raw logs.

These paper artifacts are hosted separately from the upstream result PR, whose changes contain only the submission metadata and Lean source.

Zhongpai Gao, with AI assistance. OpenAI, Hailey Collet, Akash Levy, timbalud and DaysSky credits are retained; related affine-count arithmetic by liqsweep/blueberryvertigo is acknowledged in the paper. The manuscript and integration are Apache-2.0, subject to retained predecessor and dependency licenses.
