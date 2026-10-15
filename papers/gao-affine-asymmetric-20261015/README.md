# Affine detector counting with asymmetric source savings

The canonical all-moduli Dirichlet bound **21871/25000 = 0.874840**, excluding the principal pole, has passed local canonical comparison and all three independent kernels. **Official tracker admission remains pending.**

Read [the four-page paper](paper.pdf), [TeX source](paper.tex), and [public local-verification receipt](public-receipt.json).

The accepted source head is `74643447f52a2df4d05cbb23f50b9e6f2959beaa`: [complete proof entry](https://github.com/Gaozhongpai/QuasiRiemannTracker/blob/74643447f52a2df4d05cbb23f50b9e6f2959beaa/submissions/gao-affine-asymmetric-20261015/src/Candidate/Main.lean). Its metadata SHA256 is `4f9c511cb392b5d41304e1b469b5f7d30946da3a8cb35be1727c2d2ab53bb997`.

All 897 candidate Lean modules were compiled from source in the parent replay. The final metadata-only head reused an authenticated local compilation cache and ran fresh controls, canonical exports and Comparator/Lean/NanoDa/con-ron verification. The checked target is `QRH.canonical_bound`, with only `Classical.choice`, `Quot.sound` and `propext`. The receipt binds the exact final head, source and export hashes. Local proof acceptance is distinct from the tracker's checks, review and admission.

The [receipt generator](generate-receipt.py) uses the [pinned verification binding](expected-verification.json). It verifies actual completed replay artifacts and emits only safe fields and hashes, excluding private profiles, library inventories, tool paths and raw logs.

These paper artifacts are hosted separately from the upstream result PR, whose changes contain only the submission metadata and Lean source.

Zhongpai Gao, with AI assistance. OpenAI, Hailey Collet, Akash Levy, timbalud and DaysSky credits are retained; related affine-count arithmetic by liqsweep/blueberryvertigo is acknowledged in the paper. The manuscript and integration are Apache-2.0, subject to retained predecessor and dependency licenses.
