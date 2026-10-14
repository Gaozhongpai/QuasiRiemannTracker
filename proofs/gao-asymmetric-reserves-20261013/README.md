# Asymmetric reserve allocation at 0.8748673

The exact proposed bound is **8748673/10000000 = 0.8748673**. The canonical theorem covers every positive modulus and every complex Dirichlet character, excluding only `χ = 1 ∧ s = 1`. Read the concise [three-page mathematical note](paper.pdf), with its [TeX source](paper.tex).

The complete Lean source is in [`Candidate.Main`](../../submissions/gao-asymmetric-reserves-20261013/src/Candidate/Main.lean) and its [127 supporting bundles](../../submissions/gao-asymmetric-reserves-20261013/src/Candidate/Bundles/). Apply the theorem with `Candidate.bound χ hs hpole`.

The proof enlarges the permitted affine local-moment defect to **1/241** by assigning different amounts to the raw LOW reserve, auxiliary fees, and retained saving:

| Quantity | Exact value |
| --- | --- |
| Raw LOW reserve | 1/46000 |
| Paid auxiliary fee budget | 1/2000000 |
| Retained LOW saving | 1/48000 |
| Common tiny loss | 1/100000000 |
| Extracted-error reserve | 1/1250 |

The actual raw reserve at defect 1/241 is 301/13556250. It exceeds 1/46000, and `1/46000 − 1/2000000 − 1/48000 = 7/17250000 > 0`. After eleven tiny fees, `1/48000 − 11/100000000 − 1/50000 = 217/300000000 > 0`. The amplifier remains 3/500, the source-volume cap remains 881/1000, and the final LOW and extracted-error saving powers are retained.

The complete source preserves the actual weighted coefficient packet, coprimality, ramified labels, Euler deletions, independent plain heights, coherent amplification, joint row reconstruction, and cancellation through the first-kernel errors. The capacity change is transported through the actual source and physical wrappers, with coefficient dilation repaid by the original weighted mass. The analytic source is proved internally and supplied to continuation; it is not an additional hypothesis of the endpoint theorem.

The linked geometry is θ = 8748673/10000000, ℓ = 1253981/7500000, h = 397/500, and κ = 3748673/5000000. It retains θ = 11/12 − ℓ/4 and κ = 2θ − 1. Regenerated exact certificates retain top reserve 1/2000000, junction reserve 1/10000, half-height reserve 1/100, and full-row reserve 1/3000000. The separate conservative transport estimate uses anchor 874867/1000000 and retains reserve 1/2000. Full rational coefficient tables are in [endpoint-coefficients.json](endpoint-coefficients.json).

The baseline source is Kari Roegnvaldsson's accepted affine-capacity submission at `c707738a659786b9a44a79c629bed8c801cca8f3`. The preceding reserve-allocation source is pinned to PR 38 at `14ab1618c5133a7d12e06aa76661bbcb34e843cd`. That snapshot was unverified when preparation began; PR 38 has since been accepted and merged. Our complete source replay and independent Comparator/Lean/NanoDa/con-ron checks have now passed locally. The [verification summary](verification-summary.json) records their status and exact scope. Upstream admission requires exact-head hosted verification and merge.

The frozen candidate inventory contains **128 Lean files, 6,715,524 bytes**. Its source-manifest SHA256 is `0b7e783fd6a60d098ebe094d1383d2db762d796c3ed3b27da0a272722481fb2f`. Component arithmetic checks apply to extracted mathematical bodies. All 128 bundled modules, five final axiom audits and the independent kernel checks passed. Hosted tracker admission remains pending.

This asymmetric reserve allocation and endpoint adaptation are by Zhongpai Gao, with AI assistance. Kari Roegnvaldsson introduced the affine capacity and preceding reserve reallocation. Nielstron supplied the complete local 22/5 analytic proof at `16ce30342471344c2b2f0d383388e6f9acb9bccf`. Further predecessors include OpenAI (`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`), Akash Levy (`2fd60c0926b66ea18d7436f5ed55250fd006ab5d`), Hailey Collet's Cycle25 development, and Gao's earlier adapters (`44e93fbcac36bfd10cc1316674c970747888d448`). Apache-2.0 and original notices are retained; dependencies retain their own authorship and licenses.

Text and compressed local-verification receipts are redacted publication derivatives. The [publication redaction manifest](publication-redactions.json) binds their original and published file hashes, and both decompressed member hashes for gzip receipts. Original recorded verification hashes and verdicts describe the historical proof runs. This metadata-only revision preserves every Lean source byte and protected verifier file; it has not received a fresh exact-head hosted proof check.
