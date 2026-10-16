# Directional marked affine source at 0.874836

The four-page [paper](paper.pdf) explains the all-moduli boundary
`218709/250000 = 0.874836`. [paper.tex](paper.tex) and [status.tex](status.tex)
are the exact rendered sources. Tectonic 0.15.0 renders them with
`tectonic --keep-logs paper.tex`.

The closed endpoint passed local Lean checking with only `Classical.choice`,
`Quot.sound` and `propext`. Clean packaged replay, canonical comparison and
independent-kernel checks are pending. No tracker admission is claimed.

The companion result submission supplies `Candidate.bound` under
`submissions/gao-directional-affine-20261016/src/Candidate/Main.lean`,
with finite-order Hecke and zeta consequences as well. This paper-only branch
publishes the documents; interpret canonical source paths in the result
submission tree.

[paper-receipt.json](paper-receipt.json) binds the exact document sources,
PDF, render log and formula ledgers. Its local endpoint receipts and
[formula-bindings.json](formula-bindings.json) refer to original module paths
before the import-only canonical relocation. [canonical-source-bindings.json](canonical-source-bindings.json)
maps each binding to the exact committed source and records both hashes.
These document receipts do not certify a clean packaged replay.

[loss-ledger-verification.json](loss-ledger-verification.json) records the
separate HIGH source/raw charges and the ERROR reserve-halving identity.
The full inequalities are proved in the accompanying Lean source.

Zhongpai Gao, with AI assistance. This work builds on OpenAI, Hailey Collet,
Akash Levy, timbalud and DaysSky; inherited notices and licenses remain in
the source. The fixed LOW incumbent is the accepted 0.874840 result from PR60.
