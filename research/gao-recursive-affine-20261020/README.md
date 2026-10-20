# Regional affine source component

This directory checks the actual regional main-source driver. It is a research component, not a leaderboard submission. The endpoint and the complete recursive source producer remain unproved here.

The Lean theorem keeps a regional LOW return in the native physical source operator with its actual normalizing coefficient. Its continuing-source hypothesis still has to be constructed from deeper physical sources. Passing this check verifies that theorem's stated conditional source interface; it does not remove the hypothesis or establish a new zero-free boundary.

The workflow runs on pushes to `gao-regional-affine-proof-20261020` or by manual dispatch. It uses the original pinned `verifier/actions/setup.py --warm-cache`, then checks only this driver's source dependency closure. It does not export a canonical endpoint, run Comparator or independent kernels, modify the catalogue, or claim tracker admission.

The driver is in [RegionalMainDriver.lean](src/Candidate/Research/RecursiveAffine/RegionalMainDriver.lean). The native source closure is locked to the reviewed PR67 source tree at `0db497edc397d7076b1652b060e49c76b683e901` by [source-lock.json](source-lock.json). The official dependency-graph implementation computes the actual closure; its synthetic import-only `Candidate.Main` selects this component and is not compiled as an endpoint.

The checking script authenticates the public server compilation cache using the pinned Ed25519 public key and exact signed-index/archive hashes. It requires the actual compiler and normalized package-library hashes to match the signed environment. Every OpenAI baseline module must also have its exact source/dependency cache key restored. A mismatch fails before any baseline source rebuild. The explicitly locked Candidate modules and Akash Levy source modules are then compiled coherently from source. For the initial driver this means 2,923 cached baseline modules, 226 Akash modules, and 597 Candidate modules, of which two Candidate modules also match the signed cache.

The final axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The CI artifact contains source hashes, the exact module graph, cache compatibility evidence, compiler logs, the axiom report, and an optional archive of this run's Candidate/Akash compiler products. That product archive is a component build aid, not a signed admission certificate.

To inspect the source graph without provisioning Lean or compiling anything:

```sh
python3 research/gao-recursive-affine-20261020/check_component.py --plan-only
```

After the original warm-cache setup, run the source check with:

```sh
python3 research/gao-recursive-affine-20261020/check_component.py
```

Use a fresh `--work` directory for a new full component check. Changes to the driver's proof body do not require a native lock update. If its native import closure changes, review the changed native sources before regenerating the lock with `--plan-only --write-source-lock`.

This component check runs remotely so it does not repeat the full local proof replay. The first hosted run may need to build the pinned package environment; later runs can restore that environment on this fork. Signed archive downloads are cached only after authentication.
