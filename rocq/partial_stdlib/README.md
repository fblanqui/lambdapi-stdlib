# Partial Stdlib Rocq Snapshot

This directory contains the currently checked Rocq snapshot of the translated standard-library slice.

Check it with:

```bash
xargs -n1 coqc < order.txt
```

or from the parent `rocq/` directory:

```bash
make partial-stdlib
```

The files are generated/curated outputs from the current pipeline, not hand-maintained source files. `Bool.v` and `Nat.v` are currently shim-backed modules: most of their usable content lives in `mappings.v` because the direct translated proof terms rely on Lambdapi/Dedukti rewrite-rule computation that native Rocq does not reproduce definitionally.

This directory contains its own copy of `mappings.v` so the snapshot can be checked directly with the local `order.txt`. The root `rocq/mappings.v`, `rocq/mappings.lp`, and `rocq/encoding.lp` are the support files used to reproduce or update this kind of output.
