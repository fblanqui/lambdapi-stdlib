Non-Opaque Lambdapi Source Copy
===============================

This directory contains the non-opaque Lambdapi standard-library copy used by
the Leo-III proof-to-Rocq pipeline.

The repository root keeps the upstream standard-library source layout and
package root:

```
root_path = Stdlib
```

This subdirectory provides the unfolded translation dependency:

```
root_path = Stdlib-noOp
```

The proof pipeline rewrites proof imports from `Stdlib` to `Stdlib-noOp` and
uses this directory for Lambdapi-to-Dedukti export.
