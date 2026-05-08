# Rocq Translation Support

This directory contains the current Rocq support files for the Lambdapi/Dedukti-to-Rocq experiments.

## Support Files

- `encoding.lp`
  Encoding file passed to Lambdapi's `stt_coq` exporter.
- `mappings.lp`
  Symbol mapping file used during Rocq export.
- `mappings.v`
  Rocq shim/support module. It contains both direct correspondence definitions and workaround lemmas/definitions used by the currently checked translation slice.

There are two copies of `mappings.v` on purpose. The root copy belongs to the exporter support files. The copy in `partial_stdlib/` makes the checked snapshot self-contained, so `make partial-stdlib` can compile the snapshot directly from its own directory.

## Partial Standard Library Snapshot

The directory `partial_stdlib/` contains the currently checked partial Rocq translation snapshot. It is intentionally separate from the root support files.

It currently includes:

- core stdlib translation files,
- `Disj.v` and `Conj.v`,
- checked shim-backed `Bool.v` and `Nat.v` modules,
- `order.txt`, the order used by `coqc`.

To check this snapshot:

```bash
make partial-stdlib
```

The Makefile uses the modern `rocq compile` entry point by default. If a local installation only exposes the older `coqc` command, use:

```bash
make partial-stdlib ROCQ_COMPILE=coqc
```

## Current Manual Workarounds

The current pipeline is not a clean direct export yet. Important workarounds are:

- `opaque` modifiers are removed before DK export so proofs can be materialized.
- Unicode symbols in `encoding.lp` and `mappings.lp` often need Dedukti quoted-identifier syntax such as `{|π|}`. This is an artifact of the Dedukti detour; a direct Lambdapi-to-Rocq path should not need these wrappers in the same way.
- Some mapping entries use explicit Rocq constant names such as `@proj2` or `@conj`. This compensates for names as they appear after the Dedukti/Rocq export path, where implicit arguments and fully elaborated constants are exposed more often than in ordinary Lambdapi source.
- DK rewrite rules with an empty context are dropped before Rocq export because they currently make the Lambdapi Rocq exporter fail. Lambdapi otherwise normally detects and omits rewrite rules when exporting DK files to Rocq.
- Some stdlib symbols/theorems are mapped to Rocq shim definitions in `mappings.v` instead of translating their original proof terms. This now includes `disj`, `conj`, `preserves_contents`, `insertBot`, and `insertBots`.
- The current proof pipeline skips DK object checking by default (`SKIP_DK_CHECK=1`) because freshly exported DK stdlib files currently expose a Dedukti rewrite-rule/static-symbol issue.

## Known Limitations

- This is a checked partial slice, not a complete checked translation of the whole Lambdapi standard library.
- Nat/List are only covered to the extent needed by the current checked standard-library slice. The full generated Nat proof file does not currently check against native Rocq nat because several Lambdapi/Dedukti rewrite-rule computations are not definitional in Rocq.
- `mappings.v` still contains one admitted lemma, `subset_undup_first`.

## Bool/Nat Shim Diagnosis

`Bool.v` and `Nat.v` are not merely small because the current snapshot is partial. Their direct translated proof terms expose a real mismatch between Lambdapi/Dedukti rewriting and native Rocq computation.

For Bool, disabling the Bool theorem shim mappings makes the generated `Bool.v` fail at `orC`. The generated proof uses `eq_refl` for a goal of the shape:

```coq
orb true x = orb x true
```

In Lambdapi/Dedukti, both sides reduce to `true`, because the source rewrite system includes rules such as `or x true --> true`. In Rocq, native `orb` computes by inspecting its first argument, so `orb true x` reduces to `true`, but `orb x true` is stuck when `x` is a variable.

For Nat, disabling the Nat theorem shim mappings makes the generated Nat file fail already at `addn1`, whose goal has the shape:

```coq
Nat.add n 1 = S n
```

In Lambdapi/Dedukti, this was definitional by rewrite rules. In Rocq, native `Nat.add` recurses on its first argument, so `Nat.add n 1` is stuck when `n` is a variable. Rocq can prove the theorem, but it is not true by computation, so the generated `eq_refl` proof term is not enough.

Thus many Bool/Nat shims compensate for rewrite-rule computation that is lost when mapping Lambdapi symbols to native Rocq `bool` and `nat`. Some individual Nat lemmas may still be translatable with better mappings, but the issue is not only that this snapshot is partial: mapping to native Rocq changes what counts as obvious by reduction.
