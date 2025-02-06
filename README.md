# veil-usage-example

This repository is an example project that uses
[Veil](https://github.com/verse-lab/veil), a framework for automated
and interactive verification of transition systems embedded in Lean 4.

## Using `veil`

To use `veil` in your project, add the following to your
`lakefile.lean`:

```lean
require "verse-lab" / "veil" @ git "main"
```

Or add the following to your `lakefile.toml`:

```toml
[[require]]
name = "veil"
git = "https://github.com/verse-lab/veil.git"
rev = "main"
```

**Important:** if you use Veil as a library, make sure to also install
`z3`, `cvc5`, Python >= 3.11, and the `z3-solver`, `multiprocess`, and
`sexpdata` Python libraries. See the [Build
section](https://github.com/verse-lab/veil?tab=readme-ov-file#build)
in the Veil repo for detailed instructions.