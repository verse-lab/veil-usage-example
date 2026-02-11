# veil-usage-example

This repository is an example project that uses
[Veil](https://github.com/verse-lab/veil), a framework for automated
and interactive verification of transition systems embedded in Lean 4.

## New: Veil 2.0 Preview!

The upcoming version of Veil is coming soon, with vastly improved user
experience and a TLC-style explicit state model checker.

The usage example for Veil 2.0 is available on the
[`veil-2.0-preview`](https://github.com/verse-lab/veil-usage-example/tree/veil-2.0-preview)
branch.

Try it out! (And do [let us know](https://github.com/verse-lab/veil/issues/new) if you encounter issues.)

You can ask questions on the [Veil
channel](https://leanprover.zulipchat.com/#narrow/channel/537982-Veil) on the
Lean Zulip, and we will be happy to answer.

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
