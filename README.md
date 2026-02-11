# veil-usage-example

This repository is an example project that uses
[Veil](https://github.com/verse-lab/veil), a framework for automated
and interactive verification of transition systems embedded in Lean 4.

## Veil 2.0 Pre-Release

You are looking at a pre-release version of Veil 2.0, the upcoming major
version of Veil. There are still quite a few bugs and rough edges.

If you encounter issues, please [report them to
us](https://github.com/verse-lab/veil/issues/new), so we can fix them before
the release. Your patience and feedback are greatly appreciated!

You can ask questions on the [Veil
channel](https://leanprover.zulipchat.com/#narrow/channel/537982-Veil) on the
Lean Zulip, and we will be happy to answer.


## Using `veil`

To use `veil` in your project, add the following to your
`lakefile.lean`:

```lean
require "verse-lab" / "veil" @ git "veil-2.0-preview"
```

Or add the following to your `lakefile.toml`:

```toml
[[require]]
name = "veil"
git = "https://github.com/verse-lab/veil.git"
rev = "veil-2.0-preview"
```
