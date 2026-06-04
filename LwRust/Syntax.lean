import LwRust.Core.Syntax

/-!
Compatibility module.

The previous `LwRust.Syntax` file described an unrelated toy language. The
Featherweight Rust translation now lives under `LwRust.Core` and
`LwRust.Extensions`; this module re-exports the core syntax for callers that
still import `LwRust.Syntax`.
-/
