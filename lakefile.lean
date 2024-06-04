import Lake
open Lake DSL

package glimpseOfLean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, true⟩]

@[default_target]
lean_lib GlimpseOfLean where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
