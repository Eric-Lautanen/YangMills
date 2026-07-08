import Lake
open Lake DSL

package «YangMills» where
  srcDir := "src/lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «YangMills»
