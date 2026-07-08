import Lake
open Lake DSL

package «YangMills» where
  srcDir := "src/lean"

@[default_target]
lean_lib «YangMills»
