import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "2ed404f5823ac9adfaf41e812eb2f846a37c289b"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.29.0"

package QuerySMT {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib QuerySMT
