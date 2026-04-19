import Lake
open Lake DSL

require «mathlib» from git "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

require «Duper» from git "https://github.com/leanprover-community/duper.git" @ "a05206eadfece7682abf44d52e8fd8c7110ef58a"

require «premise-selection» from git "https://github.com/hanwenzhu/premise-selection" @ "v4.29.0"

package QuerySMT {
  precompileModules := false
  preferReleaseBuild := false
}

@[default_target]
lean_lib QuerySMT
