import Lake
open Lake DSL

package «formal-qkd» {
  -- add any package configuration options here
}

require interval from git
  "https://github.com/adomasbaliuka/interval.git" @ "floor"

lean_lib «FormalQKD» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «formalqkd» where
  root := `Main
