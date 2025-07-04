import Lake
open Lake DSL

package «formal-qkd» {
  -- add any package configuration options here
}

require interval from git
  "https://github.com/girving/interval"

lean_lib «FormalQKD» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «formalqkd» where
  root := `Main

@[test_driver]
lean_lib FormalQKDTests {
  globs := #[.submodules `test]
}
