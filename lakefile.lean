import Lake
open Lake DSL

package «mahjong» {
  -- add package configuration options here
}

lean_lib «Mahjong» {
  -- add library configuration options here
}

@[default_target]
lean_exe «mahjong» {
  root := `Main
}
