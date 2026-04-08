import Lake
open Lake DSL

package «halo2-kan» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «kan-tactics» from git
  "https://github.com/MavenRain/kan-tactics" @ "db7226bd1f77aeb4e03039452392fd97e576ec00"

@[default_target]
lean_lib Halo2Kan where
  roots := #[`Halo2Kan]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.14.0"
