# QuerySMT

QuerySMT is a Lean tactic which interfaces with the SMT-solver [cvc5](https://cvc5.github.io/) to suggest self-contained proof scripts for the given goal. Notably, although `cvc5` is used to produce the proof script suggestion, the resulting proof does not retain a dependency on `cvc5`.

## Installation

QuerySMT depends on a fork of `cvc5` which has been instrumented to output hints that QuerySMT can use to build its proof scripts. To install this modified version of `cvc5`, run the following:
```sh
git clone https://github.com/HanielB/cvc5.git
cd cvc5
git checkout duper-output
./configure.sh --tracing --auto-download
# If the above step fails, try again after installing m4, e.g. with "sudo apt-get install m4"
cd ./build
make
sudo make install
```

To confirm that you have the correct version of `cvc5` installed, run `cvc5 -h | grep "dump-hints"`. A succesful implementation of the instrumented fork should yield the output: `--dump-hints dump solving hints: instantiations, lemmas, rewrites`.

***Note**: Although QuerySMT currently requires users to install this fork of `cvc5` manually, I am in the process of removing this step to make QuerySMT more easily accessible.*

## Adding QuerySMT to your project

To add QuerySMT for `v4.29.0` to an existing project with a `lakefile.toml` file, add the following dependency:

```toml
[[require]]
name = "QuerySMT"
git = "https://github.com/JOSHCLUNE/QuerySMT.git"
```

The file `lean-toolchain` should contain the following:
```
leanprover/lean4:v4.29.0
```

If you have a project with a `lakefile.lean` instead of a `lakefile.toml` file, you can use this instead:
```lean
require QuerySMT from git "https://github.com/JOSHCLUNE/QuerySMT.git"
```

Then, make sure that your `lean-toolchain` file contains the same version of Lean 4 as QuerySMT and that if your project imports [mathlib](https://github.com/leanprover-community/mathlib4), then it uses the same version of mathlib as QuerySMT. This step is necessary because QuerySMT depends on mathlib, so errors can arise if your project attempts to import a version of mathlib different from the one imported by QuerySMT.

After these steps are taken, the following example should compile without any warnings or errors:
```lean
import QuerySMT

example : True := by querySMT
```