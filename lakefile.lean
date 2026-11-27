/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
The library catalogue in submission/lake-catalogue.toml is checked against this configuration. -/
module
public import Lake
@[expose] public section
open Lake DSL Lean System
package completion_theory where
  version := v!"0.1.0"
  extraDepTargets := #[`nativeRuntime]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

target nativeRuntime pkg : Lake.Dynlib := do
  let runtimeDir := pkg.buildDir / "cyclic-native"
  let pythonExe := if System.Platform.isWindows then "python" else "python3"
  let output ← IO.Process.output {
    cmd := pythonExe
    args := #["scripts/bootstrap_native_mathlib.py", "--project-root", pkg.dir.toString,
      "--output-dir", runtimeDir.toString]
    cwd := some pkg.dir
    env := #[("LEAN_NUM_THREADS", some "1")]
  }
  if output.exitCode != 0 then
    error s!"Native runtime bootstrap failed ({output.exitCode}):\n{output.stdout}\n{output.stderr}"
  Lake.logInfo output.stdout
  let text ← IO.FS.readFile (runtimeDir / "result.json")
  let data ← IO.ofExcept (Json.parse text)
  let loader ← IO.ofExcept (data.getObjVal? "loader")
  let file ← IO.ofExcept (loader.getObjValAs? String "file")
  return Job.pure {name := "CyclicNativeLoader",path := FilePath.mk file,plugin := true}

@[default_target]
lean_lib CompletionTheory where

lean_lib Challenge where

@[default_target]
lean_lib Solution where
  plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]

lean_lib PhaseGeometry where

lean_lib HadamardMultibase where

lean_lib AlgorithmChallenge where

@[default_target]
lean_lib AlgorithmSolution where

lean_lib CompletionRepair where
  moreLeanArgs := #["-M1024"]

lean_lib RepairChallenge where

@[default_target]
lean_lib RepairSolution where

lean_lib CompletionCodeTrap where
  moreLeanArgs := #["-M1024"]

lean_lib CodeChallenge where

@[default_target]
lean_lib CodeSolution where

lean_lib CompletionLattice where
  moreLeanArgs := #["-M1024"]

lean_lib LatticeChallenge where
  moreLeanArgs := #["-M1024"]

@[default_target]
lean_lib LatticeSolution where
  moreLeanArgs := #["-M1024"]

lean_lib CompletionCharacter where
  moreLeanArgs := #["-M1024"]

lean_lib CharacterChallenge where
  moreLeanArgs := #["-M1024"]

@[default_target]
lean_lib CharacterSolution where
  moreLeanArgs := #["-M1024"]

lean_lib CompletionBloch where
  moreLeanArgs := #["-M1024"]

lean_lib BlochChallenge where
  moreLeanArgs := #["-M1024"]

@[default_target]
lean_lib BlochSolution where
  moreLeanArgs := #["-M1024"]

lean_lib CompletionQuaternary where
  moreLeanArgs := #["-M1024"]

lean_lib QuaternaryChallenge where
  moreLeanArgs := #["-M1024"]

@[default_target]
lean_lib QuaternarySolution where
  moreLeanArgs := #["-M1024"]

lean_lib CompletionCyclicExistence where
  moreLeanArgs := #["-M1024"]
  plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]

lean_lib CyclicExistenceChallenge where
  moreLeanArgs := #["-M1024"]
  plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]

@[default_target]
lean_lib CyclicExistenceSolution where
  moreLeanArgs := #["-M1024"]
  plugins := #[{key := .packageTarget .anonymous `nativeRuntime}]

