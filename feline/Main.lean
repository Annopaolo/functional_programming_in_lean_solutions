def bufsize : USize := 20 * 1024

-- partial allows you to not prove termination
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream


def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def help : IO UInt32 := do
    let stdout <- IO.getStdout
    stdout.putStrLn "you can provide a list of files, or - to read from stdin"
    process 0 []

-- In Lean, main can have one of three types:
-- IO Unit corresponds to programs that cannot read their command-line arguments and always succeed with exit code 0
-- IO UInt32 corresponds to programs without arguments that return exit codes
-- List String → IO UInt32 corresponds to programs that take arguments and return exit codes
def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | ["--help"] => help
  | _ =>  process 0 args
