/-
- Files whose names begin with a dot character ('.') typically represent files that should usually be hidden,
  such as source-control metadata and configuration files.
  Modify doug with an option to show or hide filenames that begin with a dot.
  This option should be controlled with a -a command-line option.

- Modify doug so that it takes a starting directory as an additional command-line argument.
-/

module

structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""
  showHidden : Bool := false

def usage : String :=
  "Usage: doug [--ascii] [--display-hidden-files] [--start <path>]
Options:
\t--ascii\tUse ASCII characters to display the directory structure
\t--display-hidden-files\tUse ASCII characters to display the directory structure
\t--start\tStarting directory"


-- I will take care of parsing another day
def configFromArgs : List String → Option Config
  | [] => some {} -- all fields default
  | ["--ascii"] => some {useASCII := true}
  | ["--start a"] => some {currentPrefix := "a"}
  | ["--display-hidden-files"] => some {showHidden := true}
  | _ => none

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    if name.startsWith "." then
      let cfg <- read
      if cfg.showHidden then pure (some (if (← path.isDir) then .dir name else .file name)) else pure none
    else
      pure none

def dirLT (e1 : IO.FS.DirEntry) (e2 : IO.FS.DirEntry) : Bool :=
  e1.fileName < e2.fileName

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

def showFileName (file : String) : ConfigIO Unit := do
  withReader (·.inDirectory) (IO.println file)

def showDirName (dir : String) : ConfigIO Unit := do
  withReader (·.inDirectory) (IO.println dir)

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
    | none => pure ()
    | some (.file name) => showFileName name
    | some (.dir name) =>
      showDirName name
      let contents ← path.readDir
      withReader (·.inDirectory)
        (doList (contents.qsort dirLT).toList fun d =>
          dirTree d.path)

def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      (dirTree (← IO.currentDir)).run config
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {args}\n"
      IO.eprintln usage
      pure 1
