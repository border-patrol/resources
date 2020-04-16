||| An example EDSL to describe multiple file interactions, and a
||| handler for the IO computation context.
|||
module Example.Files

import public Resources

%access public export
%default total

namespace AbstractST
  ||| Files are open for reading or writing.
  public export
  data FMode = R | W

  ||| Abstract state.
  public export
  data FileState = Open FMode | Closed

  public export
  data FH = MkFH

  {- [ NOTE ]

  Type synonym to make writing the language easier.

  -}

  public export
  FHStateType : FH -> Type
  FHStateType _ = FileState

  public export
  FileHandle : Type
  FileHandle = Var FH MkFH

  public export
  FileStateItem : Type
  FileStateItem = StateItem FH FHStateType MkFH

{- [ NOTE ]

Predicates to reason about file handlers.

-}
namespace Predicates
  ||| Reason about a file handle's current abstract state.
  public export
  data IsOpenFor : (hdl  : Var FH MkFH)
                -> (mode : FMode)
                -> (item : FileStateItem)
                -> Type where
    FileIsOpenFor : (m : FMode) -> IsOpenFor hdl m (MkStateItem MkFH hdl (Open m))

  ||| Does the abstract state belong to the given handle.
  public export
  data IsHandle : (hdl : Var FH MkFH)
               -> (item : FileStateItem)
               -> Type where
    FileExists : (hdl : Var FH MkFH) -> IsHandle hdl (MkStateItem MkFH hdl st)

{- [ NOTE ]

Functions to update FileHandle abstract states.

-}
namespace Updates

  public export
  closeHandle : (item : FileStateItem)
             -> (prf  : IsOpenFor hdl m item)
             -> FileStateItem
  closeHandle (MkStateItem MkFH label _) prf = MkStateItem MkFH label Closed

namespace Definition

{- [ NOTE ]

Type level functions to perform state transitions and update the type-level context.

-}

  public export
  openTrans : Either FileError (Var FH MkFH)
           -> FMode
           -> Context FH FHStateType
           -> Context FH FHStateType
  openTrans (Left _)  _  old = old
  openTrans (Right x) fm old = MkStateItem MkFH x (Open fm) :: old

  public export
  readTrans : Either FileError String
           -> (old : Context FH FHStateType)
           -> InContext MkFH (IsOpenFor hdl R) old
           -> Context FH FHStateType
  readTrans (Right _) old _   = old
  readTrans (Left  _) old prf = update old prf (\i,p => closeHandle i p)

  public export
  writeTrans : Maybe FileError
           -> (old : Context FH FHStateType)
           -> (prf : InContext MkFH (IsOpenFor hdl W) old)
           -> Context FH FHStateType
  writeTrans Nothing  old _   = old
  writeTrans (Just _) old prf = update old prf (\i,p => closeHandle i p)

  ||| The language definition for working with multiple file handlers.
  public export
  data Files : Lang FH FHStateType where
      ||| Open the given file in the presented mode.
      Open : (fname : String)
          -> (fm : FMode)
          -> Files (Either FileError (Var FH MkFH))
                   old
                   (\res => openTrans res fm old)

      ||| Read a line from the open (for reading) file handle.
      Read : (hdl : Var FH MkFH)
          -> (prf : InContext MkFH (IsOpenFor hdl R) old)
          -> Files (Either FileError String) old (\res => readTrans res old prf)

      ||| Write the given String to the open (for writing) file handle.
      Write : (hdl : Var FH MkFH)
           -> (msg : String)
           -> (prf : InContext MkFH (IsOpenFor hdl W) old)
           -> Files (Maybe FileError) old (\res => writeTrans res old prf)

      ||| Close the open file handle
      Close : (hdl : Var FH MkFH)
           -> (prf : InContext MkFH (IsHandle hdl) old)
           -> Files () old (const $ drop old prf)

      ||| Print stuff.
      PrintLn : Show a => a -> Files () old (const old)

{- [ NOTE ]

A high-level API to embedd language expressions within `LangM`, and calculate language proofs.

-}
namespace API
  public export
  FILES : LANG FH FHStateType
  FILES = MkLang FH FHStateType Files


  ||| Open the given file in the presented mode.
  public export
  openFile : (fname : String)
          -> (fm : FMode)
          -> LangM m (Either FileError (Var FH MkFH)) FILES old (\res => openTrans res fm old)
  openFile fname fm = expr $ Open fname fm

  ||| Read a line from the open (for reading) file handle.
  public export
  readString : (hdl : Var FH MkFH)
            -> {auto prf : InContext MkFH (IsOpenFor hdl R) old}
            -> LangM m (Either FileError String) FILES old (\res => readTrans res old prf)
  readString hdl {prf} = expr (Read hdl prf)

  ||| Write the given String to the open (for writing) file handle.file handle.
  public export
  writeString : (hdl : Var FH MkFH)
             -> String
             -> {auto prf : InContext MkFH (IsOpenFor hdl W) old}
             -> LangM m (Maybe FileError) FILES old (\res => writeTrans res old prf)
  writeString hdl str {prf} = expr (Write hdl str prf)

  ||| Close the open file handle
  public export
  closeFile : (hdl : Var FH MkFH)
           -> {auto prf : InContext MkFH (IsHandle hdl) old}
           -> LangM m () FILES old (const $ drop old prf)
  closeFile hdl {prf} = expr (Close hdl prf)

  ||| Print showable things on a line.
  public export
  printLn : Show a
         => a
         -> LangM m () FILES old (const old)
  printLn a = expr (PrintLn a)

  ||| Type given to programs to ensure that they are closed.
  |||
  public export
  Files : (m : Type -> Type) -> Type -> Type
  Files m type = LangM m type FILES Nil (const Nil)

{- [ NOTE]

A handler for the `IO` context.

-}
namespace ContextIO

  ||| Files are Files
  public export
  RealVar FH where
    CalcRealType MkFH = File

  ||| How to handle files, in which we map high-level operations to unsafe ones from Idris' prelude.
  public export
  Handler FH FHStateType Files () IO where
    handle env (Open fname fm) acc cont = do
      let m = case fm of {R => Read; W => WriteTruncate}
      res <- openFile fname m
      case res of
        Left err => cont (Left  err)   env             acc
        Right fh => cont (Right MkVar) (MkTag fh::env) acc

    handle env (Read hdl prf) acc cont = do
      let MkTag fh = lookup env prf
      res <- fGetLine fh
      case res of
        Left err  => cont (Left  err) (update env prf (\i,p => closeHandle i p)) acc
        Right str => cont (Right str) env                                        acc

    handle env (Write hdl str prf) acc cont = do
      let MkTag fh = lookup env prf
      res <- fPutStrLn fh str
      case res of
        Left err  => cont (Just err) (update env prf (\i,p => closeHandle i p)) acc
        Right _   => cont Nothing    env                                        acc

    handle env (Close hdl prf) acc cont = do
      let MkTag fh = lookup env prf
      closeFile fh
      cont () (drop env prf) acc

    handle env (PrintLn a) acc cont = do
       printLn a
       cont () env acc

||| A sample program to copy a string from one file to another.
|||
copy : (a,b : String) -> Files m (Maybe FileError)
copy a b = do
  Right fh <- openFile a R | Left err => do {printLn err; pure (Just err)}
  Right str <- readString fh | Left err => do {printLn err; closeFile fh; pure (Just err)}
  closeFile fh
  Right fh1 <- openFile b W | Left err => do {printLn err; pure (Just err)}
  res <- writeString fh1 str
  case res of
    Nothing  => do {closeFile fh1; pure Nothing}
    Just err => do {printLn err; closeFile fh1; pure (Just err)}


-- --------------------------------------------------------------------- [ EOF ]
