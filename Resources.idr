||| Resources is framework for creating Resource Dependent EDSLs as described in the 2020 ECOOP paper:
||| *A Framework for Resource Dependent EDSLs in a Dependently Typed Language*.
|||
||| > Idris’ Effects library demonstrates how to embed resource dependent algebraic effect handlers into a
||| > dependently-typed host language, providing run-time and compile-time based reasoning on type-level resources.
||| > Building upon this work, Resources is a framework for realising Embedded Domain Specific Languages (EDSLs) with
||| > type-systems that contain domain specific substructural properties. Differing from Effects, Resources allows a
||| > language’s substructural properties to be encoded in a resource that is associated with language variables. Such
||| > an association allows for multiple effect instances to be reasoned about autonomically and without explicit
||| > type-level declaration. Type-level predicates are used as proof that the language’s substructural properties
||| > hold. Several exemplar EDSLs are presented that illustrates our framework’s operation and how dependent types
||| > provide correctness-by-construction guarantees that substructural properties of written programs hold.
|||
||| This module defines the Framework's core.
|||
module Resources

%default total
%access public export

namespace TypeLevel

  ||| Language variables are typed.
  |||
  ||| @Ty the type universe in which the variable exists.
  ||| @ty the variable's actual type.
  public export
  data Var : (Ty : Type) -> (ty : Ty) -> Type where
    MkVar : Var type value

  ||| Each variable has an associated abstract state.
  |||
  ||| @type the type universe in which the variable exists.
  ||| @calcStateType a function to compute the state's value from the provided type.
  ||| @value the variables type from which the abstract state's type is calculated.
  public export
  data StateItem : (type : Type)
                -> (calcStateType : type -> Type)
                -> (value : type)
                -> Type
    where
       MkStateItem : (value : type)
                  -> (label : Var type value)
                  -> (state : calcStateType value)
                  -> StateItem type calcStateType value

  ||| The context in which EDSL variables are bound and associated
  ||| with an abstract state.
  |||
  ||| The context is a simple cons-like data structure whose internal
  ||| values are are typed sith a common value.  We cannot utilise
  ||| Idris' `List` type as we need to collect at the type-level the
  ||| variable's type.  In future this should be replaced with `DList`
  ||| from idris-containers but that is future engineering.
  |||
  ||| @type the type universe in which the variable exists.
  ||| @calcStateType a function to compute the state's value from the provided type.
  public export
  data Context : (type : Type)
              -> (calcStateType : type -> Type)
              -> Type
    where
      Nil  : Context type calcStateType
      (::) : (item : StateItem type calcStateType value)
          -> (rest : Context type calcStateType)
          -> Context type calcStateType

  ||| A function to construct the type signature common to all
  ||| /Resource Dependent EDSLs/ as specified in the framework.
  |||
  ||| The signature describes a Hoare like monad that describes the
  ||| shift from an existing `pre` context to a new context based on
  ||| the expression's type.
  |||
  ||| @type the type universe in which the variable exists.
  ||| @calcStateType a function to compute the state's value from the provided type.
  public export
  Lang : (type : Type) -> (calcStateType : (val : type) -> Type) -> Type
  Lang type calcStateType =  (exprTy : Type)
                          -> (pre    : Context type calcStateType)
                          -> (postK  : exprTy -> Context type calcStateType)
                          -> Type

  ||| A simple algebraic data type to represent a /Resource Dependent EDSL/ instance.
  |||
  ||| @type the type universe in which the variable exists.
  ||| @calcStateType a function to compute the state's value from the provided type.
  public export
  data LANG : (type : Type) -> (calcStateType : type -> Type) -> Type where
      MkLang : (type : Type)
            -> (calcStateType : type -> Type)
            -> (lang : Lang type calcStateType)
            -> LANG type calcStateType

  ||| A type-level function calculate the next set of states based on a runtime value.
  |||
  ||| @value The runtime value used for calculation.
  ||| @postK The function that calculates the new state using `value`.
  public export
  updateState : (value : t)
             -> (postK : t -> Context type calcStateType)
             -> Context type calcStateType
  updateState value postK = postK value

  ||| A data structure that captures, generically, the sequencing of resource dependent EDSL language expressions.
  |||
  ||| @m the computation context in which this EDSL is defined.
  ||| @x the type associated with a language expression.
  ||| @calcStateType a function to compute the state's value from the provided type.
  ||| @spec The specific EDSL that is to be embedded.
  ||| @pre  The initial state that the expression knows about.
  ||| @post The final state the expression will be in that is dependent on the runtime value associated with the expression.
  public export
  data LangM : (m : Type -> Type)
            -> (x : Type)
            -> (spec : LANG type calcStateType)
            -> (pre  : Context type calcStateType)
            -> (post : x -> Context type calcStateType)
            -> Type
    where
      ||| Returns a value.
      Value : (value : a)
           -> {postK : a -> Context type calcStateType}
           -> LangM m a spec (postK value) postK

      ||| Provides sequencing of expressions and insertion of computed values into subsequent expressions.
      |||
      ||| @this The computation to run first.
      ||| @beInThis The next computation to run that uses the result of `this`.
      Let : (this : LangM m a spec old oldK)
         -> (beInThis : (val : a) -> LangM m b spec (oldK val) newK)
         -> LangM m b spec old newK

      ||| How to embedd an EDSL language expression into the framework.
      |||
      ||| @t The type of the expression.
      ||| @type the type universe in which the variable exists.
      ||| @calcStateType a function to compute the state's value from the provided type.
      ||| @pre  The initial state that the expression knows about.
      ||| @postK The final state the expression will be in that is dependent on the runtime value associated with the expression.
      ||| @eSig The function to compute the expressions type signature.
      ||| @expr The expression to embedd.
      Expr : {t,type : Type}
          -> {calcStateType : type -> Type}
          -> {pre   : Context type calcStateType}
          -> {postK : t -> Context type calcStateType}
          -> {eSig  : Lang type calcStateType}
          -> (expr : eSig t pre postK)
          -> LangM m t (MkLang type calcStateType eSig) pre (\v => updateState v postK)

  -- A high-level API to make embedding and use of the framework easier for users and designers.
  namespace API
    public export
    pure : (value : a) -> {postK : a -> Context type calcStateType} -> LangM m a spec (postK value) postK
    pure = Value

    public export
    (>>=) : LangM m a spec old oldK
       -> ((val : a) -> LangM m b spec (oldK val) postK)
       -> LangM m b spec old postK
    (>>=) = Let

    public export
    expr : {t,type : Type}
        -> {calcStateType : type -> Type}
        -> {pre   : Context type calcStateType}
        -> {postK : t -> Context type calcStateType}
        -> {eSig  : Lang type calcStateType}
        -> (expr : eSig t pre postK)
        -> LangM m t (MkLang type calcStateType eSig) pre (\v => updateState v postK)
    expr e = Expr e

namespace All
  ||| Ensure that a predicate applies to all items in the given context.
  |||
  ||| @p The predicate to apply to each item.
  ||| @c The context to apply the predicate to.
  public export
  data AllContext : (p : (value : type)
                      -> (item  : StateItem type calcStateType value)
                      -> Type)
                 -> (c : Context type calcStateType)
                 -> Type
    where
      Nil  : AllContext p Nil
      (::) : {p : (v : type) -> StateItem type calcStateType v -> Type}
          -> {value : type}
          -> {item  : StateItem type calcStateType value}
          -> {items : Context type calcStateType}
          -> (prf   : p value item)
          -> (rest  : AllContext p items)
          -> AllContext p (item :: items)

namespace Element

  ||| Existential quantification that there exists an item in the
  ||| context that the given predicate is satisifed.
  |||
  ||| @value The type of variable that the predicate is applied to.
  ||| @p The predicate to apply to each item.
  ||| @c The context to apply the predicate to.
  public export
  data InContext : (value : type)
                -> (p : StateItem type calcStateType value -> Type)
                -> (c : Context type calcStateType)
                -> Type
    where
      H : {p : StateItem type calcStateType value -> Type}
       -> (bewijs : p x)
       -> InContext value p (x :: rest)

      E : {p : StateItem type calcStateType value -> Type}
       -> (komt : InContext value p rest)
       -> InContext value p (not_x :: rest)

  Uninhabited (InContext value p Nil) where
    uninhabited (H _) impossible
    uninhabited (E _) impossible

  ||| Updates the element (at the provided index) in the provided context.
  |||
  ||| @context The context in which to apply the update.
  ||| @index The position of the item to be updated.
  ||| @f The update function to apply. The proof is included incase it contains
  |||    any interesting information for the update.
  public export
  update : (context : Context type calcStateType)
        -> (index   : InContext value predicate context)
        -> (f : (item   : StateItem type calcStateType value)
             -> (bewijs : predicate item)
             -> StateItem type calcStateType value)
        -> Context type calcStateType
  update (item :: rest)     (H bewijs) f = f item bewijs :: rest
  update (not_item :: rest) (E komt)   f = not_item :: update rest komt f

  ||| Remove the element (at the provided index) in the provided context.
  |||
  ||| @predicate The predicate that was applied to the item to be dropped.
  ||| @context The context in which the item is to be dropped.
  ||| @index The position of the item to drop.
  public export
  drop : {predicate : StateItem type calcStateType value -> Type}
      -> (context   : Context type calcStateType)
      -> (index     : InContext value predicate context)
      -> Context type calcStateType
  drop (item :: rest) (H bewijs) = rest
  drop (not_x :: rest) (E komt) = not_x :: drop rest komt

  ||| A helper function to replace the state in an element in our context.
  public export
  doUpdate : {predicate : StateItem type calcStateType value -> Type}
          -> (item     : StateItem type calcStateType value)
          -> (newState : calcStateType value)
          -> (bewijs   : predicate item)
          -> StateItem type calcStateType value
  doUpdate (MkStateItem value label state) newState bewijs = (MkStateItem value label newState)


  ||| An application of `update` to set the state for an item at the specified index.
  |||
  ||| @predicate The predicate that was applied to the item.
  ||| @context The context in which to apply the update.
  ||| @index The position of the item to be updated.
  ||| @item' The new state.
  public export
  setState : {predicate : StateItem type calcStateType value -> Type}
          -> (context   : Context type calcStateType)
          -> (index     : InContext value predicate context)
          -> (item'     : calcStateType value)
          -> Context type calcStateType
  setState context index item' = update context index (\i => doUpdate i item')

  ||| Proof that the given variable has the associated state.
  data HasVar : (lbl  : Var type value)
             -> (item : StateItem type calcStateType value)
             -> Type where
    DoesHaveVar : HasVar lbl (MkStateItem value lbl state)

-- -------------------------------------------------------------- [ Evaluation ]

namespace Env

  ||| Captures how EDSL variables are translated into concrete types.
  public export
  interface RealVar (type : Type) where
    CalcRealType : type -> Type

  ||| A container for holding concrete variable representations.
  public export
  data Tag : (type : Type) -> (value : type)
          -> Type
    where
      MkTag : RealVar type
           => (real : CalcRealType value)
           -> Tag type value

  ||| An evaluation environments to keep track of our language's real
  ||| variables and their abstract state, respective to the language's
  ||| typing context.
  public export
  data Env : (m : Type -> Type)
          -> (type    : Type)
          -> {calcStateType : type -> Type}
          -> (ctxt    : Context type calcStateType)
          -> Type
    where
      Nil  : Env m type Nil
      (::) : RealVar type
          => {item : StateItem type calcStateTy value}
          -> (tag  : Tag type value)
          -> (rest : Env m type items)
          -> Env m type (item::items)

  ||| Extracting a variable from the environment at the given index.
  |||
  ||| @env The environment being accessed.
  ||| @idx The position of the variable value to be extracted.
  public export
  lookup : RealVar type
        => (env : Env m type context)
        -> {p   : (item : StateItem type calcSTy value) -> Type}
        -> (idx : InContext value p context)
        -> Tag type value
  lookup (tag :: rest) (H bewijs) = tag
  lookup (tag :: rest) (E komt) = lookup rest komt


  ||| Update the type level state in the environment.
  |||
  ||| @env The environment being accessed.
  ||| @idx The position of the variable value to be updated
  ||| @up  The update function to be applied.
  public export
  update : RealVar type
        => (env  : Env m type ctxt)
        -> (idx  : InContext value p ctxt)
        -> (up   : (i : StateItem type calcSTy value)
                -> p i
                -> StateItem type calcSTy value)
        -> Env m type (update ctxt idx up)
  update (tag :: rest) (H bewijs) up = tag :: rest
  update (tag :: rest) (E komt) up = tag :: update rest komt up

  ||| Drop the state at the given index.
  |||
  ||| @env The environment being accessed.
  ||| @idx The position of the variable value to be dropped.
  public export
  drop : (env : Env m type ctxt)
      -> (idx : InContext value p ctxt)
      -> Env m type (drop ctxt idx)
  drop (tag :: rest) (H bewijs) = rest
  drop (tag :: rest) (E komt) = tag :: drop rest komt


namespace Building

  ||| The handler interface that describes how to evaluate languages in a presented computation context.
  |||
  ||| @type the type universe in which the variable exists.
  ||| @calcStateType a function to compute the state's value from the provided type.
  ||| @eSig The function to compute the expressions type signature.
  ||| @tyBRes The type associated with the accumulator if we are to build something.
  ||| @m The computation context in which to evaluate the language.
  public export
  interface RealVar type
         => Handler (type : Type)
                    (calcStateType : type -> Type)
                    (eSig   : Lang type calcStateType)
                    (tyBRes : Type)
                    (m      : Type -> Type) | type
    where
      ||| How to handle language expressions in the given computation context `m`.
      |||
      ||| @env the current evaluation context.
      ||| @expr the expression to be handled.
      ||| @acc an accumulator to be used if building something.
      ||| @cont a continuation to make things total.
      handle : (env  : Env m type pre)
            -> (expr : eSig tyExpr pre postK)
            -> (acc  : tyBRes)
            -> (cont : (value : tyExpr)
                    -> (env'  : Env m type (postK value))
                    -> (acc'  : tyBRes)
                    -> m tyRes)
            -> m tyRes

  ||| An internal helper function to evaluate an embedded language expression.
  |||
  ||| You will not need to call this at all.
  public export
  execBuild : RealVar type
           => Handler type calcStateType eSig tyBRes m
           => (env  : Env m type pre)
           -> (expr : eSig tyExpr pre postK)
           -> (acc  : tyBRes)
           -> (cont : (value : tyExpr)
                   -> (env'  : Env m type (updateState value postK))
                   -> (acc'  : tyBRes)
                   -> m tyRes)
           -> m tyRes
  execBuild env expr acc cont = handle env expr acc cont

  ||| An internal helper function to evaluate a `LangM` instance, and sequencing of expressions.
  |||
  ||| You will not need to call this at all.
  public export
  rawEval : RealVar type
         => Handler type calcStateType eSig tyBRes m
         => (env  : Env m type pre)
         -> (expr : LangM m tyExpr (MkLang type calcStateType eSig) pre postK)
         -> (acc  : tyBRes)
         -> (cont : (value : tyExpr)
                 -> (env'  : Env m type (postK value))
                 -> (acc'  : tyBRes)
                 -> m tyRes)
         -> m tyRes
  rawEval env (Value value {postK}) acc cont = cont value env acc
  rawEval env (Let this beIn) acc cont =
    rawEval env this acc (\this', env', acc' =>
                             rawEval env' (beIn this') acc' cont)
  rawEval env (Expr expr) acc cont = execBuild env expr acc cont

  ||| A helper data structure to container evaluation results.
  public export
  record Result (tyExpr : Type) (tyBRes : Type) where
    constructor MkResult
    computed : tyExpr
    built    : tyBRes

  ||| Evaluate the given closed program in the given applicative computation context `m`.
  |||
  ||| @init the initial value for our accumulator.
  ||| @expr the program to evaluate.
  public export
  run : Applicative m
     => RealVar type
     => Handler type calcStateType eSig tyBRes m
     => (init : tyBRes)
     -> (expr : LangM m tyExpr (MkLang type calcStateType eSig) Nil (const Nil))
     -> m (Result tyExpr tyBRes)
  run init expr = rawEval Nil expr init (\val, env', acc' => pure $ MkResult val acc')

  ||| Evaluate the given closed program in the identity computation context.
  |||
  ||| @init the initial value for our accumulator.
  ||| @expr the program to evaluate.
  public export
  runPure : RealVar type
        => Handler type calcStateType eSig tyBRes Basics.id
        => (init : tyBRes)
        -> (expr : LangM Basics.id tyExpr (MkLang type calcStateType eSig) Nil (const Nil))
        -> (Result tyExpr tyBRes)
  runPure init expr = rawEval Nil expr init (\val, env', acc' => MkResult val acc')

-- --------------------------------------------------------------------- [ EOF ]
