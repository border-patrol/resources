||| This module contains an adaptation of the session description language as presented in:
|||
|||     <https://dblp.uni-trier.de/rec/html/journals/corr/abs-1904-01288>
|||
||| This implementation differs from the original in that recursive
||| calls and calling of subprograms are achieved using standard idris
||| constructs. To support his natively in resources, one will need to
||| introduce new primitives. As described in the `Resources` paper,
||| however, this requires that now means to reason about the
||| interaction between the type-level state of the caller and callee
||| programs. It would not be correct to assume anything about said
||| interaction with the framework in its current form.
|||
||| Furthermore, as described in the `Resources` paper, there is no
||| handler program to provide projection capabilities.
module Example.Sessions

import Data.List

import Resources

%access public export
%default total

{- [ Actors]

Here we define actors/roles in a session description, ensuring that we have a means to compare them.

-}
data Actor = MkActor String

Eq Actor where
 (==) (MkActor a) (MkActor b) = a == b

actorNotEqual : ((x = y) -> Void) -> (MkActor x = MkActor y) -> Void
actorNotEqual f Refl = f Refl

actorDecEq : (x,y : Actor) -> Dec (x = y)
actorDecEq (MkActor x) (MkActor y) with (decEq x y)
  actorDecEq (MkActor y) (MkActor y) | (Yes Refl) = Yes Refl
  actorDecEq (MkActor x) (MkActor y) | (No contra) = No (actorNotEqual contra)

DecEq Actor where
  decEq = actorDecEq

Ord Actor where
  compare (MkActor a) (MkActor b) = compare a b

-- Here we describe our type-level states.
namespace TypeLevel

  ||| Channels are born free until they are bound.
  data Usage = Free | Bound

  ||| Variables in Sessions are either paired actors, or data types.
  data Ty = CHAN (Actor, Actor) | DATA Type

  namespace State

    ||| A channel's state is it's usage.
    record ChanState where
      constructor MkChanState
      usage : Usage

    ||| A data types state is the type of message and who has seen the message.
    record DataState where
      constructor MkDataState
      knownBy : List Actor
      type    : Type

    ||| A mapping between variable types and their abstract state.
    CalcStateType : Ty -> Type
    CalcStateType (CHAN _) = ChanState
    CalcStateType (DATA _) = DataState


namespace Predicates

  ||| A predicate to state that all the listed actors are aware of the data item.
  |||
  ||| @actors The actors who know about the item.
  ||| @var    The item the actors know about.
  ||| @item   The abstract state associated with the item.
  data AllKnow : (actors : List Actor)
              -> (var   : Var Ty (DATA type))
              -> (item  : StateItem Ty CalcStateType (DATA type))
              -> Type
     where
       NilKnows : (prf : Elem x actors)
               -> AllKnow [x] msg (MkStateItem (DATA type) msg (MkDataState actors type))
       ConsKnows : (prf : Elem x actors)
                -> (later : AllKnow xs msg (MkStateItem (DATA type) msg (MkDataState actors type)))
                -> AllKnow (x::xs) msg (MkStateItem (DATA type) msg (MkDataState actors type))

  ||| A predicate to state that the given actor knows about the provided data item.
  |||
  ||| @actor The actor who knows about the item.
  ||| @var   The item the actors know about.
  ||| @item  The abstract state associated with the item.
  data KnowsData : (actor : Actor)
                -> (var   : Var Ty (DATA type))
                -> (item  : StateItem Ty CalcStateType (DATA type))
                -> Type
    where
      DoesKnow : (prf : x = y)
              -> (prfE : Elem x actors)
              -> KnowsData y var (MkStateItem (DATA type) var (MkDataState actors type))

  ||| A type-level function to record that a particular message has been used by an actor.
  ExpandWhoKnows : (newActor : Actor)
                -> (oldState : StateItem Ty CalcStateType (DATA type))
                -> (prfState : KnowsData sender label oldState)
                -> StateItem Ty CalcStateType (DATA type)
  ExpandWhoKnows newActor (MkStateItem (DATA type) label (MkDataState actors type)) (DoesKnow Refl prfE) =
    MkStateItem (DATA type) label (MkDataState (newActor::actors) type)

  ||| Proof that the given sender and receiver are valid participants in the protocol.
  data AllowedToConnect : (sender, receiver : Actor)
                       -> (actors : List Actor)
                       -> Type where
    CanConnect : (prfSender   : Elem sender   actors)
              -> (prfReceiver : Elem receiver actors)
              -> AllowedToConnect sender receiver actors

  ||| An assertion that the given channel has the given state.
  data ChannelHasState : (assumedState : Usage)
                      -> (chan         : Var Ty (CHAN (s,r)))
                      -> (actual       : StateItem Ty CalcStateType (CHAN (s,r)))
                      -> Type
    where
      YesChanHasState : ChannelHasState state chan (MkStateItem (CHAN (s,r)) chan (MkChanState state))

  ||| A type-level function to set a channel's state.
  SetChannelState : (newState : Usage)
                 -> (oldState : StateItem Ty CalcStateType (CHAN (s,r)))
                 -> (prfState : ChannelHasState oldState' var oldState)
                 -> StateItem Ty CalcStateType (CHAN (s,r))
  SetChannelState newState (MkStateItem (CHAN (s,r)) var (MkChanState oldState')) YesChanHasState = MkStateItem (CHAN (s,r)) var (MkChanState newState)

  ||| A predicate to describe valid end states for data and connections.
  data EndState : (ty : Ty) -> StateItem Ty CalcStateType ty -> Type where
    ||| We do not care.
    EndData : EndState (DATA type)  state
    ||| Connections must be free.
    EndConn : EndState (CHAN (s,r)) (MkStateItem (CHAN (s,r)) lbl (MkChanState Free))


||| Our algebraic definition of a Session description language.
data Sessions : (participants : List Actor) -> Lang Ty CalcStateType where

  ||| Describe that the given actor `a` creates a message of type `type`.
  |||
  ||| We also need proof that the actor is allowed to participate in the description.
  NewData : (a    : Actor)
         -> (type : Type)
         -> (prf  : Elem a ps)
         -> Sessions ps (Var Ty (DATA type)) old (\lbl => MkStateItem (DATA type) lbl (MkDataState [a] type) :: old)

  ||| Describe that the given actor `a` creates a message that depends on an earlier message that `a` has seen.
  |||
  ||| The resulting message type will be a dependent pair.
  NewDataDep : (a        : Actor)
            -> (dep      : Var Ty (DATA type))
            -> (prfKnows : InContext (DATA type) (KnowsData a dep) old)
            -> (msgType  : (msg : type) -> Type)
            -> Sessions ps (Var Ty (DATA (x ** msgType x)))
                            old
                            (\lbl => MkStateItem (DATA (x ** msgType x))
                                                 lbl
                                                 (MkDataState [a] (x ** msgType x)) :: old)

  ||| Specify a new connection between two valid participants in the session.
  NewConnection : (a,b : Actor)
               -> (prf : AllowedToConnect a b ps)
               -> Sessions ps (Var Ty (CHAN (a,b))) old (\lbl => MkStateItem (CHAN (a,b)) lbl (MkChanState Bound) :: old)

  ||| Close an existing connection.
  EndConnection : (chan : Var Ty (CHAN (a,b)))
               -> (prf  : InContext (CHAN (a,b)) (ChannelHasState Bound chan) old)
               -> Sessions ps () old (const $ update old prf (SetChannelState Free))

  ||| Send a message that the channel sender knows about (either created or received) to the receiver on the given active channel.
  SendLeft : (chan : Var Ty (CHAN (s,r)))
          -> (msg  : Var Ty (DATA type))
          -> (prfActive : InContext (CHAN (s,r))  (ChannelHasState Bound chan) old)
          -> (prfKnows  : InContext (DATA type) (KnowsData s msg) old)
          -> Sessions ps () old (const $ update old prfKnows (ExpandWhoKnows r))

  ||| Send a message that the receiver on the channel knows about (either created or received) to the sending end on the given active channel.
  SendRight : (chan : Var Ty (CHAN (s,r)))
           -> (msg  : Var Ty (DATA type))
           -> (prfActive : InContext (CHAN (s,r))  (ChannelHasState Bound chan) old)
           -> (prfKnows  : InContext (DATA type) (KnowsData r msg) old)
           -> Sessions ps () old (const $ update old prfKnows (ExpandWhoKnows s))

  ||| If all actors in the session have seen the data then we can access the message's value and depend on it.
  ReadMsg : (msg : Var Ty (DATA type))
         -> (prf : InContext (DATA type) (AllKnow ps msg) old)
         -> Sessions ps type old (const old)

  ||| End the session description if all the variables are in the correct end state.
  |||
  ||| This is our check that all channels have been closed.
  StopSession : AllContext EndState old -> Sessions ps () old (const Nil)

{- [ NOTE ]

Here we define the language and high-level friendly API.

-}
||| Define the `SESSIONS` language.
SESSIONS : (ps : List Actor) -> LANG Ty CalcStateType
SESSIONS ps = MkLang Ty CalcStateType (Sessions ps)

||| Define a closed session.
Session : (m : Type -> Type) -> List Actor -> Type
Session m ps = LangM m () (SESSIONS ps) Nil (const Nil)

||| Describe that the given actor `a` creates a message of type `type`.
|||
||| We also need proof that the actor is allowed to participate in the description.
msg : (creator : Actor)
   -> (type : Type)
   -> {auto prf : Elem creator actors}
   -> LangM m (Var Ty (DATA type)) (SESSIONS actors) old (\lbl => MkStateItem (DATA type) lbl (MkDataState ([creator]) type) :: old)
msg creator type {prf} = Expr $ NewData creator type prf

||| Describe that the given actor `a` creates a message that depends on an earlier message that `a` has seen.
|||
||| The resulting message type will be a dependent pair.
msgDep : (creator  : Actor)
      -> (dep      : Var Ty (DATA type))
      -> {auto prfKnows : InContext (DATA type) (KnowsData creator dep) old}
      -> (msgType  : (msg : type) -> Type)
      -> LangM m
               (Var Ty (DATA (x ** msgType x)))
               (SESSIONS actors)
               old
               (\lbl => MkStateItem (DATA (x ** msgType x))
                                    lbl
                                    (MkDataState [creator] (x ** msgType x)) :: old)
msgDep creator dep {prfKnows} msgType = Expr (NewDataDep creator dep prfKnows msgType)

||| If all actors in the session have seen the data then we can access the message's value and depend on it.
read : (msg : Var Ty (DATA type))
    -> {auto prf : InContext (DATA type) (AllKnow actors msg) old}
    -> LangM m type (SESSIONS actors) old (const old)
read msg {prf} = Expr $ ReadMsg msg prf

||| End the session description if all the variables are in the correct end state.
|||
||| This is our check that all channels have been closed.
end : {auto prf : AllContext EndState old} -> LangM m () (SESSIONS actors) old (const Nil)
end {prf} = Expr $ StopSession prf

||| Specify a new connection between two valid participants in the session.
setup : (a, b : Actor)
     -> {auto prf : AllowedToConnect a b actors}
     -> LangM m (Var Ty (CHAN (a,b))) (SESSIONS actors) old (\lbl => MkStateItem (CHAN (a,b)) lbl (MkChanState Bound) :: old)
setup sender receiver {prf} = Expr $ NewConnection sender receiver prf

||| Close an existing connection.
destroy : (chan : Var Ty (CHAN (a,b)))
       -> {auto prf  : InContext (CHAN (a,b)) (ChannelHasState Bound chan) old}
       -> LangM m () (SESSIONS actors) old (const $ update old prf (SetChannelState Free))
destroy chan {prf} = Expr $ EndConnection chan prf

||| Send a message that the channel sender knows about (either created or received) to the receiver on the given active channel.
sendLeft : (chan : Var Ty (CHAN (s,r)))
        -> (msg  : Var Ty (DATA type))
        -> {auto prfActive : InContext (CHAN (s,r))  (ChannelHasState Bound chan) old}
        -> {auto prfKnows  : InContext (DATA type) (KnowsData s msg) old}
        -> LangM m () (SESSIONS actors) old (const $ update old prfKnows (ExpandWhoKnows r))
sendLeft chan msg {prfActive} {prfKnows} = Expr (SendLeft chan msg prfActive prfKnows)

||| Send a message that the receiver on the channel knows about (either created or received) to the sending end on the given active channel.
sendRight : (chan : Var Ty (CHAN (s,r)))
         -> (msg  : Var Ty (DATA type))
         -> {auto prfActive : InContext (CHAN (s,r))  (ChannelHasState Bound chan) old}
         -> {auto prfKnows  : InContext (DATA type) (KnowsData r msg) old}
         -> LangM m () (SESSIONS actors) old (const $ update old prfKnows (ExpandWhoKnows s))
sendRight chan msg {prfActive} {prfKnows} = Expr (SendRight chan msg prfActive prfKnows)

{- [ NOTE ]

Let's define some actors.

-}

Alice : Actor
Alice = MkActor "A"

Bob : Actor
Bob = MkActor "B"

Charlie : Actor
Charlie = MkActor "C"

{- [ NOTE ]

Here we define a value dependent version of the well known TCP Handshake.

Dependent pairs are used to ensure that the sequence numbers sent are the ones previously seen.

There are better ways to encode this, see the PLACES paper linked in the module's documentation.

-}

data Packet

TCPHandshake : Session m [Alice, Bob]
TCPHandshake = do
  chan <- setup Alice Bob

  m1 <- msg Alice (Packet, Nat)
  sendLeft chan m1

  (p,x) <- read m1
  m2 <- msg Bob (Packet, (x' ** x' = x), Nat)

  sendRight chan m2

  (p,xplus,y) <- read m2

  m3 <- msg Alice (Packet, (x' ** x' = x), (y' ** y' = y))
  sendLeft chan m3
  destroy chan
  end


{- [ NOTE ]

Here we define a PingPong protocol. In which Alice sends a Ping to Bob who responds with a Pong, and proof that they send a pong, and calls the session description again. If alice sent a Pong then the session ends.

This is *a* encoding, there are probably better ways to encode this.

-}
data PingPong = Ping | Pong

pingNotPong : (Ping = Pong) -> Void
pingNotPong Refl impossible

DecEq PingPong where
  decEq Ping Ping = Yes Refl
  decEq Pong Pong = Yes Refl
  decEq Ping Pong = No pingNotPong
  decEq Pong Ping = No (negEqSym pingNotPong)

RfcPingPong : Session m [Alice, Bob]
RfcPingPong = do chan <- setup Alice Bob
                 val <- msg Alice PingPong
                 sendLeft chan val
                 res <- read val
                 case res of
                   Pong => do destroy chan
                              end
                   Ping => do val' <- msg Bob (x : PingPong ** x = Pong)
                              sendRight chan val'
                              destroy chan
                              end
                              assert_total $ RfcPingPong

{- [ NOTE ]

Here we define a simple varient of the Echo protocol that uses an optional type to act as a quit message in the Empty case.

-}
Echo : Session m [Alice, Bob]
Echo {m} = do chan <- setup Alice Bob
              val <- msg Alice (Maybe String)
              sendLeft chan val
              res <- read val
              case res of
                Nothing => do destroy chan
                              end
                Just _  => do sendRight chan val
                              destroy chan
                              end
                              assert_total $ Echo {m=m}

{- [ NOTE ]

Here we define a simple Higher-Order-Protocol that emulates an authentication step using a Boolean.

-}

hoppy : Session m [Alice, Bob]
     -> Session m [Alice, Bob]
hoppy p = do chan <- setup Alice Bob
             val <- msg Alice String
             sendLeft chan val
             resp <- msg Bob Bool
             sendRight chan resp
             res <- read resp
             case res of
               False => do destroy chan
                           end
               True => do destroy chan
                          end
                          p

-- --------------------------------------------------------------------- [ EOF ]
