||| An example Resource Dependent EDSL (based upon Robin Milner's BiGraphs) to specify the physical and behavioural connections for mobile devices.
|||
||| This EDSL encapsulates the following concepts:
|||
||| 1. Messages, an atomic entity of arity zero.
||| 2. Devices, a complex entity (nesting) that contains many messages, and
||| artiy one. Devices have at most one connection to another device.
||| 3. Rooms, a complex entity (merge) of arity zero that contains many devices.
||| 4. Buildings, a complex entity (merge) of arity zero that contains many
||| rooms
||| 5. Regions, a complex entity (parallel) of arity zero that situates buildings in different regions.
|||
||| We define a handler to construct EDSL instances into a pure BiGraph form based upon an algebraic graph representation.
module Examples.BiGraph

import Data.Vect
import Resources

%default total
%access public export

{- [ NOTE ] The types for our Wireless EDSL -}

||| Device Types
data DTy = MOBILE | LAPTOP

||| Node types.
data Ty = ROOM | BUILDING | DEVICE DTy | MESSAGE

||| Mobile devices can support upto two connections, laptops ten.
maxConn : DTy -> Nat
maxConn MOBILE = 2
maxConn LAPTOP = 10

||| An abstract resource to capture device states.
|||
||| As the device is used the number of free connections will decrease until zero.
|||
||| @dtype The devce type.
data StateD : (dtype : DTy) -> Type where
  ||| Capture connection status and max number of connections.
  MkD : (connected : Bool) -> (curr : Nat) -> StateD ty

||| Default status of unconnected and a calculated number of connections.
defState : (type : DTy) -> StateD type
defState type = MkD False (maxConn type)

||| Map node types to an abstract resource.
|||
||| 1. Rooms, and messages, contain placement status.
||| 2. Buildings have no associated abstract state.
||| 3. Devices have type `StateD`
|||
CalcStateType : Ty -> Type
CalcStateType ROOM = Bool
CalcStateType BUILDING = ()
CalcStateType (DEVICE ty) = StateD ty
CalcStateType MESSAGE = Bool

||| A predicate to capture if a node has been unassigned.
|||
||| @value The type of node.
||| @lbl the node's bound name.
||| @item the nodes abstract state.
data Unassigned : (value : Ty)
               -> (lbl : Var Ty value)
               -> (item : StateItem Ty CalcStateType value)
               -> Type where
                     -- Type       | Label | Abstract State
  URoom    : Unassigned ROOM         rm      (MkStateItem ROOM         rm  False)
  UDevice  : Unassigned (DEVICE ty)  dev     (MkStateItem (DEVICE ty)  dev (MkD False c))
  UMessage : Unassigned MESSAGE      msg     (MkStateItem MESSAGE      msg False)


||| Function to update a node's abstract state to indicate node usage.
|||
||| @item the nodes abstract state.
||| @prf  that the node has not been assigned.
Use : (item : StateItem Ty CalcStateType value)
   -> (prf  : Unassigned value lbl item)
   -> StateItem Ty CalcStateType value
Use {value = ROOM} (MkStateItem ROOM lbl False) URoom = MkStateItem ROOM lbl True
Use {value = DEVICE ty} (MkStateItem (DEVICE ty) lbl (MkD False curr)) UDevice = MkStateItem (DEVICE ty) lbl (MkD True curr)
Use {value = MESSAGE} (MkStateItem MESSAGE lbl False) UMessage = MkStateItem MESSAGE lbl True

||| A predicate to capture that a node can be assigned to.
|||
||| @thisValue The type of node.
||| @thisVar the node's bound name.
||| @item the nodes abstract state.
data CanAssign : (thisValue : Ty)
              -> (thisVar   : Var Ty valueThis)
              -> (item  : StateItem Ty CalcStateType valueThis)
              -> Type where
                        -- Type      | Label | Abstract State
   ToABuilding : CanAssign BUILDING    bld     (MkStateItem BUILDING bld ())
   ToARoom     : CanAssign ROOM        rm      (MkStateItem ROOM     rm  True)
   ToADevice   : CanAssign (DEVICE ty) dev     (MkStateItem (DEVICE ty)   dev (MkD True (S n)))

||| A predicate to capture valid nesting of nodes.
data ValidAssign : Ty -> Ty -> Type where
  IsValidAssignBR : ValidAssign BUILDING    ROOM
  IsValidAssignRD : ValidAssign ROOM        (DEVICE ty)
  IsValidAssignDM : ValidAssign (DEVICE ty) MESSAGE

||| A type level function to update the abstract state of a node to indicate it's assignment.
|||
||| @var  the node's label
||| @prfV proof that it is a valid assignment.
||| @item the nodes abstract state.
||| @prf  that the node can be assigned.
Assign : (var  : Var Ty x)
      -> (prfV : ValidAssign value x)
      -> (item : StateItem Ty CalcStateType value)
      -> (prf  : CanAssign value lbl item)
      -> StateItem Ty CalcStateType value
Assign {value = BUILDING} var prfV (MkStateItem BUILDING lbl ()) ToABuilding =
  MkStateItem BUILDING lbl ()
Assign {value = ROOM} var prfV (MkStateItem ROOM lbl True) ToARoom = MkStateItem ROOM lbl True
Assign {value = (DEVICE ty)} var prfV (MkStateItem (DEVICE ty) lbl (MkD True (S n))) ToADevice =
  MkStateItem (DEVICE ty) lbl (MkD True n)

||| A predicate to capture that a device has sufficient space to handle more connections
data CanConnect : (to   : Var Ty (DEVICE type))
               -> (item : StateItem Ty CalcStateType (DEVICE type))
               -> Type where
  HasSpace : CanConnect dev (MkStateItem (DEVICE type) lbl (MkD True (S n)))

||| A type-level function to update the abstract state of a device.
|||
||| This decreases the number of free connections.
|||
||| @item the nodes abstract state.
||| @prf  that the node can be assigned.
Connect : (item : StateItem Ty CalcStateType (DEVICE type))
       -> (prf  : CanConnect to item)
       -> StateItem Ty CalcStateType (DEVICE type)
Connect (MkStateItem (DEVICE type) lbl (MkD True (S n))) HasSpace =
    MkStateItem (DEVICE type) lbl (MkD True n)

{- [ Language Definition ] -}

data Wireless : Lang Ty CalcStateType where
  ||| Create a new building.
  NewBuilding : Wireless (Var Ty BUILDING) old (\lbl => MkStateItem BUILDING lbl () :: old)

  ||| Create a new room.
  NewRoom : Wireless (Var Ty ROOM) old (\lbl => MkStateItem ROOM lbl False :: old)

  ||| Create a new device.
  NewDevice : (type : DTy)
           -> Wireless (Var Ty (DEVICE type)) old (\lbl => MkStateItem (DEVICE type) lbl (defState type) :: old)

  ||| Create a new message.
  NewMessage  : Wireless (Var Ty MESSAGE) old (\lbl => MkStateItem MESSAGE lbl False :: old)

  ||| Insert `varX` into `varY`
  |||
  ||| @varX The child node.
  ||| @varY The parent node.
  ||| @prfValid that it is a valid assignment.
  ||| @prfFree that one can insert into `varX`.
  ||| @prfInsert that one can assign `varY`
  Insert : (varX : Var Ty x)
        -> (varY : Var Ty y)
        -> (prfValid : ValidAssign y x)
        -> (prfFree : InContext x (Unassigned x varX) old)
        -> (prfInsert : InContext y (CanAssign y varY) (update old prfFree Use))
        -> Wireless () old (const $ update (update old prfFree Use) prfInsert (Assign varX prfValid))

  ||| Connect `varX` to `varY`
  |||
  ||| @varX The sending node.
  ||| @varY The receiving node.
  ||| @prfSpaceX that `varX` can be linked.
  ||| @prfSpaceY that `varY` can be linked.
  Link : (varX : Var Ty (DEVICE typeX))
      -> (varY : Var Ty (DEVICE typeY))
      -> (prfSpaceX : InContext (DEVICE typeX) (CanConnect varX) old)
      -> (prfSpaceY : InContext (DEVICE typeY) (CanConnect varY) (update old prfSpaceX Connect))
      -> Wireless () old (const $ update (update old prfSpaceX Connect) prfSpaceY Connect)

  ||| End the specification.
  End : Wireless () old (const Nil)

{- [ NOTE ]

A high-level API to embedd language expressions within `LangM`, and calculate language proofs.

-}

||| An resource dependent EDSL to describe communication networks and state.
WIRELESS : LANG Ty CalcStateType
WIRELESS = MkLang Ty CalcStateType Wireless

||| Create a new building.
newBuilding : LangM m (Var Ty BUILDING) WIRELESS old (\lbl => MkStateItem BUILDING lbl () :: old)
newBuilding = Expr $ NewBuilding

||| Create a new room.
newRoom : LangM m (Var Ty ROOM) WIRELESS old (\lbl => MkStateItem ROOM lbl False :: old)
newRoom = Expr $ NewRoom

||| Create a new device.
|||
||| @type The devices type.
newDevice : (type : DTy)
         -> LangM m (Var Ty (DEVICE type))
                    WIRELESS
                    old
                    (\lbl => MkStateItem (DEVICE type) lbl (defState type) :: old)
newDevice ty = Expr $ NewDevice ty

||| Create a new message
newMessage : LangM m (Var Ty MESSAGE)
                     WIRELESS
                     old
                     (\lbl => MkStateItem MESSAGE lbl False :: old)
newMessage = Expr $ NewMessage

||| Insert `varX` into `varY`.
insert : (varX : Var Ty x)
      -> (varY : Var Ty y)
      -> {auto prfValid : ValidAssign y x}
      -> {auto prfFree : InContext x (Unassigned x varX) old}
      -> {auto prfInsert : InContext y (CanAssign y varY) (update old prfFree Use)}
      -> LangM m () WIRELESS old (const $ update (update old prfFree Use) prfInsert (Assign varX prfValid))
insert x y {prfValid} {prfFree} {prfInsert} = Expr (Insert x y prfValid prfFree prfInsert)

||| Link two devices together.
link : (varX : Var Ty (DEVICE typeX))
    -> (varY : Var Ty (DEVICE typeY))
    -> {auto prfSpaceXY : InContext (DEVICE typeX) (CanConnect varX) old}
    -> {auto prfSpaceYX : InContext (DEVICE typeY) (CanConnect varY) (update old prfSpaceXY Connect)}
    -> LangM m () WIRELESS old (const $ update (update old prfSpaceXY Connect) prfSpaceYX Connect)
link x y {prfSpaceXY} {prfSpaceYX} = Expr (Link x y prfSpaceXY prfSpaceYX)

||| End a specification.
end : LangM m () WIRELESS old (const Nil)
end = Expr End

||| Type given to programs to ensure that they are closed.
|||
WirelessDesc : (m : Type -> Type) -> Type
WirelessDesc m = LangM m () WIRELESS Nil (const Nil)

{- [ NOTE]

Here we given an example before giving the evaluation context.

-}

|||
example : WirelessDesc m
example = do
  buildingA <- newBuilding
  buildingB <- newBuilding

  roomA <- newRoom
  roomB <- newRoom
  roomC <- newRoom

  laptopA <- newDevice LAPTOP
  laptopB <- newDevice LAPTOP
  laptopC <- newDevice LAPTOP
  mobile  <- newDevice MOBILE

  msg <- newMessage

  insert roomA buildingA
  insert laptopA roomA
  insert mobile  roomA
  insert msg mobile

  insert roomB buildingA
  insert laptopB roomB

  insert roomC buildingB
  insert laptopC roomC

  link laptopA laptopC
  link mobile laptopB
  end

{- [ Evaluation context ]
-}

||| An entity has an arity, an identifier, and is typed according to the EDSLs variable type.
data Entity : (type : Type) -> (value : type) -> Type where
  MkEntity : (n : Nat) -> (arity : Nat) -> Entity type value

namespace Algebra

 ||| An algebraic graph view of a Bigraph.
 |||
 ||| The shape of a bigraph follows its algebraic definition.
 ||| The type is indexed by the entity's concrete type.
 data BiGraph : Type -> Type where
   Identity : BiGraph a

   Node : Entity a value -> BiGraph a
   Outside : String -> BiGraph a

   Nesting : (BiGraph a) -> (BiGraph a) -> BiGraph a
   Merge   : (BiGraph a) -> (BiGraph a) -> BiGraph a
   Par     : (BiGraph a) -> (BiGraph a) -> BiGraph a
   Connect : (BiGraph a) -> (BiGraph a) -> BiGraph a
   Overlay : (BiGraph a) -> (BiGraph a) -> BiGraph a

||| We map the EDSL's variable types to concrete entity specifications.
public export
RealVar Ty where
  CalcRealType ROOM       = Entity Ty ROOM
  CalcRealType BUILDING   = Entity Ty BUILDING
  CalcRealType (DEVICE x) = Entity Ty (DEVICE x)
  CalcRealType MESSAGE    = Entity Ty MESSAGE

||| A handler to construct `BiGraph` instances from `WIRELESS` specifications.
|||
||| We run the evaluation in a pure context to enable bigraph construction.
|||
||| **Note** The accumulator in this instance is a counter to generate node identifiers, and the resulting bigraph itself.
public export
Handler Ty CalcStateType Wireless (Nat, BiGraph Ty) (Basics.id) where
  handle env NewBuilding      (ctr,g) cont = cont MkVar (MkTag (MkEntity ctr Z)::env)              (S ctr,g)
  handle env NewRoom          (ctr,g) cont = cont MkVar (MkTag (MkEntity ctr Z)::env)              (S ctr,g)
  handle env (NewDevice type) (ctr,g) cont = cont MkVar (MkTag (MkEntity ctr (maxConn type))::env) (S ctr,g)
  handle env NewMessage       (ctr,g) cont = cont MkVar (MkTag (MkEntity ctr Z)::env)              (S ctr,g)

  handle env (Insert varX varY prfValid prfFree prfInsert) (ctr,g) cont with (prfValid)
    handle env (Insert varX varY prfValid prfFree prfInsert) (ctr,g) cont | IsValidAssignBR = do
        let MkTag rm  = lookup env prfFree
        let env' = (update env prfFree Use)
        let MkTag bld = lookup env' prfInsert
        let env'' = update env' prfInsert (Assign varX IsValidAssignBR)
        cont () env'' (ctr, Overlay (Nesting (Node bld) (Node rm)) g)
    handle env (Insert varX varY prfValid prfFree prfInsert) (ctr,g) cont | IsValidAssignRD = do
        let MkTag dev  = lookup env prfFree
        let env' = (update env prfFree Use)
        let MkTag rm = lookup env' prfInsert
        let env'' = update env' prfInsert (Assign varX IsValidAssignRD)
        cont () env'' (ctr, Overlay (Nesting (Node rm) (Node dev)) g)
    handle env (Insert varX varY prfValid prfFree prfInsert) (ctr,g) cont | IsValidAssignDM = do
        let MkTag msg  = lookup env prfFree
        let env' = (update env prfFree Use)
        let MkTag dev = lookup env' prfInsert
        let env'' = update env' prfInsert (Assign varX IsValidAssignDM)
        cont () env'' (ctr, Overlay (Nesting (Node dev) (Node msg)) g)

  handle env (Link varX varY prfSpaceX prfSpaceY) (ctr,g) cont = do
    let MkTag x = lookup env prfSpaceX
    let env' = update env prfSpaceX Connect
    let MkTag y = lookup env' prfSpaceY
    let env'' = update env' prfSpaceY Connect
    cont () env'' (ctr, Overlay (Connect (Node x) (Node y)) g)

  handle env End (ctr,g) cont = cont () Nil (ctr,g)

-- --------------------------------------------------------------------- [ EOF ]
