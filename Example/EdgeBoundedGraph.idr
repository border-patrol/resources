||| Here we present an example not found in the paper.
|||
||| We define an *Edge Bounded Graph* as a graph whose nodes are bounded on the number of edges they can contain.
||| Here we differentiate between bounds for roots, leaf, and other nodes.
|||
||| We define a handler to generate a simple adjacency graph representation from our graph language description.
module Examples.EdgeBoundedGraph

import Data.List

import Resources

%access public export
%default total

namespace TypeLevel

  ||| The different node types.
  data Ty = LEAF | ROOT | NODE

  namespace State
    ||| Leaf nodes can accept a certain number of connections.
    record LeafState where
      constructor MkLeafState
      max_incoming : Nat
      incoming : Nat

    ||| Root nodes can make a certain number of connections.
    record RootState where
      constructor MkRootState
      max_outgoing : Nat
      outgoing : Nat

    ||| Nodes that can make, and accept, a certain number of connections.
    record NodeState where
      constructor MkNodeState
      max_incoming : Nat
      max_outgoing : Nat
      incoming : Nat
      outgoing : Nat

    ||| Map variable types to concrete abstract states.
    CalcStateType : Ty -> Type
    CalcStateType LEAF = LeafState
    CalcStateType ROOT = RootState
    CalcStateType NODE = NodeState

namespace Predicates
    data DIRECTION = O | I

    ||| Can a node be connected.
    data CanConnect : DIRECTION
                   -> Var Ty ty
                   -> StateItem Ty CalcStateType ty
                   -> Type
      where
        CanNodeIn  : CanConnect I lbl (MkStateItem NODE lbl (MkNodeState a b (S n) x))
        CanNodeOut : CanConnect O lbl (MkStateItem NODE lbl (MkNodeState a b x     (S n)))
        CanRootOut : CanConnect O lbl (MkStateItem ROOT lbl (MkRootState a (S n)))
        CanLeafIn  : CanConnect I lbl (MkStateItem LEAF lbl (MkLeafState a (S n)))

    ||| Has the node be used completely.
    data Used : StateItem Ty CalcStateType ty -> Type where
       IsNodeUsed : Used (MkStateItem NODE lbl (MkNodeState a b Z Z))
       IsRootUsed : Used (MkStateItem ROOT lbl (MkRootState a Z))
       IsLeafUsed : Used (MkStateItem LEAF lbl (MkLeafState a Z))

    ||| Has the node been used partially.
    data UsedS : StateItem Ty CalcStateType ty -> Type where
      -- All used.
      AllUsedL : UsedS (MkStateItem LEAF lbl (MkLeafState a Z))
      AllUsedR : UsedS (MkStateItem ROOT lbl (MkRootState a Z))
      AllUsedN : UsedS (MkStateItem NODE lbl (MkNodeState a b Z Z))

      -- All incoming ports are used.
      IUsedNode : UsedS (MkStateItem NODE lbl (MkNodeState a b Z x))
      IUsedLeaf : UsedS (MkStateItem LEAF lbl (MkLeafState a Z))

      -- All outgoing ports are used.
      OUsedNode : UsedS (MkStateItem NODE lbl (MkNodeState a b x Z))
      OUsedRoot : UsedS (MkStateItem ROOT lbl (MkRootState a Z))

      ||| Some ports
      SomeNodes : LTE x a
               -> LTE y b
               -> UsedS (MkStateItem NODE lbl (MkNodeState a b x y))

      SomeRoot : LTE x a
              -> UsedS (MkStateItem ROOT lbl (MkRootState a x))

      SomeLeaf : LTE x a
              -> UsedS (MkStateItem LEAF lbl (MkLeafState a x))

namespace Update

  ||| The type-level function to update a node's usage count.
  Use : (d      : DIRECTION)
     -> (item   : StateItem Ty CalcStateType ty)
     -> (bewijs : CanConnect d lbl item)
     -> StateItem Ty CalcStateType ty
  Use I (MkStateItem NODE lbl (MkNodeState a b (S n) x)) CanNodeIn {ty = NODE} =
    MkStateItem NODE lbl (MkNodeState a b n x)
  Use O (MkStateItem NODE lbl (MkNodeState a b x (S n))) CanNodeOut {ty = NODE} =
    MkStateItem NODE lbl (MkNodeState a b x n)
  Use O (MkStateItem ROOT lbl (MkRootState a (S n))) CanRootOut {ty = ROOT} =
    MkStateItem ROOT lbl (MkRootState a n)
  Use I (MkStateItem LEAF lbl (MkLeafState a (S n))) CanLeafIn {ty = LEAF} =
    MkStateItem LEAF lbl (MkLeafState a n)

namespace Declaration

{- [ Language Definition ] -}

    data GraphLang : Lang Ty CalcStateType where
      ||| Create a node that can accept `i` connections, and make `o` connections.
      Node : (i,o : Nat) -> GraphLang (Var Ty NODE) old (\lbl => MkStateItem NODE lbl (MkNodeState i o i o) :: old)
      ||| Create a new root node that can make `o` connections.
      Root : (o   : Nat) -> GraphLang (Var Ty ROOT) old (\lbl => MkStateItem ROOT lbl (MkRootState o o)     :: old)
      ||| Create a new leaf node that can accept `i` connections.
      Leaf : (i   : Nat) -> GraphLang (Var Ty LEAF) old (\lbl => MkStateItem LEAF lbl (MkLeafState i i)     :: old)

      ||| Connect two nodes together if they each have space to allow an edge.
      Stop : GraphLang () old (const Nil)

      ||| Connect two nodes together if they each have space to allow an edge.
      Connect : (a : Var Ty tyO)
             -> (b : Var Ty tyI)

             -> (prfO : InContext tyO (CanConnect O a) old)
             -> (prfI : InContext tyI (CanConnect I b) (update old prfO (Use O)))
             -> GraphLang () old (const $ update (update old prfO (Use O)) prfI (Use I))

{- [ NOTE ]

A high-level API to embedd language expressions within `LangM`, and calculate language proofs.


-}
    ||| The definition of an edge bounded graph.
    MYGRAPH : LANG Ty CalcStateType
    MYGRAPH = MkLang Ty CalcStateType GraphLang

    ||| Create a node that can accept `i` connections, and make `o` connections.
    node : (i,o : Nat)
        -> LangM m (Var Ty NODE) MYGRAPH old (\lbl => (MkStateItem NODE lbl (MkNodeState i o i o)) :: old)
    node i o = Expr $ Node i o

    ||| Create a new root node that can make `o` connections.
    root : (o   : Nat)
        -> LangM m (Var Ty ROOT) MYGRAPH old (\lbl => MkStateItem ROOT lbl (MkRootState o o)     :: old)
    root o = Expr $ Root o

    ||| Create a new leaf node that can accept `i` connections.
    leaf : (i   : Nat)
        -> LangM m (Var Ty LEAF) MYGRAPH old (\lbl => MkStateItem LEAF lbl (MkLeafState i i)     :: old)
    leaf i = Expr $ Leaf i

    ||| Declare the end of tthe specification.
    stop : LangM m () MYGRAPH old (const Nil)
    stop = Expr Stop

    ||| Connect two nodes together if they each have space to allow an edge.
    connect : (a : Var Ty tyO)
           -> (b : Var Ty tyI)

           -> {auto prfO : InContext tyO (CanConnect O a) old}
           -> {auto prfI : InContext tyI (CanConnect I b) (update old prfO (Use O))}
           -> LangM m () MYGRAPH old (const $ update (update old prfO (Use O)) prfI (Use I))
    connect a b {prfO} {prfI} = Expr $ Connect a b prfO prfI

    ||| A simple graph representation.
    record Graph where
      constructor MkGraph
      nodes : List Nat
      edges : List (Nat, Nat)

||| Nodes are *just* Natural numbers
RealVar Ty where
  CalcRealType _ = Nat

||| A pure evaluation context to generate the graph instance.
|||
||| **note** the accumulator is one that contains the node counter,
||| and the graph being constructed.
Handler Ty CalcStateType GraphLang (Nat, Graph) Basics.id where
  handle env Stop (c,g) cont = cont () Nil (c,g)
  handle env (Node i o) (c,g) cont =
    cont MkVar (MkTag c::env) (S c, record {nodes $= (c::)} g)
  handle env (Root o) (c,g) cont =
    cont MkVar (MkTag c::env) (S c, record {nodes $= (c::)} g)
  handle env (Leaf i) (c,g) cont =
    cont MkVar (MkTag c::env) (S c, record {nodes $= (c::)} g)
  handle env (Connect a b prfO prfI) (c,g) cont =
    let (MkTag l) = lookup env prfO in
    let env' = update env prfO (Use O) in
    let (MkTag r) = lookup env' prfI in
    let env'' = update env' prfI (Use I) in
      cont () env'' (c,record {edges $= ((l,r)::)} g)

||| An example program that is closed.
example : LangM m () MYGRAPH Nil (const Nil)
example = do
  a <- node 2 5
  b <- root 1
  c <- root 3

  d <- root 5
  connect c a
  connect b a
  stop

-- --------------------------------------------------------------------- [ EOF ]
