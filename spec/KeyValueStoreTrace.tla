--------------------------- MODULE KeyValueStoreTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils

(* Matches the configuration of the app. *)
CONSTANTS
    Key,
    Val,
    TxId,
    NoVal

JsonTracePath == IF "TRACE_PATH" \in DOMAIN IOEnv THEN IOEnv.TRACE_PATH ELSE "trace_valid_0.ndjson"

(* Read trace *)
JsonTrace ==
    ndJsonDeserialize(JsonTracePath)

(* Replace RM constant *)
RM ==
    JsonTrace[1].RM

(* Get trace skipping config line *)
Trace ==
    SubSeq(JsonTrace, 2, Len(JsonTrace))

(* Generic operators *)
(* Operators to apply when updating variable *)
Replace(var, val) == val   \* 1st argument unnecessary but added for consistency
ExceptAt(var, arg, val) == [var EXCEPT ![arg] = val]
ExceptAt2(var, arg1, arg2, val) == [var EXCEPT ![arg1][arg2] = val]
AddElement(var, val) == var \cup {val}
AddElements(var, vals) == var \cup vals
RemoveElement(var, val) == var \ {val}
Clear(var) == {}

ExceptAtMany(var, args, val) == [arg \in var |-> IF arg \in args THEN var[arg] = val (* TODO Allow other transform*) ELSE var[arg] = var[arg]]




VARIABLES   store,          \* A data store mapping keys to values.
            tx,             \* The set of open snapshot transactions.
            snapshotStore,  \* Snapshots of the store for each transaction.
            written,        \* A log of writes performed within each transaction.
            missed,          \* The set of writes invisible to each transaction.
            i

vars == <<store, tx, snapshotStore, written, missed, i>>

(* Specific operators *)
(* Add key, value to snapshot store of transaction txId *)
SnapshotStoreAdd(txId, k, v) == [snapshotStore EXCEPT ![txId][k] = v]
(* Remove key, value to snapshot store of transaction txId *)
SnapshotStoreRemove(txId, k) == [snapshotStore EXCEPT ![txId][k] = NoVal]

MissedUpdate(txId, vals) ==
    [otherTx \in TxId |-> IF otherTx \in tx' /\ otherTx = txId THEN missed[otherTx] \cup ToSet(vals) ELSE missed[otherTx]]

StoreUpdate(vals) ==
    [k \in Key |-> IF k \in DOMAIN vals THEN vals[k] ELSE store[k]]

LogAdd(var, txId, val) == [var EXCEPT ![txId] = @ \cup {val}]
LogClear(var, txId) == ExceptAt(var, txId, {})
LogAddAll(var, txId, vals) == [var EXCEPT ![txId] = @ \cup ToSet(vals)]

(* TESTOS *)
\*TxUpdate(txId, op) == IF op = "add" THEN tx' \cup txId ELSE tx' \ {txId}
\*StoreUpdate(vals) == [k \in Key |-> IF k \in DOMAIN vals THEN vals[k] ELSE store[k]]


KV == INSTANCE MCKVS

(* Can be generated *)
TraceInit ==
  /\ i = 1
  /\ KV!Init

Apply(var, op, args) ==
   CASE op = "ExceptAt" -> ExceptAt2(var, args[1], args[2], args[3])
   []   op = "AddElement" -> AddElement(var, args[1])
   []   op = "RemoveElement" -> RemoveElement(var, args[1])
   []   op = "Replace" -> Replace(var, args[1])
   []   op = "LogAdd" -> LogAdd(var, args[1], args[2])
   []   op = "LogAddAll" -> LogAddAll(var, args[1], args[2])
   []   op = "LogClear" -> LogClear(var, args[1])
   []   op = "SnapshotStoreAdd" -> SnapshotStoreAdd(args[1], args[2], args[3])
   []   op = "SnapshotStoreRemove" -> SnapshotStoreRemove(args[1], args[2])
   []   op = "MissedUpdate" -> MissedUpdate(args[1], args[2])
   []   op = "StoreUpdate" -> StoreUpdate(args[1])

MapVariables(t) ==
    /\
        IF "store" \in DOMAIN t
        THEN store' = Apply(store, t.store.op, t.store.args)
        ELSE TRUE
    /\
        IF "tx" \in DOMAIN t
        THEN tx' = Apply(tx, t.tx.op, t.tx.args)
        ELSE TRUE
    /\
        IF "snapshotStore" \in DOMAIN t
        THEN snapshotStore' = Apply(snapshotStore, t.snapshotStore.op, t.snapshotStore.args)
        ELSE TRUE
    /\
        IF "written" \in DOMAIN t
        THEN written' = Apply(written, t.written.op, t.written.args)
        ELSE TRUE
    /\
        IF "missed" \in DOMAIN t
        THEN missed' = Apply(missed, t.missed.op, t.missed.args)
        ELSE TRUE

ReadNext ==
    /\ i <= Len(Trace)
    /\ i' = i + 1
    /\ MapVariables(Trace[i])

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
term ==
    /\ i > Len(Trace)
    /\ UNCHANGED vars

TraceNext ==
    \/
        /\ ReadNext
        /\ [KV!Next]_vars
    \/
        (* All trace processed case *)
        /\ term

TraceBehavior == TraceInit /\ [][TraceNext]_vars /\ WF_vars(TraceNext)

Complete == <>[](i = Len(Trace) + 1)

THEOREM TraceBehavior => KV!Spec
THEOREM TraceBehavior => []KV!TypeInvariant
THEOREM TraceBehavior => []KV!TxLifecycle

(* Property to check *)
Spec == KV!Spec
(* Invariant *)
TypeInvariant == KV!TypeInvariant
TxLifecycle == KV!TxLifecycle
-----------------------------------------------------------------------------

=============================================================================