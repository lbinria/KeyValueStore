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
    ndJsonDeserializeOption(JsonTracePath, TRUE)

(* Replace RM constant *)
RM ==
    JsonTrace[1].RM

(* Get trace skipping config line *)
Trace ==
    SubSeq(JsonTrace, 2, Len(JsonTrace))

(* Generic operators *)
(* Operators to apply when updating variable *)
Replace(var, val) == val   \* 1st argument unnecessary but added for consistency
ReplaceAsSet(var, val) == ToSet(val)
ExceptAt(var, arg, val) == [var EXCEPT ![arg] = val]
ExceptAt2(var, arg1, arg2, val) == [var EXCEPT ![arg1][arg2] = val]
AddElement(var, val) == var \cup {val}
AddElements(var, vals) == var \cup vals
RemoveElement(var, val) == var \ {val}
Clear(var) == {}

ExceptAtMany(var, args, val) == [arg \in var |-> IF arg \in args THEN var[arg] = val (* TODO Allow other transform*) ELSE var[arg] = var[arg]]

UpdateRemoveMissingSet(var, val, default) ==
    [key \in DOMAIN var |-> IF key \in DOMAIN val THEN ToSet(val[key]) ELSE var[key]]

UpdateRemoveMissing(var, val, default) ==
    [key \in DOMAIN var |-> IF key \in DOMAIN val THEN val[key] ELSE var[key]]

UpdateRemoveMissing2(var, val, default) ==
    [key1 \in DOMAIN var |->
        IF key1 \in DOMAIN val THEN
            [key2 \in DOMAIN var[key1] |-> IF key2 \in DOMAIN val[key1] THEN val[key1][key2] ELSE var[key1][key2]]
        ELSE
            var[key1]
\*            [key2 \in DOMAIN var[key1] |-> default]
    ]


VARIABLES   store,          \* A data store mapping keys to values.
            tx,             \* The set of open snapshot transactions.
            snapshotStore,  \* Snapshots of the store for each transaction.
            written,        \* A log of writes performed within each transaction.
            missed,          \* The set of writes invisible to each transaction.
            i

vars == <<store, tx, snapshotStore, written, missed, i>>


KV == INSTANCE MCKVS

(* Can be generated *)
TraceInit ==
  /\ i = 1
  /\ KV!Init

Apply(var, op, args) ==
   CASE op = "ExceptAt" -> ExceptAt2(var, args[1], args[2], args[3])
   []   op = "AddElement" -> AddElement(var, args[1])
   []   op = "RemoveElement" -> RemoveElement(var, args[1])
   []   op = "Replace" -> Replace(var, args)
   []   op = "ReplaceAsSet" -> ReplaceAsSet(var, args)
   []   op = "UpdateRemoveMissingSet" -> UpdateRemoveMissingSet(var, args, "null")
   []   op = "UpdateRemoveMissing" -> UpdateRemoveMissing(var, args, "null")
   []   op = "UpdateRemoveMissing2" -> UpdateRemoveMissing2(var, args, "null")

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