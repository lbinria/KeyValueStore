--------------------------- MODULE KeyValueStoreTraceConstraint ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, MCKVS

ASSUME "TRACE_PATH" \in DOMAIN IOEnv
ASSUME TLCGet("config").mode = "bfs"

(* Read trace *)
JsonTrace ==
    IF "TRACE_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.TRACE_PATH)
    ELSE
        Print(<<"Failed to validate the trace. TRACE_PATH environnement variable was expected.">>, "")

TraceNoVal == "null"

TraceKey ==
    ToSet(JsonTrace[1].__config.Key)

TraceVal ==
    ToSet(JsonTrace[1].__config.Val)

TraceTxId ==
    ToSet(JsonTrace[1].__config.TxId)

(* Get trace skipping config line *)
Trace ==
    SubSeq(JsonTrace, 2, Len(JsonTrace))

(* Generic operators *)
Replace(cur, val) == val
AddElement(cur, val) == cur \cup {val}
AddElements(cur, vals) == cur \cup vals
RemoveElement(cur, val) == cur \ {val}
Clear(cur, val) == {}
\*RemoveKey(cur, val) == NoVal
RemoveKey(cur, val) == [k \in DOMAIN cur |-> IF k = val THEN NoVal ELSE cur[k]]
UpdateRec(cur, val) == [k \in DOMAIN cur |-> IF k \in DOMAIN val THEN val[k] ELSE cur[k]]

(* Can be extracted from init *)
Default(varName) ==
    CASE varName = "store" -> [k \in Key |-> NoVal]
    []  varName = "tx" -> {}
    []  varName = "snapshotStore" -> [t \in TxId |-> [k \in Key |-> NoVal]]
    []  varName = "written" -> [t \in TxId |-> {}]
    []  varName = "missed" -> [t \in TxId |-> {}]

Apply(var, default, op, args) ==
    CASE op = "Replace" -> Replace(var, args[1])
    []   op = "AddElement" -> AddElement(var, args[1])
    []   op = "AddElements" -> AddElements(var, args[1])
    []   op = "RemoveElement" -> RemoveElement(var, args[1])
    []   op = "Clear" -> Clear(var, <<>>)
    []   op = "RemoveKey" -> RemoveKey(var, args[1])
    []   op = "UpdateRec" -> UpdateRec(var, args[1])
    []   op = "Init" -> Replace(var, default)



RECURSIVE ExceptAtPath(_,_,_,_,_)
LOCAL ExceptAtPath(var, default, path, op, args) ==
    LET h == Head(path) IN
    IF Len(path) > 1 THEN
        [var EXCEPT ![h] = ExceptAtPath(var[h], default[h], Tail(path), op, args)]
    ELSE
        [var EXCEPT ![h] = Apply(@, default[h], op, args)]

RECURSIVE ExceptAtPaths(_,_,_)
LOCAL ExceptAtPaths(var, varName, updates) ==
    LET update == Head(updates) IN

    LET applied ==
        IF Len(update.path) > 0 THEN
            ExceptAtPath(var, Default(varName), update.path, update.op, update.args)
        ELSE
            Apply(var, Default(varName), update.op, update.args)
    IN
    IF Len(updates) > 1 THEN
        ExceptAtPaths(applied, varName, Tail(updates))
    ELSE
        applied

\*VARIABLES   store,          \* A data store mapping keys to values.
\*            tx,             \* The set of open snapshot transactions.
\*            snapshotStore,  \* Snapshots of the store for each transaction.
\*            written,        \* A log of writes performed within each transaction.
\*            missed          \* The set of writes invisible to each transaction.
\*            i

\*vars == <<store, tx, snapshotStore, written, missed(*, i*)>>


KV == INSTANCE MCKVS

(* Can be generated *)
\*TraceInit ==
\*  /\ i = 1
\*  /\ KV!Init

TraceInitConstraint ==
    \* The implementation's initial state is deterministic and known.
    TLCGet("level") = 1 => /\ KV!Init



MapVariables(t) ==
    /\
        IF "store" \in DOMAIN t
        THEN store' = ExceptAtPaths(store, "store", t.store)
        ELSE TRUE
    /\
        IF "tx" \in DOMAIN t
        THEN tx' = ExceptAtPaths(tx, "tx", t.tx)
        ELSE TRUE
    /\
        IF "snapshotStore" \in DOMAIN t
        THEN snapshotStore' = ExceptAtPaths(snapshotStore, "snapshotStore", t.snapshotStore)
        ELSE TRUE
    /\
        IF "written" \in DOMAIN t
        THEN written' = ExceptAtPaths(written, "written", t.written)
        ELSE TRUE
    /\
        IF "missed" \in DOMAIN t
        THEN missed' = ExceptAtPaths(missed, "missed", t.missed)
        ELSE TRUE

TraceNextConstraint ==
    LET i == TLCGet("level")
    IN
       /\ i <= Len(Trace)
        /\ MapVariables(Trace[i])

\*ReadNext ==
\*    /\ i <= Len(Trace)
\*    /\ i' = i + 1
\*    /\ MapVariables(Trace[i])

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", Trace[d],
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

-----------------------------------------------------------------------------

(* Infinite stuttering... *)
\*term ==
\*    /\ i > Len(Trace)
\*    /\ UNCHANGED vars

\*TraceNext ==
\*    \/
\*        /\ ReadNext
\*        /\ [KV!Next]_vars
\*    \/
\*        (* All trace processed case *)
\*        /\ term

\*TraceBehavior == TraceInit /\ [][TraceNext]_vars /\ WF_vars(TraceNext)

\*Complete == <>[](i = Len(Trace) + 1)

\*THEOREM TraceBehavior => KV!Spec
\*THEOREM TraceBehavior => []KV!TypeInvariant
\*THEOREM TraceBehavior => []KV!TxLifecycle

(* Property to check *)
\*Spec == KV!Spec
(* Invariant *)
\*TypeInvariant == KV!TypeInvariant
\*TxLifecycle == KV!TxLifecycle
-----------------------------------------------------------------------------

=============================================================================