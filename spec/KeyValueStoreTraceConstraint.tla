--------------------------- MODULE KeyValueStoreTraceConstraint ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, MCKVS

\*ASSUME "TRACE_PATH" \in DOMAIN IOEnv
ASSUME TLCGet("config").mode = "bfs"
vars == <<store, tx, snapshotStore, written, missed>>

(* Read trace *)
JsonTrace ==
    IF "TRACE_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.TRACE_PATH)
    ELSE
        Print(<<"Failed to validate the trace. TRACE_PATH environnement variable was expected.">>, "")

TraceNoVal == "null"

TraceKey ==
    ToSet(JsonTrace[1].Key)

TraceVal ==
    ToSet(JsonTrace[1].Val)

TraceTxId ==
    ToSet(JsonTrace[1].TxId)

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
    []   op = "InitWithValue" -> UpdateRec(default, args[1])



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


KV == INSTANCE MCKVS

TraceInit ==
    \* The implementation's initial state is deterministic and known.
    \* TLCGet("level") = 1 => /\ KV!Init
    TRUE


TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
     \* equivalent to the (canonical) Spec formual  Init /\ [][Next]_vars  .  
     \* However, TLC's breadth-first algorithm does not explore successor
     \* states of a *seen* state.  Since one or more states may appear one or 
     \* more times in the the trace, the  UNCHANGED vars  combined with the
     \*  TraceView  that includes  TLCGet("level")  is our workaround. 
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars


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

TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(Trace) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", Trace[d],
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<vars, TLCGet("level")>>

TraceAlias ==
    [
        \* TODO: Funny TLCGet("level")-1 could be removed if the spec has an
        \* TODO: auxiliary counter variable  i  .  Would also take care of 
        \* TODO: the bug that TLCGet("level")-1 is not defined for the initial
        \* TODO: state.
        len |-> Len(Trace),
        log     |-> <<TLCGet("level"), Trace[TLCGet("level")]>>,
        snapshotStore |-> snapshotStore,
        written |-> written,
        enabled |-> [
            OpenTx |-> ENABLED \E t \in TxId : OpenTx(t) /\ MapVariables(Trace[TLCGet("level")]),
            RollbackTx |-> ENABLED \E t \in TxId : RollbackTx(t)  /\ MapVariables(Trace[TLCGet("level")]),
            CloseTx |-> ENABLED \E t \in TxId : CloseTx(t)  /\ MapVariables(Trace[TLCGet("level")]),
            Add |-> ENABLED \E t \in TxId, k \in Key, v \in Val : Add(t,k,v)  /\ MapVariables(Trace[TLCGet("level")]),
            Update |-> ENABLED \E t \in TxId, k \in Key, v \in Val : Update(t,k,v)  /\ MapVariables(Trace[TLCGet("level")]),
            Map |-> ENABLED MapVariables(Trace[TLCGet("level")])
        ]
    ]
-----------------------------------------------------------------------------

=============================================================================